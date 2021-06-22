/*-
 * SPDX-License-Identifier: BSD-2-Clause-FreeBSD
 *
 * Copyright (c) 2019 Tobias Kortkamp <tobik@FreeBSD.org>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include "config.h"

#include <sys/param.h>
#include <ctype.h>
#if HAVE_ERR
# include <err.h>
#endif
#include <regex.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <libias/array.h>
#include <libias/mempool.h>
#include <libias/str.h>

#include "parser.h"
#include "parser/edits.h"
#include "rules.h"
#include "token.h"
#include "variable.h"

static ssize_t
extract_git_describe_suffix(const char *ver)
{
	if (strlen(ver) == 0) {
		return -1;
	}

	int gflag = 0;
	for (size_t i = strlen(ver) - 1; i != 0; i--) {
		switch (ver[i]) {
		case 'a':
		case 'b':
		case 'c':
		case 'd':
		case 'e':
		case 'f':
			break;
		case 'g':
			gflag = 1;
			break;
		case '-':
			if (gflag) {
				return i;
			} else {
				return -1;
			}
		default:
			if (!isdigit(ver[i])) {
				return -1;
			}
		}
	}

	return -1;
}

static ssize_t
extract_git_describe_prefix(const char *ver)
{
	if (*ver == 0 || isdigit(*ver)) {
		return -1;
	}

	for (size_t i = 0; i < strlen(ver); i++) {
		if (i > 0 && isdigit(ver[i])) {
			return i - 1;
		}
	}

	return -1;
}

static int
is_git_describe_version(struct Mempool *pool, const char *ver, char **distversion, char **prefix, char **suffix)
{
	ssize_t suffix_index;
	if ((suffix_index = extract_git_describe_suffix(ver)) == -1) {
		if (distversion != NULL) {
			*distversion = NULL;
		}
		if (prefix != NULL) {
			*prefix = NULL;
		}
		if (suffix != NULL) {
			*suffix = NULL;
		}
		return 0;
	}

	ssize_t prefix_index;
	if ((prefix_index = extract_git_describe_prefix(ver)) != -1) {
		if (prefix != NULL) {
			*prefix = str_ndup(pool, ver, prefix_index + 1);
		}

	} else {
		if (prefix != NULL) {
			*prefix = NULL;
		}
	}

	if (suffix != NULL) {
		*suffix = str_dup(pool, ver + suffix_index);
	}

	if (distversion != NULL) {
		*distversion = str_slice(pool, ver, prefix_index + 1, suffix_index);
	}

	return 1;
}

PARSER_EDIT(edit_set_version)
{
	SCOPE_MEMPOOL(pool);

	const struct ParserEdit *params = userdata;
	if (params == NULL ||
	    params->subparser != NULL ||
	    params->arg1 == NULL ||
	    params->merge_behavior != PARSER_MERGE_DEFAULT) {
		parser_set_error(parser, PARSER_ERROR_INVALID_ARGUMENT, "missing version");
		return NULL;
	}

	const char *newversion = str_dup(pool, params->arg1);

	const char *ver = "DISTVERSION";
	if (parser_lookup_variable(parser, "PORTVERSION", PARSER_LOOKUP_FIRST, pool, NULL, NULL)) {
		ver = "PORTVERSION";
	}

	char *version;
	int rev = 0;
	int rev_opt = 0;
	if (parser_lookup_variable_str(parser, ver, PARSER_LOOKUP_FIRST, pool, &version, NULL)) {
		char *revision;
		struct Variable *rev_var;
		if (strcmp(version, newversion) != 0 &&
		    (rev_var = parser_lookup_variable_str(parser, "PORTREVISION", PARSER_LOOKUP_FIRST, pool, &revision, NULL))) {
			rev_opt = variable_modifier(rev_var) == MODIFIER_OPTIONAL;
			const char *errstr = NULL;
			rev = strtonum(revision, 0, INT_MAX, &errstr);
			if (errstr != NULL) {
				parser_set_error(parser, PARSER_ERROR_EXPECTED_INT, errstr);
				return NULL;
			}
		}
	}

	int remove_distversionprefix = 0;
	int remove_distversionsuffix = 0;
	char *distversion;
	char *prefix;
	char *suffix;
	if (!is_git_describe_version(pool, newversion, &distversion, &prefix, &suffix)) {
		if (parser_lookup_variable_str(parser, "DISTVERSIONSUFFIX", PARSER_LOOKUP_FIRST, pool, &suffix, NULL)) {
			if (str_endswith(newversion, suffix)) {
				newversion = str_ndup(pool, newversion, strlen(newversion) - strlen(suffix));
			} else {
				remove_distversionsuffix = 1;
			}
			suffix = NULL;
		}
		if (parser_lookup_variable_str(parser, "DISTVERSIONPREFIX", PARSER_LOOKUP_FIRST, pool, &prefix, NULL)) {
			if (str_startswith(newversion, prefix)) {
				newversion += strlen(prefix);
			}
			prefix = NULL;
		}
	} else if (prefix == NULL) {
		remove_distversionprefix = 1;
		ver = "DISTVERSION";
	} else {
		ver = "DISTVERSION";
	}

	struct ParserSettings settings = parser_settings(parser);
	struct Parser *subparser = parser_new(pool, &settings);

	struct Array *script = mempool_array(pool);
	if (suffix) {
		array_append(script, str_printf(pool, "DISTVERSIONSUFFIX=%s", suffix));
	} else if (remove_distversionsuffix) {
		array_append(script, str_printf(pool, "DISTVERSIONSUFFIX!="));
	}

	if (prefix) {
		array_append(script, str_printf(pool, "DISTVERSIONPREFIX=%s", prefix));
	} else if (remove_distversionprefix) {
		array_append(script, str_printf(pool, "DISTVERSIONPREFIX!="));
	}

	if (strcmp(ver, "DISTVERSION") == 0) {
		array_append(script, str_printf(pool, "PORTVERSION!="));
	}

	if (distversion) {
		newversion = distversion;
	}

	if (rev > 0) {
		if (rev_opt) {
			// Reset PORTREVISION?= to 0
			array_append(script, str_printf(pool, "%s=%s\nPORTREVISION=0", ver, newversion));
		} else {
			// Remove PORTREVISION
			array_append(script, str_printf(pool, "%s=%s\nPORTREVISION!=", ver, newversion));
		}
	} else {
		array_append(script, str_printf(pool, "%s=%s", ver, newversion));
	}

	char *script_buf = str_join(pool, script, "\n");
	enum ParserError error = parser_read_from_buffer(subparser, script_buf, strlen(script_buf));
	if (error != PARSER_ERROR_OK) {
		return NULL;
	}
	error = parser_read_finish(subparser);
	if (error != PARSER_ERROR_OK) {
		return NULL;
	}
	error = parser_merge(parser, subparser, params->merge_behavior | PARSER_MERGE_SHELL_IS_DELETE);
	if (error != PARSER_ERROR_OK) {
		return NULL;
	}

	return NULL;
}

