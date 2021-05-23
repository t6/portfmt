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

static char *
get_merge_script(struct Mempool *extpool, struct Parser *parser, const char *variable)
{
	SCOPE_MEMPOOL(pool);
	struct Array *script = mempool_array(pool);

	struct Variable *var;
	if (strcmp(variable, "PORTEPOCH") == 0) {
		if ((var = parser_lookup_variable(parser, "PORTREVISION", PARSER_LOOKUP_FIRST, pool, NULL, NULL)) &&
		    variable_modifier(var) == MODIFIER_OPTIONAL) {
			array_append(script, "PORTREVISION=0\n");
		} else {
			array_append(script, "PORTREVISION!=\n");
		}
	}

	char *comment;
	char *current_revision;
	if ((var = parser_lookup_variable_str(parser, variable, PARSER_LOOKUP_FIRST, pool, &current_revision, &comment)) != NULL) {
		const char *errstr = NULL;
		int rev = strtonum(current_revision, 0, INT_MAX, &errstr);
		if (errstr == NULL) {
			rev++;
		} else {
			parser_set_error(parser, PARSER_ERROR_EXPECTED_INT, errstr);
			return NULL;
		}
		if (parser_lookup_variable(parser, "MASTERDIR", PARSER_LOOKUP_FIRST, pool, NULL, NULL) == NULL) {
			// In slave ports we do not delete the variable first since
			// they have a non-uniform structure and edit_merge will probably
			// insert it into a non-optimal position.
			//
			// In normal ports we can safely remove it.
			array_append(script, variable);
			array_append(script, "!=\n");
		}
		array_append(script, variable_tostring(var, pool));
		array_append(script, str_printf(pool, "%d %s\n", rev, comment));
	} else {
		array_append(script, variable);
		array_append(script, "=1\n");
	}

	return str_join(extpool, script, "");
}

PARSER_EDIT(edit_bump_revision)
{
	SCOPE_MEMPOOL(pool);

	const struct ParserEdit *params = userdata;
	if (params == NULL ||
	    params->subparser != NULL ||
	    params->merge_behavior != PARSER_MERGE_DEFAULT) {
		parser_set_error(parser, PARSER_ERROR_INVALID_ARGUMENT, NULL);
		return NULL;
	}
	const char *variable = params->arg1;

	if (variable == NULL) {
		variable = "PORTREVISION";
	}

	char *script = get_merge_script(pool, parser, variable);
	struct ParserSettings settings = parser_settings(parser);
	struct Parser *subparser = parser_new(pool, &settings);
	enum ParserError error = parser_read_from_buffer(subparser, script, strlen(script));
	if (error != PARSER_ERROR_OK) {
		return NULL;
	}
	error = parser_read_finish(subparser);
	if (error != PARSER_ERROR_OK) {
		return NULL;
	}
	error = parser_merge(parser, subparser, params->merge_behavior | PARSER_MERGE_SHELL_IS_DELETE | PARSER_MERGE_OPTIONAL_LIKE_ASSIGN);
	if (error != PARSER_ERROR_OK) {
		return NULL;
	}

	return NULL;
}

