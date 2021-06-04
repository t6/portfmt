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

#include <ctype.h>
#include <regex.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <libias/array.h>
#include <libias/set.h>
#include <libias/str.h>
#include <libias/util.h>

#include "parser.h"
#include "parser/edits.h"
#include "rules.h"
#include "token.h"
#include "variable.h"

struct UnknownVariable {
	char *name;
	char *hint;
};

static struct UnknownVariable *
var_new(const char *name, const char *hint)
{
	struct UnknownVariable *var = xmalloc(sizeof(struct UnknownVariable));
	var->name = xstrdup(name);
	if (hint) {
		var->hint = xstrdup(hint);
	}
	return var;
}

static void
var_free(struct UnknownVariable *var)
{
	if (var) {
		free(var->name);
		free(var->hint);
	}
}

static int
var_compare(const void *ap, const void *bp, void *userdata)
{
	struct UnknownVariable *a = *(struct UnknownVariable **)ap;
	struct UnknownVariable *b = *(struct UnknownVariable **)bp;
	int retval = strcmp(a->name, b->name);
	if (retval == 0) {
		if (a->hint && b->hint) {
			return strcmp(a->hint, b->hint);
		} else if (a->hint) {
			return -1;
		} else {
			return 1;
		}
	} else {
		return retval;
	}
}

static void
check_opthelper(struct Parser *parser, struct ParserEditOutput *param, struct Set *vars, const char *option, int optuse, int optoff)
{
	const char *suffix;
	if (optoff) {
		suffix = "_OFF";
	} else {
		suffix = "";
	}
	char *var;
	if (optuse) {
		var = str_printf("%s_USE%s", option, suffix);
	} else {
		var = str_printf("%s_VARS%s", option, suffix);
	}
	struct Array *optvars;
	if (!parser_lookup_variable(parser, var, PARSER_LOOKUP_DEFAULT, &optvars, NULL)) {
		free(var);
		return;
	}

	ARRAY_FOREACH(optvars, const char *, token) {
		char *suffix = strchr(token, '+');
		if (!suffix) {
			suffix = strchr(token, '=');
			if (!suffix) {
				continue;
			}
		} else if (*(suffix + 1) != '=') {
			continue;
		}
		char *name = str_map(token, suffix - token, toupper);
		if (optuse) {
			char *tmp = name;
			name = str_printf("USE_%s", tmp);
			free(tmp);
		}
		struct UnknownVariable varskey = { .name = name, .hint = var };
		if (variable_order_block(parser, name, NULL) == BLOCK_UNKNOWN &&
		    !set_contains(vars, &varskey) &&
		    (param->keyfilter == NULL || param->keyfilter(parser, name, param->keyuserdata))) {
			set_add(vars, var_new(name, var));
			if (param->callback) {
				param->callback(name, name, var, param->callbackuserdata);
			}
		}
		free(name);
	}
	free(var);
	array_free(optvars);
}

PARSER_EDIT(output_unknown_variables)
{
	struct ParserEditOutput *param = userdata;
	if (param == NULL) {
		*error = PARSER_ERROR_INVALID_ARGUMENT;
		*error_msg = str_printf("missing parameter");
		return NULL;
	}

	param->found = 0;

	struct Set *vars = set_new(var_compare, NULL, var_free);
	ARRAY_FOREACH(ptokens, struct Token *, t) {
		if (token_type(t) != VARIABLE_START) {
			continue;
		}
		char *name = variable_name(token_variable(t));
		struct UnknownVariable varskey = { .name = name, .hint = NULL };
		if (variable_order_block(parser, name, NULL) == BLOCK_UNKNOWN &&
		    !is_declarative_var(parser, name) &&
		    !set_contains(vars, &varskey) &&
		    (param->keyfilter == NULL || param->keyfilter(parser, name, param->keyuserdata))) {
			set_add(vars, var_new(name, NULL));
			param->found = 1;
			if (param->callback) {
				param->callback(name, name, NULL, param->callbackuserdata);
			}
		}
	}
	struct Set *options = parser_metadata(parser, PARSER_METADATA_OPTIONS);
	SET_FOREACH (options, const char *, option) {
		check_opthelper(parser, param, vars, option, 1, 0);
		check_opthelper(parser, param, vars, option, 0, 0);
		check_opthelper(parser, param, vars, option, 1, 1);
		check_opthelper(parser, param, vars, option, 0, 1);
	}
	set_free(vars);

	return NULL;
}

