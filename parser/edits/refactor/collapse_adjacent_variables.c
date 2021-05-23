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

#include <regex.h>
#include <stdlib.h>
#include <stdio.h>

#include <libias/array.h>
#include <libias/mempool.h>
#include <libias/set.h>
#include <libias/util.h>

#include "parser.h"
#include "parser/edits.h"
#include "rules.h"
#include "token.h"
#include "variable.h"

static int
has_valid_modifier(struct Variable *var) {
	switch (variable_modifier(var)) {
	case MODIFIER_APPEND:
	case MODIFIER_ASSIGN:
		return 1;
	default:
		return 0;
	}
}

static int
next_variable_has_eol_comment(struct Array *tokens, size_t i) {
	// Skip until next variable
	int found = 0;
	for (i++; i < array_len(tokens); i++) {
		struct Token *t = array_get(tokens, i);
		if (token_type(t) == VARIABLE_START) {
			i++;
			found = 1;
			break;
		}
	}
	if (!found) {
		return 0;
	}
	for (; i < array_len(tokens); i++) {
		struct Token *t = array_get(tokens, i);
		switch (token_type(t)) {
		case VARIABLE_TOKEN:
			if (is_comment(t)) {
				return 1;
			}
			break;
		case VARIABLE_END:
			return 0;
		default:
			abort();
		}
	}
	return 0;
}

PARSER_EDIT(refactor_collapse_adjacent_variables)
{
	SCOPE_MEMPOOL(pool);

	if (userdata != NULL) {
		parser_set_error(parser, PARSER_ERROR_INVALID_ARGUMENT, NULL);
		return NULL;
	}

	struct Array *tokens = array_new();
	struct Variable *last_var = NULL;
	struct Token *last_end = NULL;
	struct Token *last_token = NULL;
	struct Set *ignored_tokens = mempool_set(pool, NULL, NULL, NULL);
	ARRAY_FOREACH(ptokens, struct Token *, t) {
		switch (token_type(t)) {
		case VARIABLE_START:
			if (last_var != NULL &&
			    variable_cmp(token_variable(t), last_var) == 0 &&
			    has_valid_modifier(last_var) &&
			    has_valid_modifier(token_variable(t)) &&
			    last_end) {
				if (!next_variable_has_eol_comment(ptokens, t_index)) {
					set_add(ignored_tokens, t);
					set_add(ignored_tokens, last_end);
				}
				last_end = NULL;
			}
			break;
		case VARIABLE_TOKEN:
			last_token = t;
			break;
		case VARIABLE_END:
			if ((!last_token || !is_comment(last_token)) &&
			    !next_variable_has_eol_comment(ptokens, t_index)) {
				last_end = t;
			}
			last_token = NULL;
			last_var = token_variable(t);
			break;
		default:
			last_var = NULL;
			break;
		}
	}

	ARRAY_FOREACH(ptokens, struct Token *, t) {
		if (set_contains(ignored_tokens, t)) {
			parser_mark_for_gc(parser, t);
		} else {
			array_append(tokens, t);
		}
	}

	return tokens;
}

