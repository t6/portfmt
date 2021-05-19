/*-
 * SPDX-License-Identifier: BSD-2-Clause-FreeBSD
 *
 * Copyright (c) 2020 Tobias Kortkamp <tobik@FreeBSD.org>
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

#include <assert.h>
#include <regex.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <libias/array.h>
#include <libias/str.h>

#include "parser.h"
#include "parser/edits.h"
#include "rules.h"
#include "token.h"
#include "variable.h"

enum State {
	NONE,
	CMAKE_ARGS,
	CMAKE_D,
};

PARSER_EDIT(refactor_sanitize_cmake_args)
{
	if (userdata != NULL) {
		*error = PARSER_ERROR_INVALID_ARGUMENT;
		return NULL;
	}

	struct Array *tokens = array_new();
	enum State state = NONE;
	ARRAY_FOREACH(ptokens, struct Token *, t) {
		switch (token_type(t)) {
		case VARIABLE_START: {
			char *name = variable_name(token_variable(t));
			char *helper = NULL;
			if (is_options_helper(parser, name, NULL, &helper, NULL)) {
				if (strcmp(helper, "CMAKE_ON") == 0 || strcmp(helper, "CMAKE_OFF") == 0 ||
				    strcmp(helper, "MESON_ON") == 0 || strcmp(helper, "MESON_OFF") == 0) {
					state = CMAKE_ARGS;
				} else {
					state = NONE;
				}
				free(helper);
			} else if (strcmp(name, "CMAKE_ARGS") == 0 || strcmp(name, "MESON_ARGS") == 0) {
				state = CMAKE_ARGS;
			} else {
				state = NONE;
			}
			array_append(tokens, t);
			break;
		} case VARIABLE_TOKEN:
			if (state == NONE) { 
				array_append(tokens, t);
			} else if (strcmp(token_data(t), "-D") == 0) {
				state = CMAKE_D;
				parser_mark_for_gc(parser, t);
			} else if (state == CMAKE_D) {
				char *buf = str_printf("-D%s", token_data(t));
				struct Token *newt = token_clone(t, buf);
				free(buf);
				array_append(tokens, newt);
				parser_mark_for_gc(parser, t);
				state = CMAKE_ARGS;
			} else {
				array_append(tokens, t);
			}
			break;
		case VARIABLE_END:
			state = NONE;
			array_append(tokens, t);
			break;
		default:
			array_append(tokens, t);
			break;
		}
	}

	return tokens;
}

