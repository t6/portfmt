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
#include <libias/str.h>
#include <libias/util.h>

#include "conditional.h"
#include "parser.h"
#include "parser/edits.h"
#include "token.h"
#include "variable.h"

static void
add_clones(struct Set *clones, struct Set *seen, struct Set *seen_in_cond)
{
	SET_FOREACH(seen_in_cond, char *, name) {
		if (set_contains(seen, name) && !set_contains(clones, name)) {
			set_add(clones, str_dup(NULL, name));
		}
	}
	set_truncate(seen_in_cond);
}

PARSER_EDIT(lint_clones)
{
	SCOPE_MEMPOOL(pool);

	struct Set **clones_ret = userdata;
	int no_color = parser_settings(parser).behavior & PARSER_OUTPUT_NO_COLOR;

	struct Set *seen = mempool_set(pool, str_compare, NULL, NULL);
	struct Set *seen_in_cond = mempool_set(pool, str_compare, NULL, NULL);
	struct Set *clones = mempool_set(pool, str_compare, NULL, free);
	int in_conditional = 0;
	ARRAY_FOREACH(ptokens, struct Token *, t) {
		switch (token_type(t)) {
		case CONDITIONAL_START:
			switch(conditional_type(token_conditional(t))) {
			case COND_FOR:
			case COND_IF:
			case COND_IFDEF:
			case COND_IFNDEF:
			case COND_IFMAKE:
				in_conditional++;
				break;
			case COND_ENDFOR:
			case COND_ENDIF:
				in_conditional--;
				if (in_conditional <= 0) {
					add_clones(clones, seen, seen_in_cond);
				}
				break;
			default:
				break;
			}
			break;
		case VARIABLE_START: {
			struct Variable *v = token_variable(t);
			if (variable_modifier(v) == MODIFIER_ASSIGN) {
				char *name = variable_name(v);
				if (in_conditional > 0) {
					set_add(seen_in_cond, name);
				} else if (set_contains(seen, name)) {
					if (!set_contains(clones, name)) {
						set_add(clones, str_dup(NULL, name));
					}
				} else {
					set_add(seen, name);
				}
			}
			break;
		} default:
			break;
		}
	}

	if (clones_ret == NULL && set_len(clones) > 0) {
		if (!no_color) {
			parser_enqueue_output(parser, ANSI_COLOR_CYAN);
		}
		parser_enqueue_output(parser, "# Variables set twice or more\n");
		if (!no_color) {
			parser_enqueue_output(parser, ANSI_COLOR_RESET);
		}
		SET_FOREACH (clones, const char *, name) {
			parser_enqueue_output(parser, name);
			parser_enqueue_output(parser, "\n");
		}
	}

	if (clones_ret != NULL) {
		*clones_ret = mempool_forget(pool, clones);
	}

	return NULL;
}

