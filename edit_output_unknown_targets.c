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
#include <string.h>

#include "array.h"
#include "parser.h"
#include "rules.h"
#include "target.h"
#include "token.h"
#include "util.h"

struct Array *
edit_output_unknown_targets(struct Parser *parser, struct Array *tokens, enum ParserError *error, char **error_msg, const void *userdata)
{
	struct Array **unknowns = (struct Array **)userdata;
	if (!(parser_settings(parser).behavior & PARSER_OUTPUT_RAWLINES)) {
		*error = PARSER_ERROR_INVALID_ARGUMENT;
		xasprintf(error_msg, "needs PARSER_OUTPUT_RAWLINES");
		return NULL;
	}

	struct Array *targets = array_new();
	for (size_t i = 0; i < array_len(tokens); i++) {
		struct Token *t = array_get(tokens, i);
		if (token_type(t) != TARGET_START) {
			continue;
		}
		char *name = target_name(token_target(t));
		if (!is_special_target(name) && !is_known_target(parser, name)) {
			if (array_find(targets, name, str_compare, NULL) == -1) {
				parser_enqueue_output(parser, name);
				parser_enqueue_output(parser, "\n");
				array_append(targets, name);
			}
		}
	}
	if (unknowns) {
		*unknowns = targets;
	} else {
		array_free(targets);
	}

	return NULL;
}
