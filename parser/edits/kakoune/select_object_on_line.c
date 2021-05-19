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

#include <limits.h>
#include <regex.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <libias/array.h>
#include <libias/str.h>

#include "parser.h"
#include "parser/edits.h"
#include "token.h"

static void
kak_error(struct Parser *parser, const char *errstr)
{
	char *buf = str_printf("echo -markup \"{Error}%s\"\n", errstr);
	parser_enqueue_output(parser, buf);
	free(buf);
}

PARSER_EDIT(kakoune_select_object_on_line)
{
	if (!(parser_settings(parser).behavior & PARSER_OUTPUT_RAWLINES)) {
		*error = PARSER_ERROR_INVALID_ARGUMENT;
		*error_msg = str_printf("needs PARSER_OUTPUT_RAWLINES");
		kak_error(parser, *error_msg);
		return NULL;
	}

	char *kak_cursor_line_buf = getenv("kak_cursor_line");
	if (!kak_cursor_line_buf) {
		*error = PARSER_ERROR_INVALID_ARGUMENT;
		*error_msg = str_printf("could not find kak_cursor_line");
		kak_error(parser, *error_msg);
		return NULL;
	}

	const char *errstr;
	size_t kak_cursor_line = strtonum(kak_cursor_line_buf, 1, INT_MAX, &errstr);
	if (kak_cursor_line == 0) {
		*error = PARSER_ERROR_INVALID_ARGUMENT;
		if (errstr) {
			*error_msg = str_printf("could not parse kak_cursor_line: %s", errstr);
		} else {
			*error_msg = str_printf("could not parse kak_cursor_line");
		}
		kak_error(parser, *error_msg);
		return NULL;
	}

	int found = 0;
	struct Range *target_start_range = NULL;
	ARRAY_FOREACH(ptokens, struct Token *, t) {
		struct Range *range = NULL;
		switch (token_type(t)) {
		case TARGET_START:
			target_start_range = token_lines(t);
			break;
		case TARGET_END:
			range = &(struct Range){ target_start_range->start, token_lines(t)->end - 1 };
			break;
		case VARIABLE_START:
			range = token_lines(t);
			break;
		default:
			break;
		}
		if (range && kak_cursor_line >= range->start && kak_cursor_line < range->end) {
			char *buf = str_printf("select %zu.1,%zu.10000000\n", range->start, range->end - 1);
			parser_enqueue_output(parser, buf);
			free(buf);
			found = 1;
			break;
		}
		range = NULL;
	}
	if (!found) {
		kak_error(parser, "no selectable object found on this line");
	}

	return NULL;
}

