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

#include <libias/array.h>
#include <libias/str.h>

#include "parser.h"
#include "parser/edits.h"
#include "token.h"
#include "variable.h"

PARSER_EDIT(output_variable_value)
{
	struct ParserEditOutput *param = userdata;
	if (param == NULL) {
		parser_set_error(parser, PARSER_ERROR_INVALID_ARGUMENT, "missing parameter");
		return NULL;
	}

	param->found = 0;

	ARRAY_FOREACH(ptokens, struct Token *, t) {
		switch (token_type(t)) {
		case VARIABLE_START:
			if ((param->keyfilter == NULL || param->keyfilter(parser, variable_name(token_variable(t)), param->keyuserdata))) {
				param->found = 1;
			}
			break;
		case VARIABLE_TOKEN:
			if (param->found && token_data(t) &&
			    (param->keyfilter == NULL || param->keyfilter(parser, variable_name(token_variable(t)), param->keyuserdata)) &&
			    (param->filter == NULL || param->filter(parser, token_data(t), param->filteruserdata))) {
				param->found = 1;
				if (param->callback) {
					param->callback(extpool, variable_name(token_variable(t)), token_data(t), NULL, param->callbackuserdata);
				}
			}
			break;
		default:
			break;
		}
	}

	return NULL;
}

