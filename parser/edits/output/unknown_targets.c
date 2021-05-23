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
#include <libias/mempool.h>
#include <libias/set.h>
#include <libias/str.h>

#include "parser.h"
#include "parser/edits.h"
#include "rules.h"
#include "target.h"
#include "token.h"

static int
add_target(struct Parser *parser, struct Mempool *extpool, struct ParserEditOutput *param, struct Set *targets, struct Set *post_plist_targets, char *name, int deps)
{
	if (deps && is_special_source(name)) {
		return 0;
	}
	if (is_special_target(name)) {
		return 1;
	}
	if (!is_known_target(parser, name) &&
	    !set_contains(post_plist_targets, name) &&
	    !set_contains(targets, name) &&
	    (param->keyfilter == NULL || param->keyfilter(parser, name, param->keyuserdata))) {
		set_add(targets, name);
		param->found = 1;
		if (param->callback) {
			// XXX: provide option as hint for opthelper targets?
			param->callback(extpool, name, name, NULL, param->callbackuserdata);
		}
	}
	return 0;
}

PARSER_EDIT(output_unknown_targets)
{
	SCOPE_MEMPOOL(pool);

	struct ParserEditOutput *param = userdata;
	if (param == NULL) {
		parser_set_error(parser, PARSER_ERROR_INVALID_ARGUMENT, "missing parameter");
		return NULL;
	}

	param->found = 0;
	struct Set *post_plist_targets = parser_metadata(parser, PARSER_METADATA_POST_PLIST_TARGETS);
	struct Set *targets = mempool_set(pool, str_compare, NULL, NULL);
	ARRAY_FOREACH(ptokens, struct Token *, t) {
		if (token_type(t) != TARGET_START) {
			continue;
		}
		int skip_deps = 0;
		ARRAY_FOREACH(target_names(token_target(t)), char *, name) {
			if (add_target(parser, extpool, param, targets, post_plist_targets, name, 0)) {
				skip_deps = 1;
			}
		}
		if (!skip_deps) {
			ARRAY_FOREACH(target_dependencies(token_target(t)), char *, name) {
				add_target(parser, extpool, param, targets, post_plist_targets, name, 1);
			}
		}
	}

	return NULL;
}

