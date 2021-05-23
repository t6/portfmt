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

#include <assert.h>
#include <regex.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <libias/mempool.h>
#include <libias/str.h>
#include <libias/util.h>

#include "conditional.h"
#include "regexp.h"
#include "rules.h"

struct Conditional {
	enum ConditionalType type;
};

struct Conditional *
conditional_new(char *s)
{
	SCOPE_MEMPOOL(pool);

	struct Regexp *re = regexp_new(pool, regex(RE_CONDITIONAL));
	if (regexp_exec(re, s) != 0) {
		return NULL;
	}

	char *tmp = regexp_substr(re, pool, 0);
	if (strlen(tmp) < 2) {
		return NULL;
	}

	char *type;
	if (tmp[0] == '.') {
		char *tmp2 = str_trim(pool, tmp + 1);
		type = str_printf(pool, ".%s", tmp2);
	} else {
		type = str_trim(pool, tmp);
	}

	enum ConditionalType cond_type;
	if (strcmp(type, "include") == 0) {
		cond_type = COND_INCLUDE_POSIX;
	} else if (strcmp(type, ".include") == 0) {
		cond_type = COND_INCLUDE;
	} else if (strcmp(type, ".error") == 0) {
		cond_type = COND_ERROR;
	} else if (strcmp(type, ".export") == 0) {
		cond_type = COND_EXPORT;
	} else if (strcmp(type, ".export-env") == 0) {
		cond_type = COND_EXPORT_ENV;
	} else if (strcmp(type, ".export.env") == 0) {
		cond_type = COND_EXPORT_ENV;
	} else if (strcmp(type, ".export-literal") == 0) {
		cond_type = COND_EXPORT_LITERAL;
	} else if (strcmp(type, ".info") == 0) {
		cond_type = COND_INFO;
	} else if (strcmp(type, ".undef") == 0) {
		cond_type = COND_UNDEF;
	} else if (strcmp(type, ".unexport") == 0) {
		cond_type = COND_UNEXPORT;
	} else if (strcmp(type, ".for") == 0) {
		cond_type = COND_FOR;
	} else if (strcmp(type, ".endfor") == 0) {
		cond_type = COND_ENDFOR;
	} else if (strcmp(type, ".unexport-env") == 0) {
		cond_type = COND_UNEXPORT_ENV;
	} else if (strcmp(type, ".warning") == 0) {
		cond_type = COND_WARNING;
	} else if (strcmp(type, ".if") == 0) {
		cond_type = COND_IF;
	} else if (strcmp(type, ".ifdef") == 0) {
		cond_type = COND_IFDEF;
	} else if (strcmp(type, ".ifndef") == 0) {
		cond_type = COND_IFNDEF;
	} else if (strcmp(type, ".ifmake") == 0) {
		cond_type = COND_IFMAKE;
	} else if (strcmp(type, ".ifnmake") == 0) {
		cond_type = COND_IFNMAKE;
	} else if (strcmp(type, ".else") == 0) {
		cond_type = COND_ELSE;
	} else if (strcmp(type, ".elif") == 0) {
		cond_type = COND_ELIF;
	} else if (strcmp(type, ".elifdef") == 0) {
		cond_type = COND_ELIFDEF;
	} else if (strcmp(type, ".elifndef") == 0) {
		cond_type = COND_ELIFNDEF;
	} else if (strcmp(type, ".elifmake") == 0) {
		cond_type = COND_ELIFMAKE;
	} else if (strcmp(type, ".endif") == 0) {
		cond_type = COND_ENDIF;
	} else if (strcmp(type, ".dinclude") == 0) {
		cond_type = COND_DINCLUDE;
	} else if (strcmp(type, ".sinclude") == 0 || strcmp(type, ".-include") == 0) {
		cond_type = COND_SINCLUDE;
	} else {
		return NULL;
	}

	struct Conditional *cond = xmalloc(sizeof(struct Conditional));
	cond->type = cond_type;

	return cond;
}

struct Conditional *
conditional_clone(struct Conditional *cond)
{
	struct Conditional *newcond = xmalloc(sizeof(struct Conditional));
	newcond->type = cond->type;
	return newcond;
}

void
conditional_free(struct Conditional *cond)
{
	free(cond);
}

char *
conditional_tostring(struct Conditional *cond, struct Mempool *pool)
{
	const char *type = NULL;

	switch(cond->type) {
	case COND_DINCLUDE:
		type = ".dinclude";
		break;
	case COND_ELIF:
		type = ".elif";
		break;
	case COND_ELIFDEF:
		type = ".elifdef";
		break;
	case COND_ELIFMAKE:
		type = ".elifmake";
		break;
	case COND_ELIFNDEF:
		type = ".elifndef";
		break;
	case COND_ELSE:
		type = ".else";
		break;
	case COND_ENDFOR:
		type = ".endfor";
		break;
	case COND_ENDIF:
		type = ".endif";
		break;
	case COND_ERROR:
		type = ".error";
		break;
	case COND_EXPORT_ENV:
		type = ".export-env";
		break;
	case COND_EXPORT_LITERAL:
		type = ".export-literal";
		break;
	case COND_EXPORT:
		type = ".export";
		break;
	case COND_FOR:
		type = ".for";
		break;
	case COND_IF:
		type = ".if";
		break;
	case COND_IFDEF:
		type = ".ifdef";
		break;
	case COND_IFMAKE:
		type = ".ifmake";
		break;
	case COND_IFNDEF:
		type = ".ifndef";
		break;
	case COND_IFNMAKE:
		type = ".ifnmake";
		break;
	case COND_INCLUDE_POSIX:
		type = "include";
		break;
	case COND_INCLUDE:
		type = ".include";
		break;
	case COND_INFO:
		type = ".info";
		break;
	case COND_SINCLUDE:
		type = ".sinclude";
		break;
	case COND_UNDEF:
		type = ".undef";
		break;
	case COND_UNEXPORT_ENV:
		type = ".unexport-env";
		break;
	case COND_UNEXPORT:
		type = ".unexport";
		break;
	case COND_WARNING:
		type = ".warning";
		break;
	}
	assert(type != NULL);

	return str_dup(pool, type);
}

enum ConditionalType
conditional_type(struct Conditional *cond)
{
	return cond->type;
}
