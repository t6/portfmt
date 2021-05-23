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

#include <sys/types.h>
#include <assert.h>
#include <regex.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <libias/mempool.h>
#include <libias/str.h>
#include <libias/util.h>

#include "regexp.h"
#include "rules.h"
#include "variable.h"

struct Variable {
	char *name;
	enum VariableModifier modifier;
};

struct Variable *
variable_new(const char *buf)
{
	SCOPE_MEMPOOL(pool);

	size_t len = strlen(buf);

	if (len < 2) {
		return NULL;
	}
	if (buf[len - 1] != '=') {
		return NULL;
	}

	enum VariableModifier mod = MODIFIER_ASSIGN;
	size_t i = 2;
	switch (buf[len - 2]) {
	case ':':
		mod = MODIFIER_EXPAND;
		break;
	case '!':
		mod = MODIFIER_SHELL;
		break;
	case '?':
		mod = MODIFIER_OPTIONAL;
		break;
	case '+':
		mod = MODIFIER_APPEND;
		break;
	default:
		i = 1;
		break;
	}

	char *name = str_trimr(pool, str_ndup(pool, buf, strlen(buf) - i));
	if (strcmp(name, "") == 0) {
		return NULL;
	}

	struct Variable *var = xmalloc(sizeof(struct Variable));
	var->modifier = mod;
	var->name = mempool_forget(pool, name);

	return var;
}

struct Variable *
variable_clone(struct Variable *var)
{
	struct Variable *newvar = xmalloc(sizeof(struct Variable));
	newvar->name = str_dup(NULL, var->name);
	newvar->modifier = var->modifier;
	return newvar;
}

void
variable_free(struct Variable *var)
{
	if (var == NULL) {
		return;
	}
	free(var->name);
	free(var);
}

int
variable_cmp(struct Variable *a, struct Variable *b)
{
	assert(a != NULL);
	assert(b != NULL);
	return strcmp(a->name, b->name);
}

int
variable_compare(const void *ap, const void *bp, void *userdata)
{
	struct Variable *a = *(struct Variable **)ap;
	struct Variable *b = *(struct Variable **)bp;
	return variable_cmp(a, b);
}

enum VariableModifier
variable_modifier(struct Variable *var)
{
	assert(var != NULL);
	return var->modifier;
}

void
variable_set_modifier(struct Variable *var, enum VariableModifier modifier)
{
	assert(var != NULL);
	var->modifier = modifier;
}

char *
variable_name(struct Variable *var)
{
	assert(var != NULL);
	return var->name;
}

char *
variable_tostring(struct Variable *var, struct Mempool *pool)
{
	assert(var != NULL);

	const char *mod = NULL;
	switch (var->modifier) {
	case MODIFIER_APPEND:
		mod = "+=";
		break;
	case MODIFIER_ASSIGN:
		mod = "=";
		break;
	case MODIFIER_EXPAND:
		mod = ":=";
		break;
	case MODIFIER_OPTIONAL:
		mod = "?=";
		break;
	case MODIFIER_SHELL:
		mod = "!=";
		break;
	}

	const char *sep = "";
	if (str_endswith(var->name, "+")) {
		sep = " ";
	}
	return str_printf(pool, "%s%s%s", var->name, sep, mod);
}
