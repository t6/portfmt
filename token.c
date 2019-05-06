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

#include <stdlib.h>
#include <string.h>

#include "conditional.h"
#include "target.h"
#include "token.h"
#include "util.h"
#include "variable.h"

struct Token {
	enum TokenType type;
	char *data;
	struct Conditional *cond;
	struct Variable *var;
	struct Target *target;
	int goalcol;
	struct Range lines;
};

struct Token *
token_new(enum TokenType type, struct Range *lines, const char *data,
	  char *varname, char *condname, char *targetname)
{
	struct Token *t = xmalloc(sizeof(struct Token));

	t->type = type;
	t->lines = *lines;

	if (data) {
		t->data = xstrdup(data);
	}
	if (targetname) {
		t->target = target_new(targetname);
	}
	if (condname) {
		t->cond = conditional_new(condname);
	}
	if (varname) {
		t->var = variable_new(varname);
	}

	return t;
}

struct Token *
token_new2(enum TokenType type, struct Range *lines, const char *data,
	   struct Variable *var, struct Conditional *cond, struct Target *target)
{
	struct Token *t = xmalloc(sizeof(struct Token));

	t->type = type;
	t->lines = *lines;

	if (data) {
		t->data = xstrdup(data);
	}
	if (target) {
		t->target = target_clone(target);
	}
	if (cond) {
		t->cond = conditional_clone(cond);
	}
	if (var) {
		t->var = variable_clone(var);
	}

	return t;
}

void
token_free(struct Token *token)
{
	if (token->data) {
		free(token->data);
	}
	if (token->var) {
		variable_free(token->var);
	}
	if (token->target) {
		target_free(token->target);
	}
	free(token);
}

struct Token *
token_clone(struct Token *token, const char *newdata)
{
	struct Token *t = xmalloc(sizeof(struct Token));

	t->type = token->type;
	if (newdata) {
		t->data = xstrdup(newdata);
	} else if (token->data) {
		t->data = xstrdup(token->data);
	}
	if (token->cond) {
		t->cond = conditional_clone(token->cond);
	}
	if (token->var) {
		t->var = variable_clone(token->var);
	}
	if (token->target) {
		t->target = target_clone(token->target);
	}
	t->goalcol = token->goalcol;
	t->lines = token->lines;

	return t;
}

struct Conditional *
token_conditional(struct Token *token)
{
	return token->cond;
}

char *
token_data(struct Token *token)
{
	return token->data;
}

int
token_goalcol(struct Token *token)
{
	return token->goalcol;
}

struct Range *
token_lines(struct Token *token)
{
	return &token->lines;
}

struct Target *
token_target(struct Token *token)
{
	return token->target;
}

enum TokenType
token_type(struct Token *token)
{
	return token->type;
}

struct Variable *
token_variable(struct Token *token)
{
	return token->var;
}

void
token_set_goalcol(struct Token *token, int goalcol)
{
	token->goalcol = goalcol;
}
