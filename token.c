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

#include <libias/str.h>
#include <libias/util.h>

#include "conditional.h"
#include "target.h"
#include "token.h"
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
	if (((type == VARIABLE_END || type == VARIABLE_START ||
	      type == VARIABLE_TOKEN) && varname == NULL) ||
	    ((type == CONDITIONAL_END || type == CONDITIONAL_START ||
	      type == CONDITIONAL_TOKEN) && condname  == NULL) ||
	    ((type == TARGET_COMMAND_END || type == TARGET_COMMAND_START ||
	      type == TARGET_COMMAND_TOKEN || type == TARGET_END ||
	      type == TARGET_START) && targetname == NULL)) {
		return NULL;
	}

	struct Target *target = NULL;
	if (targetname && (target = target_new(targetname)) == NULL) {
		return NULL;
	}

	struct Conditional *cond = NULL;
	if (condname && (cond = conditional_new(condname)) == NULL) {
		target_free(target);
		return NULL;
	}

	struct Variable *var = NULL;
	if (varname && (var = variable_new(varname)) == NULL) {
		target_free(target);
		conditional_free(cond);
		return NULL;
	}

	struct Token *t = xmalloc(sizeof(struct Token));
	t->type = type;
	t->lines = *lines;

	if (data) {
		t->data = str_dup(NULL, data);
	}
	t->cond = cond;
	t->target = target;
	t->var = var;

	return t;
}

struct Token *
token_new_comment(struct Range *lines, const char *data, struct Conditional *cond)
{
	if (lines == NULL || data == NULL) {
		return NULL;
	}

	struct Token *t = xmalloc(sizeof(struct Token));
	t->type = COMMENT;
	t->lines = *lines;
	if (cond) {
		t->cond = conditional_clone(cond);
	}
	t->data = str_dup(NULL, data);
	return t;
}

struct Token *
token_new_variable_end(struct Range *lines, struct Variable *var)
{
	if (lines == NULL || var == NULL) {
		return NULL;
	}

	struct Token *t = xmalloc(sizeof(struct Token));
	t->type = VARIABLE_END;
	t->lines = *lines;
	t->var = variable_clone(var);

	return t;
}

struct Token *
token_new_variable_start(struct Range *lines, struct Variable *var)
{
	if (lines == NULL || var == NULL) {
		return NULL;
	}

	struct Token *t = xmalloc(sizeof(struct Token));
	t->type = VARIABLE_START;
	t->lines = *lines;
	t->var = variable_clone(var);

	return t;
}

struct Token *
token_new_variable_token(struct Range *lines, struct Variable *var, const char *data)
{
	if (lines == NULL || var == NULL || data == NULL) {
		return NULL;
	}

	struct Token *t = xmalloc(sizeof(struct Token));
	t->type = VARIABLE_TOKEN;
	t->lines = *lines;
	t->var = variable_clone(var);
	t->data = str_dup(NULL, data);

	return t;
}

void
token_free(struct Token *token)
{
	if (token == NULL) {
		return;
	}
	free(token->data);
	conditional_free(token->cond);
	variable_free(token->var);
	target_free(token->target);
	free(token);
}

struct Token *
token_as_comment(struct Token *token)
{
	return token_new_comment(token_lines(token), token_data(token), token_conditional(token));
}

struct Token *
token_clone(struct Token *token, const char *newdata)
{
	struct Token *t = xmalloc(sizeof(struct Token));

	t->type = token->type;
	if (newdata) {
		t->data = str_dup(NULL, newdata);
	} else if (token->data) {
		t->data = str_dup(NULL, token->data);
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

const char *
token_type_tostring(enum TokenType type)
{
	switch (type) {
	case COMMENT:
		return "comment";
	case CONDITIONAL_END:
		return "conditional end";
	case CONDITIONAL_TOKEN:
		return "conditional token";
	case CONDITIONAL_START:
		return "conditional start";
	case TARGET_COMMAND_END:
		return "target command end";
	case TARGET_COMMAND_START:
		return "target command start";
	case TARGET_COMMAND_TOKEN:
		return "command token";
	case TARGET_END:
		return "target end";
	case TARGET_START:
		return "target start";
	case VARIABLE_END:
		return "variable end";
	case VARIABLE_START:
		return "variable start";
	case VARIABLE_TOKEN:
		return "variable token";
	}

	// Never reached
	abort();
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
