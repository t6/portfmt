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
#include <sys/param.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <ctype.h>
#if HAVE_ERR
# include <err.h>
#endif
#include <errno.h>
#include <math.h>
#include <regex.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include <unistd.h>

#include <libias/array.h>
#include <libias/diff.h>
#include <libias/diffutil.h>
#include <libias/io.h>
#include <libias/map.h>
#include <libias/mempool.h>
#include <libias/set.h>
#include <libias/str.h>
#include <libias/util.h>

#include "conditional.h"
#include "parser.h"
#include "parser/edits.h"
#include "regexp.h"
#include "rules.h"
#include "target.h"
#include "token.h"
#include "variable.h"

struct Parser {
	struct ParserSettings settings;
	int continued;
	int in_target;
	struct Range lines;
	int skip;
	enum ParserError error;
	char *error_msg;
	char *inbuf;
	char *condname;
	char *targetname;
	char *varname;

	struct Set *edited;
	struct Mempool *pool;
	struct Mempool *tokengc;
	struct Array *tokens;
	struct Array *result;
	struct Array *rawlines;
	void *metadata[PARSER_METADATA_USES + 1];
	int metadata_valid[PARSER_METADATA_USES + 1];

	int read_finished;
};

#define INBUF_SIZE 131072

static size_t consume_comment(const char *);
static size_t consume_conditional(const char *);
static size_t consume_target(const char *);
static size_t consume_token(struct Parser *, const char *, size_t, char, char, int);
static size_t consume_var(const char *);
static int is_empty_line(const char *);
static void parser_append_token(struct Parser *, enum TokenType, const char *);
static void parser_find_goalcols(struct Parser *);
static void parser_meta_values(struct Parser *, const char *, struct Set *);
static void parser_metadata_alloc(struct Parser *);
static void parser_metadata_free(struct Parser *);
static void parser_metadata_port_options(struct Parser *);
static void parser_output_dump_tokens(struct Parser *);
static void parser_output_prepare(struct Parser *);
static void parser_output_print_rawlines(struct Parser *, struct Range *);
static void parser_output_print_target_command(struct Parser *, struct Array *);
static struct Array *parser_output_sort_opt_use(struct Parser *, struct Mempool *, struct Array *);
static struct Array *parser_output_reformatted_helper(struct Parser *, struct Mempool *, struct Array *);
static void parser_output_reformatted(struct Parser *);
static void parser_output_diff(struct Parser *);
static void parser_propagate_goalcol(struct Parser *, size_t, size_t, int);
static void parser_read_internal(struct Parser *);
static void parser_read_line(struct Parser *, char *);
static void parser_tokenize(struct Parser *, const char *, enum TokenType, size_t);
static void print_newline_array(struct Parser *, struct Mempool *, struct Array *);
static void print_token_array(struct Parser *, struct Mempool *, struct Array *);
static char *range_tostring(struct Mempool *, struct Range *);

#include "parser/constants.h"

size_t
consume_comment(const char *buf)
{
	for (const char *bufp = buf; *bufp != 0; bufp++) {
		if (*bufp == '#') {
			return strlen(buf);
		} else if (!isspace(*bufp)) {
			break;
		}
	}
	return 0;
}

size_t
consume_conditional(const char *buf)
{
	SCOPE_MEMPOOL(pool);

	size_t pos = 0;
	struct Regexp *re = regexp_new(pool, regex(RE_CONDITIONAL));
	if (regexp_exec(re, buf) == 0) {
		pos = regexp_length(re, 0);
	}

	if(pos > 0 && (buf[pos - 1] == '(' || buf[pos - 1] == '!')) {
		pos--;
	}

	return pos;
}

size_t
consume_target(const char *buf)
{
	// Variable assignments are prioritized and can be ambigious
	// due to :=, so check for it first.  Targets can also not
	// start with a tab which implies a conditional.
	if (consume_var(buf) > 0 || *buf == '\t') {
		return 0;
	}

	// ^[^:]+(::?|!)
	// We are more strict than make(1) and do not accept something
	// like just ":".
	size_t len = strlen(buf);
	for (size_t i = 0; i < len; i++) {
		if (buf[i] == ':' || buf[i] == '!') {
			if (i == 0) {
				return 0;
			}
			// Consume the next ':' too if any
			if (buf[i] == ':' && i < len - 1 && buf[i + 1] == ':') {
				i++;
			}
			return i;
		}
	}

	return 0;
}

size_t
consume_token(struct Parser *parser, const char *line, size_t pos,
	      char startchar, char endchar, int eol_ok)
{
	int counter = 0;
	int escape = 0;
	size_t i = pos;
	for (; i < strlen(line); i++) {
		char c = line[i];
		if (escape) {
			escape = 0;
			continue;
		}
		if (startchar == endchar) {
			if (c == startchar) {
				if (counter == 1) {
					return i;
				} else {
					counter++;
				}
			} else if (c == '\\') {
				escape = 1;
			}
		} else {
			if (c == startchar) {
				counter++;
			} else if (c == endchar && counter == 1) {
				return i;
			} else if (c == endchar) {
				counter--;
			} else if (c == '\\') {
				escape = 1;
			}
		}
	}
	if (!eol_ok) {
		SCOPE_MEMPOOL(pool);
		parser_set_error(parser, PARSER_ERROR_EXPECTED_CHAR, str_printf(pool, "%c", endchar));
		return 0;
	} else {
		return i;
	}
}

size_t
consume_var(const char *buf)
{
	size_t len = strlen(buf);

	// ^ *
	size_t pos;
	for (pos = 0; pos < len && buf[pos] == ' '; pos++);

	// [^[:space:]=]+
	size_t i;
	for (i = pos; i < len && !(isspace(buf[i]) || buf[i] == '='); i++);
	if (pos == i) {
		return 0;
	}
	pos = i;

	// [[:space:]]*
	for (; pos < len && isspace(buf[pos]); pos++);

	// [+!?:]?
	switch (buf[pos]) {
	case '+':
	case '!':
	case '?':
	case ':':
		pos++;
		break;
	case '=':
		return pos + 1;
	default:
		return 0;
	}

	// =
	if (buf[pos] != '=') {
		return 0;
	}
	return pos + 1;
}

int
is_empty_line(const char *buf)
{
	for (const char *p = buf; *p != 0; p++) {
		if (!isspace(*p)) {
			return 0;
		}
	}

	return 1;
}

char *
range_tostring(struct Mempool *pool, struct Range *range)
{
	assert(range);
	assert(range->start < range->end);

	if (range->start == range->end - 1) {
		return str_printf(pool, "%zu", range->start);
	} else {
		return str_printf(pool, "%zu-%zu", range->start, range->end - 1);
	}
}

static int
parser_is_category_makefile(struct Parser *parser)
{
	ARRAY_FOREACH(parser->tokens, struct Token *, t) {
		if (token_type(t) == CONDITIONAL_TOKEN &&
		    conditional_type(token_conditional(t)) == COND_INCLUDE &&
		    strcmp(token_data(t), "<bsd.port.subdir.mk>") == 0) {
			return 1;
		}
	}

	return 0;
}

void
parser_init_settings(struct ParserSettings *settings)
{
	settings->filename = NULL;
	settings->behavior = PARSER_DEFAULT;
	settings->diff_context = 3;
	settings->target_command_format_threshold = 8;
	settings->target_command_format_wrapcol = 65;
	settings->wrapcol = 80;
}

struct Parser *
parser_new(struct Mempool *extpool, struct ParserSettings *settings)
{
	rules_init();

	struct Parser *parser = xmalloc(sizeof(struct Parser));

	parser->edited = set_new(NULL, NULL, NULL);
	parser->pool = mempool_new();
	parser->tokengc = mempool_new_unique();
	parser->rawlines = array_new();
	parser->result = array_new();
	parser->tokens = array_new();
	parser_metadata_alloc(parser);
	parser->error = PARSER_ERROR_OK;
	parser->error_msg = NULL;
	parser->lines.start = 1;
	parser->lines.end = 1;
	parser->inbuf = xmalloc(INBUF_SIZE);
	parser->settings = *settings;
	if (settings->filename) {
		parser->settings.filename = str_dup(NULL, settings->filename);
	} else {
		parser->settings.filename = str_dup(NULL, "/dev/stdin");
	}

	if (parser->settings.behavior & PARSER_OUTPUT_EDITED) {
		parser->settings.behavior &= ~PARSER_COLLAPSE_ADJACENT_VARIABLES;
	}

	if ((settings->behavior & PARSER_OUTPUT_DUMP_TOKENS) ||
	    (settings->behavior & PARSER_OUTPUT_DIFF) ||
	    (settings->behavior & PARSER_OUTPUT_RAWLINES)) {
		settings->behavior &= ~PARSER_OUTPUT_INPLACE;
	}

	return mempool_add(extpool, parser, parser_free);
}

void
parser_free(struct Parser *parser)
{
	if (parser == NULL) {
		return;
	}

	ARRAY_FOREACH(parser->result, void *, x) {
		free(x);
	}
	array_free(parser->result);

	ARRAY_FOREACH(parser->rawlines, char *, line) {
		free(line);
	}
	array_free(parser->rawlines);

	mempool_free(parser->pool);
	mempool_free(parser->tokengc);
	set_free(parser->edited);
	parser_metadata_free(parser);
	array_free(parser->tokens);

	free(parser->condname);
	free(parser->targetname);
	free(parser->varname);
	free(parser->settings.filename);
	free(parser->error_msg);
	free(parser->inbuf);
	free(parser);
}

void
parser_set_error(struct Parser *parser, enum ParserError error, const char *msg)
{
	free(parser->error_msg);
	if (msg) {
		parser->error_msg = str_dup(NULL, msg);
	} else {
		parser->error_msg = NULL;
	}
	parser->error = error;
}

char *
parser_error_tostring(struct Parser *parser, struct Mempool *extpool)
{
	SCOPE_MEMPOOL(pool);

	char *lines = range_tostring(pool, &parser->lines);
	switch (parser->error) {
	case PARSER_ERROR_OK:
		return str_printf(extpool, "line %s: no error", lines);
	case PARSER_ERROR_BUFFER_TOO_SMALL:
		if (parser->error_msg) {
			return str_printf(extpool, "line %s: buffer too small: %s", lines, parser->error_msg);
		} else {
			return str_printf(extpool, "line %s: buffer too small", lines);
		}
	case PARSER_ERROR_DIFFERENCES_FOUND:
		return str_printf(extpool, "differences found");
	case PARSER_ERROR_EDIT_FAILED:
		if (parser->error_msg) {
			return str_printf(extpool, "%s", parser->error_msg);
		} else {
			return str_printf(extpool, "line %s: edit failed", lines);
		}
	case PARSER_ERROR_EXPECTED_CHAR:
		if (parser->error_msg) {
			return str_printf(extpool, "line %s: expected char: %s", lines, parser->error_msg);
		} else {
			return str_printf(extpool, "line %s: expected char", lines);
		}
	case PARSER_ERROR_EXPECTED_INT:
		if (parser->error_msg) {
			return str_printf(extpool, "line %s: expected integer: %s", lines, parser->error_msg);
		} else {
			return str_printf(extpool, "line %s: expected integer", lines);
		}
	case PARSER_ERROR_EXPECTED_TOKEN:
		if (parser->error_msg) {
			return str_printf(extpool, "line %s: expected %s", lines, parser->error_msg);
		} else {
			return str_printf(extpool, "line %s: expected token", lines);
		}
	case PARSER_ERROR_INVALID_ARGUMENT:
		if (parser->error_msg) {
			return str_printf(extpool, "invalid argument: %s", parser->error_msg);
		} else {
			return str_printf(extpool, "invalid argument");
		}
	case PARSER_ERROR_INVALID_REGEXP:
		if (parser->error_msg) {
			return str_printf(extpool, "invalid regexp: %s", parser->error_msg);
		} else {
			return str_printf(extpool, "invalid regexp");
		}
	case PARSER_ERROR_IO:
		if (parser->error_msg) {
			return str_printf(extpool, "line %s: IO error: %s", lines, parser->error_msg);
		} else {
			return str_printf(extpool, "line %s: IO error", lines);
		}
	case PARSER_ERROR_UNHANDLED_TOKEN_TYPE:
		if (parser->error_msg) {
			return str_printf(extpool, "line %s: unhandled token type: %s", lines, parser->error_msg);
		} else {
			return str_printf(extpool, "line %s: unhandled token type", lines);
		}
	case PARSER_ERROR_UNSPECIFIED:
		if (parser->error_msg) {
			return str_printf(extpool, "line %s: parse error: %s", lines, parser->error_msg);
		} else {
			return str_printf(extpool, "line %s: parse error", lines);
		}
	default:
		abort();
	}
}

void
parser_append_token(struct Parser *parser, enum TokenType type, const char *data)
{
	struct Token *t = token_new(type, &parser->lines, data, parser->varname,
				    parser->condname, parser->targetname);
	if (t == NULL) {
		parser_set_error(parser, PARSER_ERROR_EXPECTED_TOKEN, token_type_tostring(type));
		return;
	}
	parser_mark_for_gc(parser, t);
	array_append(parser->tokens, t);
}

void
parser_enqueue_output(struct Parser *parser, const char *s)
{
	assert(s != NULL);
	array_append(parser->result, str_dup(NULL, s));
}

void
parser_tokenize(struct Parser *parser, const char *line, enum TokenType type, size_t start)
{
	SCOPE_MEMPOOL(pool);

	int dollar = 0;
	int escape = 0;
	char *token = NULL;
	size_t i = start;
	for (; i < strlen(line); i++) {
		assert(i >= start);
		char c = line[i];
		if (escape) {
			escape = 0;
			if (c == '#' || c == '\\' || c == '$' || isspace(c)) {
				continue;
			}
		}
		if (dollar) {
			if (dollar > 1) {
				if (c == '(') {
					i = consume_token(parser, line, i - 2, '(', ')', 0);
					if (parser->error != PARSER_ERROR_OK) {
						return;
					}
					dollar = 0;
					continue;
				} else if (c == '$') {
					dollar++;
				} else {
					dollar = 0;
				}
			} else if (c == '{') {
				i = consume_token(parser, line, i, '{', '}', 0);
				dollar = 0;
			} else if (c == '(') {
				i = consume_token(parser, line, i, '(', ')', 0);
				dollar = 0;
			} else if (isalnum(c) || c == '@' || c == '<' || c == '>' || c == '/' ||
				   c == '?' || c == '*' || c == '^' || c == '-' || c == '_' ||
				   c == ')') {
				dollar = 0;
			} else if (c == ' ' || c == '\\') {
				/* '$ ' or '$\' are ignored by make for some reason instead of making
				 * it an error, so we do the same...
				 */
				dollar = 0;
				i--;
			} else if (c == 1) {
				dollar = 0;
			} else if (c == '$') {
				dollar++;
			} else {
				parser_set_error(parser, PARSER_ERROR_EXPECTED_CHAR, "$");
			}
			if (parser->error != PARSER_ERROR_OK) {
				return;
			}
		} else {
			if (c == ' ' || c == '\t') {
				token = str_trim(pool, str_slice(pool, line, start, i));
				if (strcmp(token, "") != 0 && strcmp(token, "\\") != 0) {
					parser_append_token(parser, type, token);
				}
				token = NULL;
				start = i;
			} else if (c == '"') {
				i = consume_token(parser, line, i, '"', '"', 1);
			} else if (c == '\'') {
				i = consume_token(parser, line, i, '\'', '\'', 1);
			} else if (c == '`') {
				i = consume_token(parser, line, i, '`', '`', 1);
			} else if (c == '$') {
				dollar++;
			} else if (c == '\\') {
				escape = 1;
			} else if (c == '#') {
				token = str_trim(pool, str_slice(pool, line, i, -1));
				parser_append_token(parser, type, token);
				token = NULL;
				parser->error = PARSER_ERROR_OK;
				return;
			}
			if (parser->error != PARSER_ERROR_OK) {
				return;
			}
		}
	}

	token = str_trim(pool, str_slice(pool, line, start, i));
	if (strcmp(token, "") != 0) {
		parser_append_token(parser, type, token);
	}
	parser->error = PARSER_ERROR_OK;
}

void
parser_propagate_goalcol(struct Parser *parser, size_t start, size_t end,
			 int moving_goalcol)
{
	moving_goalcol = MAX(16, moving_goalcol);
	for (size_t k = start; k <= end; k++) {
		struct Token *t = array_get(parser->tokens, k);
		if (token_variable(t) && !skip_goalcol(parser, token_variable(t))) {
			token_set_goalcol(t, moving_goalcol);
		}
	}
}

void
parser_find_goalcols(struct Parser *parser)
{
	int moving_goalcol = 0;
	size_t last = 0;
	ssize_t tokens_start = -1;
	ssize_t tokens_end = -1;
	ARRAY_FOREACH(parser->tokens, struct Token *, t) {
		switch (token_type(t)) {
		case VARIABLE_END:
		case VARIABLE_START:
			break;
		case VARIABLE_TOKEN:
			if (tokens_start == -1) {
				tokens_start = t_index;
			}
			tokens_end = t_index;

			struct Variable *var = token_variable(t);
			if (var && skip_goalcol(parser, var)) {
				token_set_goalcol(t, indent_goalcol(var));
			} else {
				moving_goalcol = MAX(indent_goalcol(var), moving_goalcol);
			}
			break;
		case TARGET_END:
		case TARGET_START:
		case CONDITIONAL_END:
		case CONDITIONAL_START:
		case CONDITIONAL_TOKEN:
		case TARGET_COMMAND_END:
		case TARGET_COMMAND_START:
		case TARGET_COMMAND_TOKEN:
			break;
		case COMMENT:
			/* Ignore comments in between variables and
			 * treat variables after them as part of the
			 * same block, i.e., indent them the same way.
			 */
			if (is_comment(t)) {
				continue;
			}
			if (tokens_start != -1) {
				parser_propagate_goalcol(parser, last, tokens_end, moving_goalcol);
				moving_goalcol = 0;
				last = t_index;
				tokens_start = -1;
			}
			break;
		default:
			parser->error = PARSER_ERROR_UNHANDLED_TOKEN_TYPE;
			return;
		}
	}
	if (tokens_start != -1) {
		parser_propagate_goalcol(parser, last, tokens_end, moving_goalcol);
	}
}

void
print_newline_array(struct Parser *parser, struct Mempool *pool, struct Array *arr)
{
	struct Token *o = array_get(arr, 0);
	assert(o && token_data(o) != NULL);
	assert(strlen(token_data(o)) != 0);
	assert(token_type(o) == VARIABLE_TOKEN);

	if (array_len(arr) == 0) {
		parser_enqueue_output(parser, variable_tostring(token_variable(o), pool));
		parser_enqueue_output(parser, "\n");
		parser->error = PARSER_ERROR_OK;
		return;
	}

	char *start = variable_tostring(token_variable(o), pool);
	parser_enqueue_output(parser, start);
	size_t ntabs = ceil((MAX(16, token_goalcol(o)) - strlen(start)) / 8.0);
	char *sep = str_repeat(pool, "\t", ntabs);
	const char *end = " \\\n";
	ARRAY_FOREACH(arr, struct Token *, o) {
		struct Token *next = array_get(arr, o_index + 1);
		char *line = token_data(o);
		if (!line || strlen(line) == 0) {
			continue;
		}
		if (o_index == array_len(arr) - 1) {
			end = "\n";
		}
		parser_enqueue_output(parser, sep);
		parser_enqueue_output(parser, line);
		// Do not wrap end of line comments
		if (next && is_comment(next)) {
			sep = str_dup(pool, " ");
			continue;
		}
		parser_enqueue_output(parser, end);
		switch (token_type(o)) {
		case VARIABLE_TOKEN:
			if (o_index == 0) {
				size_t ntabs = ceil(MAX(16, token_goalcol(o)) / 8.0);
				sep = str_repeat(pool, "\t", ntabs);
			}
			break;
		case CONDITIONAL_TOKEN:
			sep = str_dup(NULL, "\t");
			break;
		case TARGET_COMMAND_TOKEN:
			sep = str_dup(NULL, "\t\t");
			break;
		default:
			parser->error = PARSER_ERROR_UNHANDLED_TOKEN_TYPE;
			return;
		}
	}
}

void
print_token_array(struct Parser *parser, struct Mempool *pool, struct Array *tokens)
{
	if (array_len(tokens) < 2) {
		print_newline_array(parser, pool, tokens);
		return;
	}

	struct Array *arr = mempool_array(pool);
	struct Token *o = array_get(tokens, 0);
	size_t wrapcol;
	if (token_variable(o) && ignore_wrap_col(parser, token_variable(o))) {
		wrapcol = 99999999;
	} else {
		/* Minus ' \' at end of line */
		wrapcol = parser->settings.wrapcol - token_goalcol(o) - 2;
	}

	size_t rowsz = 8192;
	char *row = mempool_alloc(pool, rowsz);
	struct Token *token = NULL;
	ARRAY_FOREACH(tokens, struct Token *, t) {
		token = t;
		size_t tokenlen = strlen(token_data(token));
		if (tokenlen == 0) {
			continue;
		}
		if ((strlen(row) + tokenlen) > wrapcol) {
			if (strlen(row) == 0) {
				array_append(arr, token);
				continue;
			} else {
				struct Token *t = token_clone(token, row);
				parser_mark_for_gc(parser, t);
				array_append(arr, t);
				row[0] = 0;
			}
		}
		size_t len;
		if (strlen(row) == 0) {
			if ((len = strlcpy(row, token_data(token), rowsz)) >= rowsz) {
				parser->error = PARSER_ERROR_BUFFER_TOO_SMALL;
				return;
			}
		} else {
			if ((len = strlcat(row, " ", rowsz)) >= rowsz) {
				parser->error = PARSER_ERROR_BUFFER_TOO_SMALL;
				return;
			}
			if ((len = strlcat(row, token_data(token), rowsz)) >= rowsz) {
				parser->error = PARSER_ERROR_BUFFER_TOO_SMALL;
				return;
			}
		}
	}
	if (token && strlen(row) > 0 && array_len(arr) < array_len(tokens)) {
		struct Token *t = token_clone(token, row);
		parser_mark_for_gc(parser, t);
		array_append(arr, t);
	}
	print_newline_array(parser, pool, arr);
}

void
parser_output_print_rawlines(struct Parser *parser, struct Range *lines)
{
	for (size_t i = lines->start; i < lines->end; i++) {
		parser_enqueue_output(parser, array_get(parser->rawlines, i - 1));
		parser_enqueue_output(parser, "\n");
	}
}

void
parser_output_print_target_command(struct Parser *parser, struct Array *tokens)
{
	if (array_len(tokens) == 0) {
		return;
	}

	SCOPE_MEMPOOL(pool);
	struct Array *commands = mempool_array(pool);
	struct Array *merge = mempool_array(pool);
	char *command = NULL;
	int wrap_after = 0;
	ARRAY_FOREACH(tokens, struct Token *, t) {
		char *word = token_data(t);
		assert(token_type(t) == TARGET_COMMAND_TOKEN);
		assert(word && strlen(word) != 0);

		if (command == NULL) {
			command = word;
			if (*command == '@') {
				command++;
			}
		}
		if (target_command_should_wrap(word)) {
			command = NULL;
		}

		if (command &&
		    (strcmp(command, "${SED}") == 0 ||
		     strcmp(command, "${REINPLACE_CMD}") == 0)) {
			if (strcmp(word, "-e") == 0 || strcmp(word, "-i") == 0) {
				array_append(merge, word);
				wrap_after = 1;
				continue;
			}
		}

		array_append(merge, word);
		array_append(commands, str_join(pool, merge, " "));
		if (wrap_after) {
			// An empty string is abused as a "wrap line here" marker
			array_append(commands, str_dup(pool, ""));
			wrap_after = 0;
		}
		array_truncate(merge);
	}
	if (array_len(merge) > 0) {
		array_append(commands, str_join(pool, merge, " "));
		if (wrap_after) {
			// An empty string is abused as a "wrap line here" marker
			array_append(commands, str_dup(pool, ""));
			wrap_after = 0;
		}
	}
	merge = NULL;

	const char *endline = "\n";
	const char *endnext = "\\\n";
	const char *endword = " ";
	const char *startlv0 = "";
	const char *startlv1 = "\t";
	const char *startlv2 = "\t\t";
	const char *start = startlv0;

	// Find the places we need to wrap to the next line.
	struct Set *wraps = mempool_set(pool, NULL, NULL, NULL);
	size_t column = 8;
	int complexity = 0;
	size_t command_i = 0;
	ARRAY_FOREACH(commands, char *, word) {
		if (command == NULL) {
			command = word;
			command_i = word_index;
		}
		if (target_command_should_wrap(word)) {
			command = NULL;
			command_i = 0;
		}

		for (char *c = word; *c != 0; c++) {
			switch (*c) {
			case '`':
			case '(':
			case ')':
			case '[':
			case ']':
			case ';':
				complexity++;
				break;
			}
		}

		if (start == startlv1 || start == startlv2) {
			start = startlv0;
		}

		column += strlen(start) * 8 + strlen(word);
		if (column > parser->settings.target_command_format_wrapcol ||
		    strcmp(word, "") == 0 || target_command_should_wrap(word) ||
		    (command && word_index > command_i && target_command_wrap_after_each_token(command))) {
			if (word_index + 1 < array_len(commands)) {
				char *next = array_get(commands, word_index + 1);
				if (strcmp(next, "") == 0 || target_command_should_wrap(next)) {
					continue;
				}
			}
			start = startlv2;
			column = 16;
			set_add(wraps, (void *)word_index);
		}
	}

	if (!(parser->settings.behavior & PARSER_FORMAT_TARGET_COMMANDS) ||
	    complexity > parser->settings.target_command_format_threshold) {
		struct Token *t = array_get(tokens, 0);
		if (!set_contains(parser->edited, t)) {
			parser_output_print_rawlines(parser, token_lines(t));
			return;
		}
	}

	parser_enqueue_output(parser, startlv1);
	int wrapped = 0;
	ARRAY_FOREACH(commands, const char *, word) {
		if (wrapped) {
			parser_enqueue_output(parser, startlv2);
		}
		wrapped = set_contains(wraps, (void *)word_index);

		parser_enqueue_output(parser, word);
		if (wrapped) {
			if (word_index == array_len(tokens) - 1) {
				parser_enqueue_output(parser, endline);
			} else {
				if (strcmp(word, "") != 0) {
					parser_enqueue_output(parser, endword);
				}
				parser_enqueue_output(parser, endnext);
			}
		} else {
			if (word_index == array_len(tokens) - 1) {
				parser_enqueue_output(parser, endline);
			} else {
				parser_enqueue_output(parser, endword);
			}
		}
	}
}

void
parser_output_prepare(struct Parser *parser)
{
	if (!parser->read_finished) {
		parser_read_finish(parser);
	}

	if (parser->error != PARSER_ERROR_OK) {
		return;
	}

	if (parser->settings.behavior & PARSER_OUTPUT_DUMP_TOKENS) {
		parser_output_dump_tokens(parser);
	} else if (parser->settings.behavior & PARSER_OUTPUT_RAWLINES) {
		/* no-op */
	} else if (parser->settings.behavior & PARSER_OUTPUT_EDITED) {
		parser_output_reformatted(parser);
	} else if (parser->settings.behavior & PARSER_OUTPUT_REFORMAT) {
		parser_output_reformatted(parser);
	}

	if (parser->settings.behavior & PARSER_OUTPUT_DIFF) {
		parser_output_diff(parser);
	}
}

static int
matches_opt_use_prefix_helper(char c)
{
	return isupper(c) || islower(c) || isdigit(c) || c == '-' || c == '_';
}

static int
matches_opt_use_prefix(const char *s)
{
	// ^([-_[:upper:][:lower:][:digit:]]+)
	if (!matches_opt_use_prefix_helper(*s)) {
		return 0;
	}
	size_t len = strlen(s);
	size_t i;
	for (i = 1; i < len && matches_opt_use_prefix_helper(s[i]); i++);

	// \+?
	if (s[i] == '+') {
		i++;
	}

	// =
	if (s[i] == '=') {
		return 1;
	}

	return 0;
}

struct Array *
parser_output_sort_opt_use(struct Parser *parser, struct Mempool *pool, struct Array *arr)
{
	if (array_len(arr) == 0) {
		return arr;
	}

	struct Token *t = array_get(arr, 0);
	assert(token_type(t) == VARIABLE_TOKEN);
	int opt_use = 0;
	char *helper = NULL;
	if (is_options_helper(pool, parser, variable_name(token_variable(t)), NULL, &helper, NULL)) {
		if (strcmp(helper, "USE") == 0 || strcmp(helper, "USE_OFF") == 0)  {
			opt_use = 1;
		} else if (strcmp(helper, "VARS") == 0 || strcmp(helper, "VARS_OFF") == 0) {
			opt_use = 0;
		} else {
			return arr;
		}
	} else {
		return arr;
	}

	struct Array *up = mempool_array(pool);
	ARRAY_FOREACH(arr, struct Token *, t) {
		assert(token_type(t) == VARIABLE_TOKEN);
		if (!matches_opt_use_prefix(token_data(t))) {
			array_append(up, t);
			continue;
		}
		char *suffix = strchr(token_data(t), '=');
		if (suffix == NULL ) {
			array_append(up, t);
			continue;
		}
		suffix++;

		char *prefix = str_map(pool, token_data(t), suffix - token_data(t), toupper);
		struct Array *buf = mempool_array(pool);
		if (opt_use) {
			struct Array *values = mempool_array(pool);
			char *var = str_printf(pool, "USE_%s", prefix);
			array_append(buf, prefix);
			char *s, *token;
			s = str_dup(pool, suffix);
			while ((token = strsep(&s, ",")) != NULL) {
				struct Variable *v = mempool_add(pool, variable_new(var), variable_free);
				struct Token *t2 = token_new_variable_token(token_lines(t), v, token);
				if (t2 != NULL) {
					mempool_add(pool, t2, token_free);
					array_append(values, t2);
				}
			}

			array_sort(values, compare_tokens, parser);
			ARRAY_FOREACH(values, struct Token *, t2) {
				array_append(buf, token_data(t2));
				if (t2_index < array_len(values) - 1) {
					array_append(buf, ",");
				}
			}
		} else {
			array_append(buf, prefix);
			array_append(buf, suffix);
		}

		struct Token *t2 = token_clone(t, str_join(pool, buf, ""));
		parser_mark_for_gc(parser, t2);
		array_append(up, t2);
	}
	return up;
}

struct Array *
parser_output_reformatted_helper(struct Parser *parser, struct Mempool *pool, struct Array *arr)
{
	if (array_len(arr) == 0) {
		return arr;
	}
	struct Token *t0 = array_get(arr, 0);

	/* Leave variables unformatted that have $\ in them. */
	if ((array_len(arr) == 1 && strstr(token_data(t0), "$\001") != NULL) ||
	    (leave_unformatted(parser, token_variable(t0)) &&
	     !set_contains(parser->edited, t0))) {
		parser_output_print_rawlines(parser, token_lines(t0));
		goto cleanup;
	}

	if (!set_contains(parser->edited, t0) &&
	    (parser->settings.behavior & PARSER_OUTPUT_EDITED)) {
		parser_output_print_rawlines(parser, token_lines(t0));
		goto cleanup;
	}

	if (!(parser->settings.behavior & PARSER_UNSORTED_VARIABLES) &&
	    should_sort(parser, token_variable(t0))) {
		arr = parser_output_sort_opt_use(parser, pool, arr);
		array_sort(arr, compare_tokens, parser);
	}

	t0 = array_get(arr, 0);
	if (print_as_newlines(parser, token_variable(t0))) {
		print_newline_array(parser, pool, arr);
	} else {
		print_token_array(parser, pool, arr);
	}

cleanup:
	array_truncate(arr);
	return arr;
}

static void
parser_output_edited_insert_empty(struct Parser *parser, struct Token *prev)
{
	switch (token_type(prev)) {
	case CONDITIONAL_END: {
		enum ConditionalType type = conditional_type(token_conditional(prev));
		switch (type) {
		case COND_ENDFOR:
		case COND_ENDIF:
		case COND_ERROR:
		case COND_EXPORT_ENV:
		case COND_EXPORT_LITERAL:
		case COND_EXPORT:
		case COND_INCLUDE_POSIX:
		case COND_INCLUDE:
		case COND_SINCLUDE:
		case COND_UNDEF:
		case COND_UNEXPORT_ENV:
		case COND_UNEXPORT:
		case COND_WARNING:
			parser_enqueue_output(parser, "\n");
			break;
		default:
			break;
		}
		break;
	} case COMMENT:
	case TARGET_COMMAND_END:
	case TARGET_END:
	case TARGET_START:
		break;
	default:
		parser_enqueue_output(parser, "\n");
		break;
	}
}

static int
category_makefile_compare(const void *ap, const void *bp, void *userdata)
{
	struct Token *a = *(struct Token**)ap;
	struct Token *b = *(struct Token**)bp;
	return strcmp(token_data(a), token_data(b));
}

static void
parser_output_category_makefile_reformatted(struct Parser *parser)
{
	// Category Makefiles have a strict layout so we can simply
	// dump everything out but also verify everything when doing so.
	// We do not support editing/formatting the top level Makefile.
	const char *indent = "    ";
	SCOPE_MEMPOOL(pool);
	struct Array *tokens = mempool_array(pool);
	ARRAY_FOREACH(parser->tokens, struct Token *, t) {
		switch (token_type(t)) {
		case CONDITIONAL_END: {
			size_t tokens_len = array_len(tokens);
			ARRAY_FOREACH(tokens, struct Token *, o) {
				parser_enqueue_output(parser, token_data(o));
				if ((o_index + 1) < tokens_len) {
					parser_enqueue_output(parser, " ");
				}
			}
			parser_enqueue_output(parser, "\n");
			break;
		} case CONDITIONAL_START:
			if (conditional_type(token_conditional(t)) != COND_INCLUDE) {
				parser_set_error(parser, PARSER_ERROR_UNSPECIFIED,
						 str_printf(pool, "unsupported conditional in category Makefile: %s",
							conditional_tostring(token_conditional(t), pool)));
				return;
			}
			array_truncate(tokens);
			break;
		case CONDITIONAL_TOKEN:
			array_append(tokens, t);
			break;
		case VARIABLE_START:
			array_truncate(tokens);
			break;
		case VARIABLE_END: {
			const char *varname = variable_name(token_variable(t));
			if (strcmp(varname, "COMMENT") == 0) {
				parser_enqueue_output(parser, indent);
				parser_enqueue_output(parser, varname);
				parser_enqueue_output(parser, " = ");
				size_t tokens_len = array_len(tokens);
				ARRAY_FOREACH(tokens, struct Token *, o) {
					parser_enqueue_output(parser, token_data(o));
					if ((o_index + 1) < tokens_len) {
						parser_enqueue_output(parser, " ");
					}
				}
				parser_enqueue_output(parser, "\n");
			} else if (strcmp(varname, "SUBDIR") == 0) {
				array_sort(tokens, category_makefile_compare, NULL);
				ARRAY_FOREACH(tokens, struct Token *, o) {
					parser_enqueue_output(parser, indent);
					parser_enqueue_output(parser, varname);
					parser_enqueue_output(parser, " += ");
					parser_enqueue_output(parser, token_data(o));
					parser_enqueue_output(parser, "\n");
				}
			} else {
				parser_set_error(parser, PARSER_ERROR_UNSPECIFIED,
						 str_printf(pool, "unsupported variable in category Makefile: %s", varname));
				return;
			}
			break;
		} case VARIABLE_TOKEN: {
			array_append(tokens, t);
			break;
		} case COMMENT:
			parser_enqueue_output(parser, token_data(t));
			parser_enqueue_output(parser, "\n");
			break;
		default:
			parser_set_error(parser, PARSER_ERROR_UNHANDLED_TOKEN_TYPE,
					 str_printf(pool, "%s", token_type_tostring(token_type(t))));
			return;
		}
	}
}

void
parser_output_reformatted(struct Parser *parser)
{
	SCOPE_MEMPOOL(pool);

	parser_find_goalcols(parser);
	if (parser->error != PARSER_ERROR_OK) {
		return;
	}

	if (parser_is_category_makefile(parser)) {
		parser_output_category_makefile_reformatted(parser);
		return;
	}

	struct Array *target_arr = mempool_array(pool);
	struct Array *variable_arr = mempool_array(pool);
	struct Token *prev = NULL;
	ARRAY_FOREACH(parser->tokens, struct Token *, o) {
		int edited = set_contains(parser->edited, o);
		switch (token_type(o)) {
		case CONDITIONAL_END:
			if (edited) {
				parser_enqueue_output(parser, "\n");
			} else {
				parser_output_print_rawlines(parser, token_lines(o));
			}
			break;
		case CONDITIONAL_START:
			if (edited && prev) {
				parser_output_edited_insert_empty(parser, prev);
			}
			break;
		case CONDITIONAL_TOKEN:
			if (edited) {
				parser_enqueue_output(parser, token_data(o));
				parser_enqueue_output(parser, " ");
			}
			break;
		case VARIABLE_END:
			if (array_len(variable_arr) == 0) {
				parser_enqueue_output(parser, variable_tostring(token_variable(o), pool));
				parser_enqueue_output(parser, "\n");
				array_truncate(variable_arr);
			} else {
				variable_arr = parser_output_reformatted_helper(parser, pool, variable_arr);
			}
			break;
		case VARIABLE_START:
			array_truncate(variable_arr);
			break;
		case VARIABLE_TOKEN:
			array_append(variable_arr, o);
			break;
		case TARGET_COMMAND_END:
			parser_output_print_target_command(parser, target_arr);
			array_truncate(target_arr);
			break;
		case TARGET_COMMAND_START:
			array_truncate(target_arr);
			break;
		case TARGET_COMMAND_TOKEN:
			array_append(target_arr, o);
			break;
		case TARGET_END:
			break;
		case COMMENT:
			variable_arr = parser_output_reformatted_helper(parser, pool, variable_arr);
			if (edited) {
				parser_enqueue_output(parser, token_data(o));
				parser_enqueue_output(parser, "\n");
			} else {
				parser_output_print_rawlines(parser, token_lines(o));
			}
			break;
		case TARGET_START:
			variable_arr = parser_output_reformatted_helper(parser, pool, variable_arr);
			if (edited) {
				if (prev) {
					parser_output_edited_insert_empty(parser, prev);
				}
				parser_enqueue_output(parser, token_data(o));
				parser_enqueue_output(parser, "\n");
			} else {
				parser_output_print_rawlines(parser, token_lines(o));
			}
			break;
		default:
			parser->error = PARSER_ERROR_UNHANDLED_TOKEN_TYPE;
			return;
		}
		if (parser->error != PARSER_ERROR_OK) {
			return;
		}
		prev = o;
	}
	if (array_len(target_arr) > 0) {
		print_token_array(parser, pool, target_arr);
		array_truncate(target_arr);
	}
	parser_output_reformatted_helper(parser, pool, variable_arr);
}

void
parser_output_diff(struct Parser *parser)
{
	SCOPE_MEMPOOL(pool);

	if (parser->error != PARSER_ERROR_OK) {
		return;
	}

	// Normalize result: one element = one line like parser->rawlines
	struct Array *lines = mempool_array(pool);
	char *lines_buf = str_join(pool, parser->result, "");
	char *token;
	while ((token = strsep(&lines_buf, "\n")) != NULL) {
		array_append(lines, token);
	}
	array_pop(lines);

	struct diff *p = array_diff(parser->rawlines, lines, pool, str_compare, NULL);
	if (p == NULL) {
		parser_set_error(parser, PARSER_ERROR_UNSPECIFIED,
				 str_printf(pool, "could not create diff"));
		return;
	}

	ARRAY_FOREACH(parser->result, char *, line) {
		free(line);
	}
	array_truncate(parser->result);

	if (p->editdist > 0) {
		const char *filename = parser->settings.filename;
		if (filename == NULL) {
			filename = "Makefile";
		}
		const char *color_add = ANSI_COLOR_GREEN;
		const char *color_delete = ANSI_COLOR_RED;
		const char *color_reset = ANSI_COLOR_RESET;
		int nocolor = parser->settings.behavior & PARSER_OUTPUT_NO_COLOR;
		if (nocolor) {
			color_add = "";
			color_delete = "";
			color_reset = "";
		}
		char *buf = str_printf(NULL, "%s--- %s\n%s+++ %s%s\n", color_delete, filename, color_add, filename, color_reset);
		array_append(parser->result, buf);
		array_append(parser->result, diff_to_patch(p, NULL, NULL, NULL, parser->settings.diff_context, !nocolor));
		parser->error = PARSER_ERROR_DIFFERENCES_FOUND;
	}
}

void
parser_output_dump_tokens(struct Parser *parser)
{
	SCOPE_MEMPOOL(pool);

	if (parser->error != PARSER_ERROR_OK) {
		return;
	}

	size_t maxvarlen = 0;
	ARRAY_FOREACH(parser->tokens, struct Token *, o) {
		if (token_type(o) == VARIABLE_START && token_variable(o)) {
			maxvarlen = MAX(maxvarlen, strlen(variable_tostring(token_variable(o), pool)));
		}
	}

	struct Array *vars = mempool_array(pool);
	ARRAY_FOREACH(parser->tokens, struct Token *, t) {
		const char *type;
		switch (token_type(t)) {
		case VARIABLE_END:
			type = "variable-end";
			break;
		case VARIABLE_START:
			type = "variable-start";
			break;
		case VARIABLE_TOKEN:
			type = "variable-token";
			break;
		case TARGET_COMMAND_END:
			type = "target-command-end";
			break;
		case TARGET_COMMAND_START:
			type = "target-command-start";
			break;
		case TARGET_COMMAND_TOKEN:
			type = "target-command-token";
			break;
		case TARGET_END:
			type = "target-end";
			break;
		case TARGET_START:
			type = "target-start";
			break;
		case CONDITIONAL_END:
			type = "conditional-end";
			break;
		case CONDITIONAL_START:
			type = "conditional-start";
			break;
		case CONDITIONAL_TOKEN:
			type = "conditional-token";
			break;
		case COMMENT:
			type = "comment";
			break;
		default:
			parser->error = PARSER_ERROR_UNHANDLED_TOKEN_TYPE;
			return;
		}
		if (token_variable(t) &&
		    (token_type(t) == VARIABLE_TOKEN ||
		     token_type(t) == VARIABLE_START ||
		     token_type(t) == VARIABLE_END)) {
			array_append(vars, variable_tostring(token_variable(t), pool));
		} else if (token_conditional(t) &&
			   (token_type(t) == CONDITIONAL_END ||
			    token_type(t) == CONDITIONAL_START ||
			    token_type(t) == CONDITIONAL_TOKEN)) {
			array_append(vars, conditional_tostring(token_conditional(t), pool));
		} else if (token_target(t) && token_type(t) == TARGET_START) {
			ARRAY_FOREACH(target_names(token_target(t)), char *, name) {
				array_append(vars, str_dup(pool, name));
			}
			ARRAY_FOREACH(target_dependencies(token_target(t)), char *, dep) {
				array_append(vars, str_printf(pool, "->%s", dep));
			}
		} else if (token_target(t) &&
			   (token_type(t) == TARGET_COMMAND_END ||
			    token_type(t) == TARGET_COMMAND_START ||
			    token_type(t) == TARGET_COMMAND_TOKEN ||
			    token_type(t) == TARGET_START ||
			    token_type(t) == TARGET_END)) {
			array_append(vars, str_dup(pool, "-"));
		} else {
			array_append(vars, str_dup(pool, "-"));
		}

		ARRAY_FOREACH(vars, char *, var) {
			ssize_t len = maxvarlen - strlen(var);
			char *range = range_tostring(pool, token_lines(t));
			char *tokentype;
			if (array_len(vars) > 1) {
				tokentype = str_printf(pool, "%s#%zu", type, var_index + 1);
			} else {
				tokentype = str_dup(pool, type);
			}
			parser_enqueue_output(parser, str_printf(pool, "%-20s %8s ", tokentype, range));
			parser_enqueue_output(parser, var);

			if (len > 0) {
				parser_enqueue_output(parser, str_repeat(pool, " ", len));
			}
			parser_enqueue_output(parser, " ");

			if (token_data(t) &&
			    (token_type(t) != CONDITIONAL_START &&
			     token_type(t) != CONDITIONAL_END)) {
				parser_enqueue_output(parser, token_data(t));
			} else {
				parser_enqueue_output(parser, "-");
			}
			parser_enqueue_output(parser, "\n");
		}
		array_truncate(vars);
	}

	parser->error = PARSER_ERROR_OK;
}

void
parser_read_line(struct Parser *parser, char *line)
{
	if (parser->error != PARSER_ERROR_OK) {
		return;
	}

	size_t linelen = strlen(line);

	array_append(parser->rawlines, str_dup(NULL, line));

	parser->lines.end++;

	int will_continue = linelen > 0 && line[linelen - 1] == '\\' && (linelen == 1 || line[linelen - 2] != '\\');
	if (will_continue) {
 		if (linelen > 2 && line[linelen - 2] == '$' && line[linelen - 3] != '$') {
			/* Hack to "handle" things like $\ in variable values */
			line[linelen - 1] = 1;
		} else if (linelen > 1 && !isspace(line[linelen - 2])) {
			/* "Handle" lines that end without a preceding space before '\'. */
			line[linelen - 1] = ' ';
		} else {
			line[linelen - 1] = 0;
		}
	}

	if (parser->continued) {
		/* Replace all whitespace at the beginning with a single
		 * space which is what make seems to do.
		 */
		for (;isblank(*line); line++);
		if (strlen(line) < 1) {
			if (strlcat(parser->inbuf, " ", INBUF_SIZE) >= INBUF_SIZE) {
				parser->error = PARSER_ERROR_BUFFER_TOO_SMALL;
				return;
			}
		}
	}

	if (strlcat(parser->inbuf, line, INBUF_SIZE) >= INBUF_SIZE) {
		parser->error = PARSER_ERROR_BUFFER_TOO_SMALL;
		return;
	}

	if (!will_continue) {
		parser_read_internal(parser);
		if (parser->error != PARSER_ERROR_OK) {
			return;
		}
		parser->lines.start = parser->lines.end;
		memset(parser->inbuf, 0, INBUF_SIZE);
	}

	parser->continued = will_continue;
}

enum ParserError
parser_read_from_file(struct Parser *parser, FILE *fp)
{
	if (parser->error != PARSER_ERROR_OK) {
		return parser->error;
	}

	LINE_FOREACH(fp, line) {
		parser_read_line(parser, line);
		if (parser->error != PARSER_ERROR_OK) {
			return parser->error;
		}
	}

	return PARSER_ERROR_OK;
}

void
parser_read_internal(struct Parser *parser)
{
	SCOPE_MEMPOOL(pool);

	if (parser->error != PARSER_ERROR_OK) {
		return;
	}

	char *buf = str_trimr(pool, parser->inbuf);
	size_t pos;

	pos = consume_comment(buf);
	if (pos > 0) {
		parser_append_token(parser, COMMENT, buf);
		goto next;
	} else if (is_empty_line(buf)) {
		parser_append_token(parser, COMMENT, buf);
		goto next;
	}

	if (parser->in_target) {
		pos = consume_conditional(buf);
		if (pos > 0) {
			free(parser->condname);
			char *tmp = str_ndup(NULL, buf, pos);
			parser->condname = str_trimr(NULL, tmp);
			free(tmp);

			parser_append_token(parser, CONDITIONAL_START, parser->condname);
			parser_append_token(parser, CONDITIONAL_TOKEN, parser->condname);
			parser_tokenize(parser, buf, CONDITIONAL_TOKEN, pos);
			parser_append_token(parser, CONDITIONAL_END, parser->condname);
			goto next;
		}
		if (consume_var(buf) == 0 && consume_target(buf) == 0 &&
		    *buf != 0 && *buf == '\t') {
			parser_append_token(parser, TARGET_COMMAND_START, NULL);
			parser_tokenize(parser, buf, TARGET_COMMAND_TOKEN, 0);
			parser_append_token(parser, TARGET_COMMAND_END, NULL);
			goto next;
		}
		if (consume_var(buf) > 0) {
			goto var;
		}
		parser_append_token(parser, TARGET_END, NULL);
		parser->in_target = 0;
	}

	pos = consume_conditional(buf);
	if (pos > 0) {
		free(parser->condname);
		char *tmp = str_ndup(NULL, buf, pos);
		parser->condname = str_trimr(NULL, tmp);
		free(tmp);

		parser_append_token(parser, CONDITIONAL_START, parser->condname);
		parser_append_token(parser, CONDITIONAL_TOKEN, parser->condname);
		parser_tokenize(parser, buf, CONDITIONAL_TOKEN, pos);
		parser_append_token(parser, CONDITIONAL_END, parser->condname);
		goto next;
	}

	pos = consume_target(buf);
	if (pos > 0) {
		parser->in_target = 1;
		free(parser->targetname);
		parser->targetname = str_dup(NULL, buf);
		parser_append_token(parser, TARGET_START, buf);
		goto next;
	}

var:
	pos = consume_var(buf);
	if (pos != 0) {
		if (pos > strlen(buf)) {
			parser->error = PARSER_ERROR_BUFFER_TOO_SMALL;
			goto next;
		}
		char *tmp = str_ndup(NULL, buf, pos);
		parser->varname = str_trim(NULL, tmp);
		free(tmp);
		parser_append_token(parser, VARIABLE_START, NULL);
	}
	parser_tokenize(parser, buf, VARIABLE_TOKEN, pos);
	if (parser->varname == NULL) {
		parser->error = PARSER_ERROR_UNSPECIFIED;
	}
next:
	if (parser->varname) {
		parser_append_token(parser, VARIABLE_END, NULL);
		free(parser->varname);
		parser->varname = NULL;
	}
}

enum ParserError
parser_read_finish(struct Parser *parser)
{
	if (parser->error != PARSER_ERROR_OK) {
		return parser->error;
	}

	for (size_t i = 0; i <= PARSER_METADATA_USES; i++) {
		parser->metadata_valid[i] = 0;
	}

	if (!parser->continued) {
		parser->lines.end++;
	}

	if (strlen(parser->inbuf) > 0) {
		parser_read_internal(parser);
		if (parser->error != PARSER_ERROR_OK) {
			return parser->error;
		}
	}

	if (parser->in_target) {
		parser_append_token(parser, TARGET_END, NULL);
	}

	// Set it now to avoid recursion in parser_edit()
	parser->read_finished = 1;

	if (parser->settings.behavior & PARSER_SANITIZE_COMMENTS &&
	    PARSER_ERROR_OK != parser_edit(parser, NULL, refactor_sanitize_comments, NULL)) {
		return parser->error;
	}

	if (PARSER_ERROR_OK != parser_edit(parser, NULL, refactor_sanitize_cmake_args, NULL)) {
		return parser->error;
	}

	// To properly support editing category Makefiles always
	// collapse all the SUBDIR into one assignment regardless
	// of settings.
	if ((parser_is_category_makefile(parser) ||
	     parser->settings.behavior & PARSER_COLLAPSE_ADJACENT_VARIABLES) &&
	    PARSER_ERROR_OK != parser_edit(parser, NULL, refactor_collapse_adjacent_variables, NULL)) {
		return parser->error;
	}

	if (parser->settings.behavior & PARSER_SANITIZE_APPEND &&
	    PARSER_ERROR_OK != parser_edit(parser, NULL, refactor_sanitize_append_modifier, NULL)) {
		return parser->error;
	}

	if (parser->settings.behavior & PARSER_DEDUP_TOKENS &&
	    PARSER_ERROR_OK != parser_edit(parser, NULL, refactor_dedup_tokens, NULL)) {
		return parser->error;
	}

	if (PARSER_ERROR_OK != parser_edit(parser, NULL, refactor_remove_consecutive_empty_lines, NULL)) {
		return parser->error;
	}

	return parser->error;
}

enum ParserError
parser_output_write_to_file(struct Parser *parser, FILE *fp)
{
	SCOPE_MEMPOOL(pool);

	parser_output_prepare(parser);
	if (fp == NULL ||
	    (parser->error != PARSER_ERROR_OK &&
	     parser->error != PARSER_ERROR_DIFFERENCES_FOUND)) {
		return parser->error;
	}

	int fd = fileno(fp);
	if (parser->settings.behavior & PARSER_OUTPUT_INPLACE) {
		if (lseek(fd, 0, SEEK_SET) < 0) {
			parser_set_error(parser, PARSER_ERROR_IO,
					 str_printf(pool, "lseek: %s", strerror(errno)));
			return parser->error;
		}
		if (ftruncate(fd, 0) < 0) {
			parser_set_error(parser, PARSER_ERROR_IO,
					 str_printf(pool, "ftruncate: %s", strerror(errno)));
			return parser->error;
		}
	}

	size_t len = array_len(parser->result);
	if (len == 0) {
		return parser->error;
	}

	size_t iov_len = MIN(len, IOV_MAX);
	struct iovec *iov = mempool_take(pool, xrecallocarray(NULL, 0, iov_len, sizeof(struct iovec)));
	for (size_t i = 0; i < len;) {
		size_t j = 0;
		for (; i < len && j < iov_len; j++) {
			char *s = array_get(parser->result, i++);
			iov[j].iov_base = s;
			iov[j].iov_len = strlen(s);
		}
		if (writev(fd, iov, j) < 0) {
			parser_set_error(parser, PARSER_ERROR_IO,
					 str_printf(pool, "writev: %s", strerror(errno)));
			return parser->error;
		}
	}

	/* Collect garbage */
	ARRAY_FOREACH(parser->result, char *, line) {
		free(line);
	}
	array_truncate(parser->result);

	return parser->error;
}

enum ParserError
parser_read_from_buffer(struct Parser *parser, const char *input, size_t len)
{
	if (parser->error != PARSER_ERROR_OK) {
		return parser->error;
	}

	char *buf, *bufp, *line;
	buf = bufp = str_ndup(NULL, input, len);
	while ((line = strsep(&bufp, "\n")) != NULL) {
		parser_read_line(parser, line);
		if (parser->error != PARSER_ERROR_OK) {
			break;
		}
	}
	free(buf);

	return parser->error;
}

void
parser_mark_for_gc(struct Parser *parser, struct Token *t)
{
	mempool_add(parser->tokengc, t, token_free);
}

void
parser_mark_edited(struct Parser *parser, struct Token *t)
{
	set_add(parser->edited, t);
}

enum ParserError
parser_edit(struct Parser *parser, struct Mempool *extpool, ParserEditFn f, void *userdata)
{
	SCOPE_MEMPOOL(pool);

	if (!parser->read_finished) {
		parser_read_finish(parser);
	}

	if (parser->error != PARSER_ERROR_OK) {
		return parser->error;
	}

	struct Array *tokens = f(parser, parser->tokens, extpool, userdata);
	if (tokens && tokens != parser->tokens) {
		array_free(parser->tokens);
		parser->tokens = tokens;
	}

	if (parser->error != PARSER_ERROR_OK) {
		parser_set_error(parser, PARSER_ERROR_EDIT_FAILED, parser_error_tostring(parser, pool));
	}

	return parser->error;
}

struct ParserSettings parser_settings(struct Parser *parser)
{
	return parser->settings;
}

static void
parser_meta_values_helper(struct Set *set, const char *var, char *value)
{
	if (strcmp(var, "USES") == 0) {
		char *buf = strchr(value, ':');
		if (buf != NULL) {
			char *val = str_ndup(NULL, value, buf - value);
			if (set_contains(set, val)) {
				free(val);
			} else {
				set_add(set, val);
			}
			return;
		}
	}

	if (!set_contains(set, value)) {
		set_add(set, str_dup(NULL, value));
	}
}

void
parser_meta_values(struct Parser *parser, const char *var, struct Set *set)
{
	SCOPE_MEMPOOL(pool);

	struct Array *tmp = NULL;
	if (parser_lookup_variable(parser, var, PARSER_LOOKUP_DEFAULT, pool, &tmp, NULL)) {
		ARRAY_FOREACH(tmp, char *, value) {
			parser_meta_values_helper(set, var, value);
		}
	}

	struct Set *options = parser_metadata(parser, PARSER_METADATA_OPTIONS);
	SET_FOREACH(options, const char *, opt) {
		char *buf = str_printf(pool, "%s_VARS", opt);
		if (parser_lookup_variable(parser, buf, PARSER_LOOKUP_DEFAULT, pool, &tmp, NULL)) {
			ARRAY_FOREACH(tmp, char *, value) {
				char *buf = str_printf(pool, "%s+=", var);
				if (str_startswith(value, buf)) {
					value += strlen(buf);
				} else {
					buf = str_printf(pool, "%s=", var);
					if (str_startswith(value, buf)) {
						value += strlen(buf);
					} else {
						continue;
					}
				}
				parser_meta_values_helper(set, var, value);
			}
		}

		buf = str_printf(pool, "%s_VARS_OFF", opt);
		if (parser_lookup_variable(parser, buf, PARSER_LOOKUP_DEFAULT, pool, &tmp, NULL)) {
			ARRAY_FOREACH(tmp, char *, value) {
				char *buf = str_printf(pool, "%s+=", var);
				if (str_startswith(value, buf)) {
					value += strlen(buf);
				} else {
					buf = str_printf(pool, "%s=", var);
					if (str_startswith(value, buf)) {
						value += strlen(buf);
					} else {
						continue;
					}
				}
				parser_meta_values_helper(set, var, value);
			}
		}

#if PORTFMT_SUBPACKAGES
		if (strcmp(var, "USES") == 0 || strcmp(var, "SUBPACKAGES") == 0) {
#else
		if (strcmp(var, "USES") == 0) {
#endif
			buf = str_printf(pool, "%s_%s", opt, var);
			if (parser_lookup_variable(parser, buf, PARSER_LOOKUP_DEFAULT, pool, &tmp, NULL)) {
				ARRAY_FOREACH(tmp, char *, value) {
					parser_meta_values_helper(set, var, value);
				}
			}

			buf = str_printf(pool, "%s_%s_OFF", opt, var);
			if (parser_lookup_variable(parser, buf, PARSER_LOOKUP_DEFAULT, pool, &tmp, NULL)) {
				ARRAY_FOREACH(tmp, char *, value) {
					parser_meta_values_helper(set, var, value);
				}
			}
		}
	}
}

static void
parser_port_options_add_from_group(struct Parser *parser, const char *groupname)
{
	SCOPE_MEMPOOL(pool);

	struct Array *optmulti = NULL;
	if (parser_lookup_variable(parser, groupname, PARSER_LOOKUP_DEFAULT, pool, &optmulti, NULL)) {
		ARRAY_FOREACH(optmulti, char *, optgroupname) {
			if (!set_contains(parser->metadata[PARSER_METADATA_OPTION_GROUPS], optgroupname)) {
				set_add(parser->metadata[PARSER_METADATA_OPTION_GROUPS], str_dup(NULL, optgroupname));
			}
			char *optgroupvar = str_printf(pool, "%s_%s", groupname, optgroupname);
			struct Array *opts = NULL;
			if (parser_lookup_variable(parser, optgroupvar, PARSER_LOOKUP_DEFAULT, pool, &opts, NULL)) {
				ARRAY_FOREACH(opts, char *, opt) {
					if (!set_contains(parser->metadata[PARSER_METADATA_OPTIONS], opt)) {
						set_add(parser->metadata[PARSER_METADATA_OPTIONS], str_dup(NULL, opt));
					}
				}
			}
		}
	}
}

static void
parser_port_options_add_from_var(struct Parser *parser, const char *var)
{
	SCOPE_MEMPOOL(pool);

	struct Array *optdefine = NULL;
	if (parser_lookup_variable(parser, var, PARSER_LOOKUP_DEFAULT, pool, &optdefine, NULL)) {
		ARRAY_FOREACH(optdefine, char *, opt) {
			if (!set_contains(parser->metadata[PARSER_METADATA_OPTIONS], opt)) {
				set_add(parser->metadata[PARSER_METADATA_OPTIONS], str_dup(NULL, opt));
			}
		}
	}
}

void
parser_metadata_port_options(struct Parser *parser)
{
	SCOPE_MEMPOOL(pool);

	if (parser->metadata_valid[PARSER_METADATA_OPTIONS]) {
		return;
	}

	parser->metadata_valid[PARSER_METADATA_OPTION_DESCRIPTIONS] = 1;
	parser->metadata_valid[PARSER_METADATA_OPTION_GROUPS] = 1;
	parser->metadata_valid[PARSER_METADATA_OPTIONS] = 1;

#define FOR_EACH_ARCH(f, var) \
	for (size_t i = 0; i < nitems(known_architectures_); i++) { \
		char *buf = str_printf(pool, "%s_%s", var, known_architectures_[i]); \
		f(parser, buf); \
	}

	parser_port_options_add_from_var(parser, "OPTIONS_DEFINE");
	FOR_EACH_ARCH(parser_port_options_add_from_var, "OPTIONS_DEFINE");

	parser_port_options_add_from_group(parser, "OPTIONS_GROUP");
	FOR_EACH_ARCH(parser_port_options_add_from_group, "OPTIONS_GROUP");

	parser_port_options_add_from_group(parser, "OPTIONS_MULTI");
	FOR_EACH_ARCH(parser_port_options_add_from_group, "OPTIONS_MULTI");

	parser_port_options_add_from_group(parser, "OPTIONS_RADIO");
	FOR_EACH_ARCH(parser_port_options_add_from_group, "OPTIONS_RADIO");

	parser_port_options_add_from_group(parser, "OPTIONS_SINGLE");
	FOR_EACH_ARCH(parser_port_options_add_from_group, "OPTIONS_SINGLE");

#undef FOR_EACH_ARCH

	struct Set *opts[] = { parser->metadata[PARSER_METADATA_OPTIONS], parser->metadata[PARSER_METADATA_OPTION_GROUPS] };
	for (size_t i = 0; i < nitems(opts); i++) {
		if (opts[i]) SET_FOREACH(opts[i], const char *, opt) {
			char *var = str_printf(pool, "%s_DESC", opt);
			if (!map_contains(parser->metadata[PARSER_METADATA_OPTION_DESCRIPTIONS], var)) {
				char *desc;
				if (parser_lookup_variable_str(parser, var, PARSER_LOOKUP_FIRST, pool, &desc, NULL)) {
					map_add(parser->metadata[PARSER_METADATA_OPTION_DESCRIPTIONS], str_dup(NULL, var), str_dup(NULL, desc));
				}
			}
		}
	}
}

void
parser_metadata_alloc(struct Parser *parser)
{
	for (enum ParserMetadata meta = 0; meta <= PARSER_METADATA_USES; meta++) {
		switch (meta) {
		case PARSER_METADATA_OPTION_DESCRIPTIONS:
			parser->metadata[meta] = map_new(str_compare, NULL, free, free);
			break;
		case PARSER_METADATA_MASTERDIR:
			parser->metadata[meta] = NULL;
			break;
		default:
			parser->metadata[meta] = set_new(str_compare, NULL, free);
			break;
		}
	}
}

void
parser_metadata_free(struct Parser *parser)
{
	for (enum ParserMetadata i = 0; i <= PARSER_METADATA_USES; i++) {
		switch (i) {
		case PARSER_METADATA_MASTERDIR:
			free(parser->metadata[i]);
			break;
		case PARSER_METADATA_OPTION_DESCRIPTIONS:
			map_free(parser->metadata[i]);
			break;
		default:
			set_free(parser->metadata[i]);
			break;
		}
		parser->metadata[i] = NULL;
	}
}

void *
parser_metadata(struct Parser *parser, enum ParserMetadata meta)
{
	SCOPE_MEMPOOL(pool);

	if (!parser->metadata_valid[meta]) {
		switch (meta) {
		case PARSER_METADATA_CABAL_EXECUTABLES: {
			struct Set *uses = parser_metadata(parser, PARSER_METADATA_USES);
			if (set_contains(uses, "cabal")) {
				parser_meta_values(parser, "EXECUTABLES", parser->metadata[PARSER_METADATA_CABAL_EXECUTABLES]);
				if (set_len(parser->metadata[PARSER_METADATA_CABAL_EXECUTABLES]) == 0) {
					char *portname;
					if (parser_lookup_variable_str(parser, "PORTNAME", PARSER_LOOKUP_FIRST, pool, &portname, NULL)) {
						if (!set_contains(parser->metadata[PARSER_METADATA_CABAL_EXECUTABLES], portname)) {
							set_add(parser->metadata[PARSER_METADATA_CABAL_EXECUTABLES], str_dup(NULL, portname));
						}
					}
				}
			}
			break;
		} case PARSER_METADATA_FLAVORS: {
			parser_meta_values(parser, "FLAVORS", parser->metadata[PARSER_METADATA_FLAVORS]);
			struct Set *uses = parser_metadata(parser, PARSER_METADATA_USES);
			// XXX: Does not take into account USE_PYTHON=noflavors etc.
			for (size_t i = 0; i < nitems(static_flavors_); i++) {
				if (set_contains(uses, (void*)static_flavors_[i].uses) &&
				    !set_contains(parser->metadata[PARSER_METADATA_FLAVORS], (void*)static_flavors_[i].flavor)) {
					set_add(parser->metadata[PARSER_METADATA_FLAVORS], str_dup(NULL, static_flavors_[i].flavor));
				}
			}
			break;
		} case PARSER_METADATA_LICENSES:
			parser_meta_values(parser, "LICENSE", parser->metadata[PARSER_METADATA_LICENSES]);
			break;
		case PARSER_METADATA_MASTERDIR: {
			struct Array *tokens = NULL;
			if (parser_lookup_variable(parser, "MASTERDIR", PARSER_LOOKUP_FIRST, pool, &tokens, NULL)) {
				free(parser->metadata[meta]);
				parser->metadata[meta] = str_join(NULL, tokens, " ");
			}
			break;
		} case PARSER_METADATA_SHEBANG_LANGS:
			parser_meta_values(parser, "SHEBANG_LANG", parser->metadata[PARSER_METADATA_SHEBANG_LANGS]);
			break;
		case PARSER_METADATA_OPTION_DESCRIPTIONS:
		case PARSER_METADATA_OPTION_GROUPS:
		case PARSER_METADATA_OPTIONS:
			parser_metadata_port_options(parser);
			break;
		case PARSER_METADATA_POST_PLIST_TARGETS:
			parser_meta_values(parser, "POST_PLIST", parser->metadata[PARSER_METADATA_POST_PLIST_TARGETS]);
			break;
#if PORTFMT_SUBPACKAGES
		case PARSER_METADATA_SUBPACKAGES:
			if (!set_contains(parser->metadata[PARSER_METADATA_SUBPACKAGES], "main")) {
				// There is always a main subpackage
				set_add(parser->metadata[PARSER_METADATA_SUBPACKAGES], str_dup(NULL, "main"));
			}
			parser_meta_values(parser, "SUBPACKAGES", parser->metadata[PARSER_METADATA_SUBPACKAGES]);
			break;
#endif
		case PARSER_METADATA_USES:
			parser_meta_values(parser, "USES", parser->metadata[PARSER_METADATA_USES]);
			break;
		}
		parser->metadata_valid[meta] = 1;
	}

	return parser->metadata[meta];
}

struct Target *
parser_lookup_target(struct Parser *parser, const char *name, struct Mempool *pool, struct Array **retval)
{
	struct Target *target = NULL;
	struct Array *tokens = mempool_array(pool);
	ARRAY_FOREACH(parser->tokens, struct Token *, t) {
		switch (token_type(t)) {
		case TARGET_START:
			array_truncate(tokens);
			/* fallthrough */
		case TARGET_COMMAND_START:
		case TARGET_COMMAND_TOKEN:
		case TARGET_COMMAND_END:
			ARRAY_FOREACH(target_names(token_target(t)), char *, tgt) {
				if (strcmp(tgt, name) == 0) {
					array_append(tokens, token_data(t));
					break;
				}
			}
			break;
		case TARGET_END:
			ARRAY_FOREACH(target_names(token_target(t)), char *, tgt) {
				if (strcmp(tgt, name) == 0) {
					target = token_target(t);
					goto found;
				}
			}
			break;
		default:
			break;
		}
	}

	if (retval) {
		*retval = NULL;
	}

	return NULL;

found:
	if (retval) {
		*retval = tokens;
	}

	return target;
}

struct Variable *
parser_lookup_variable(struct Parser *parser, const char *name, enum ParserLookupVariableBehavior behavior, struct Mempool *pool, struct Array **retval, struct Array **comment)
{
	struct Variable *var = NULL;
	struct Array *tokens = mempool_array(pool);
	struct Array *comments = mempool_array(pool);
	int skip = 0;
	ARRAY_FOREACH(parser->tokens, struct Token *, t) {
		if ((behavior & PARSER_LOOKUP_IGNORE_VARIABLES_IN_CONDITIIONALS) &&
		    skip_conditional(t, &skip)) {
			continue;
		}
		switch (token_type(t)) {
		case VARIABLE_START:
			if (behavior & PARSER_LOOKUP_FIRST) {
				array_truncate(tokens);
			}
			break;
		case VARIABLE_TOKEN:
			if (strcmp(variable_name(token_variable(t)), name) == 0) {
				if (is_comment(t)) {
					array_append(comments, token_data(t));
				} else {
					array_append(tokens, token_data(t));
				}
			}
			break;
		case VARIABLE_END:
			if (strcmp(variable_name(token_variable(t)), name) == 0) {
				var = token_variable(t);
				if (behavior & PARSER_LOOKUP_FIRST) {
					goto found;
				}
			}
			break;
		default:
			break;
		}
	}

	if (var) {
		goto found;
	}
	if (comment) {
		*comment = NULL;
	}
	if (retval) {
		*retval = NULL;
	}

	return NULL;

found:
	if (comment) {
		*comment = comments;
	}
	if (retval) {
		*retval = tokens;
	}

	return var;
}

struct Variable *
parser_lookup_variable_str(struct Parser *parser, const char *name, enum ParserLookupVariableBehavior behavior, struct Mempool *extpool, char **retval, char **comment)
{
	SCOPE_MEMPOOL(pool);

	struct Array *comments;
	struct Array *tokens;
	struct Variable *var;
	if ((var = parser_lookup_variable(parser, name, behavior, pool, &tokens, &comments)) == NULL) {
		return NULL;
	}

	if (comment) {
		*comment = str_join(extpool, comments, " ");
	}

	if (retval) {
		*retval = str_join(extpool, tokens, " ");
	}

	return var;
}

enum ParserError
parser_merge(struct Parser *parser, struct Parser *subparser, enum ParserMergeBehavior settings)
{
	if (parser_is_category_makefile(parser)) {
		settings &= ~PARSER_MERGE_AFTER_LAST_IN_GROUP;
	}
	struct ParserEdit params = { subparser, NULL, settings };
	enum ParserError error = parser_edit(parser, NULL, edit_merge, &params);

	if (error == PARSER_ERROR_OK &&
	    parser->settings.behavior & PARSER_DEDUP_TOKENS) {
		error = parser_edit(parser, NULL, refactor_dedup_tokens, NULL);
	}

	if (error == PARSER_ERROR_OK) {
		error = parser_edit(parser, NULL, refactor_remove_consecutive_empty_lines, NULL);
	}

	return error;
}
