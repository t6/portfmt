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
#pragma once

enum ParserBehavior {
	PARSER_DEFAULT = 0,
	PARSER_COLLAPSE_ADJACENT_VARIABLES = 1 << 0,
	PARSER_DEDUP_TOKENS = 1 << 1,
	PARSER_FORMAT_TARGET_COMMANDS = 1 << 2,
	PARSER_OUTPUT_DIFF = 1 << 4,
	PARSER_OUTPUT_DUMP_TOKENS = 1 << 5,
	PARSER_OUTPUT_EDITED = 1 << 6,
	PARSER_OUTPUT_INPLACE = 1 << 7,
	PARSER_OUTPUT_NO_COLOR = 1 << 8,
	PARSER_OUTPUT_RAWLINES = 1 << 9,
	PARSER_OUTPUT_REFORMAT = 1 << 10,
	PARSER_SANITIZE_APPEND = 1 << 11,
	PARSER_UNSORTED_VARIABLES = 1 << 12,
	PARSER_ALLOW_FUZZY_MATCHING = 1 << 13,
	PARSER_SANITIZE_COMMENTS = 1 << 14,
	PARSER_ALWAYS_SORT_VARIABLES = 1 << 15,
};

enum ParserMergeBehavior {
	PARSER_MERGE_DEFAULT = 0,
	PARSER_MERGE_COMMENTS = 1 << 0,
	PARSER_MERGE_OPTIONAL_LIKE_ASSIGN = 1 << 2,
	PARSER_MERGE_SHELL_IS_DELETE = 1 << 3,
	PARSER_MERGE_AFTER_LAST_IN_GROUP = 1 << 4,
	PARSER_MERGE_IGNORE_VARIABLES_IN_CONDITIONALS = 1 << 5,
};

enum ParserLookupVariableBehavior {
	PARSER_LOOKUP_DEFAULT = 0,
	PARSER_LOOKUP_FIRST = 1 << 0,
	PARSER_LOOKUP_IGNORE_VARIABLES_IN_CONDITIIONALS = 1 << 1,
};

enum ParserError {
	PARSER_ERROR_OK = 0,
	PARSER_ERROR_BUFFER_TOO_SMALL,
	PARSER_ERROR_DIFFERENCES_FOUND,
	PARSER_ERROR_EDIT_FAILED,
	PARSER_ERROR_EXPECTED_CHAR,
	PARSER_ERROR_EXPECTED_INT,
	PARSER_ERROR_EXPECTED_TOKEN,
	PARSER_ERROR_INVALID_ARGUMENT,
	PARSER_ERROR_INVALID_REGEXP,
	PARSER_ERROR_IO,
	PARSER_ERROR_UNHANDLED_TOKEN_TYPE,
	PARSER_ERROR_UNSPECIFIED,
};

enum ParserMetadata {
	PARSER_METADATA_CABAL_EXECUTABLES = 0,
	PARSER_METADATA_FLAVORS,
	PARSER_METADATA_LICENSES,
	PARSER_METADATA_MASTERDIR,
	PARSER_METADATA_SHEBANG_LANGS,
	PARSER_METADATA_OPTION_DESCRIPTIONS,
	PARSER_METADATA_OPTION_GROUPS,
	PARSER_METADATA_OPTIONS,
	PARSER_METADATA_POST_PLIST_TARGETS,
#if PORTFMT_SUBPACKAGES
	PARSER_METADATA_SUBPACKAGES,
#endif
// Used as sentinel, keep PARSER_METADATA_USES last
	PARSER_METADATA_USES,
};

struct ParserSettings {
	char *filename;
	enum ParserBehavior behavior;
	int target_command_format_threshold;
	size_t diff_context;
	size_t target_command_format_wrapcol;
	size_t wrapcol;
};

struct Array;
struct Mempool;
struct Parser;
struct Set;
struct Token;

typedef struct Array *(*ParserEditFn)(struct Parser *, struct Array *, struct Mempool *, void *);

#define PARSER_EDIT(name) \
	struct Array *name(struct Parser *parser, struct Array *ptokens, struct Mempool *extpool, void *userdata)

struct Parser *parser_new(struct Mempool *, struct ParserSettings *);
void parser_init_settings(struct ParserSettings *);
enum ParserError parser_read_from_buffer(struct Parser *, const char *, size_t);
enum ParserError parser_read_from_file(struct Parser *, FILE *);
enum ParserError parser_read_finish(struct Parser *);
char *parser_error_tostring(struct Parser *, struct Mempool *);
void parser_set_error(struct Parser *, enum ParserError, const char *);
void parser_free(struct Parser *);
enum ParserError parser_output_write_to_file(struct Parser *, FILE *);
enum ParserError parser_edit(struct Parser *, struct Mempool *, ParserEditFn, void *);
void parser_enqueue_output(struct Parser *, const char *);
struct Target *parser_lookup_target(struct Parser *, const char *, struct Mempool *, struct Array **);
struct Variable *parser_lookup_variable(struct Parser *, const char *, enum ParserLookupVariableBehavior, struct Mempool *, struct Array **, struct Array **);
struct Variable *parser_lookup_variable_str(struct Parser *, const char *, enum ParserLookupVariableBehavior, struct Mempool *, char **, char **);
void parser_mark_for_gc(struct Parser *, struct Token *);
void parser_mark_edited(struct Parser *, struct Token *);
void *parser_metadata(struct Parser *, enum ParserMetadata);
enum ParserError parser_merge(struct Parser *, struct Parser *, enum ParserMergeBehavior);
struct ParserSettings parser_settings(struct Parser *);
