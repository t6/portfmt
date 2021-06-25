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

#include <sys/param.h>
#include <sys/stat.h>
#if HAVE_CAPSICUM
# include <sys/capsicum.h>
#endif
#include <assert.h>
#include <dirent.h>
#if HAVE_ERR
# include <err.h>
#endif
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <pthread.h>
#include <regex.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include <unistd.h>

#include <libias/array.h>
#include <libias/diff.h>
#include <libias/io.h>
#include <libias/map.h>
#include <libias/mempool.h>
#include <libias/mempool/dir.h>
#include <libias/mempool/file.h>
#include <libias/set.h>
#include <libias/str.h>
#include <libias/util.h>

#include "capsicum_helpers.h"
#include "conditional.h"
#include "mainutils.h"
#include "parser.h"
#include "parser/edits.h"
#include "portscan/log.h"
#include "portscan/status.h"
#include "regexp.h"
#include "token.h"
#include "variable.h"

enum ScanFlags {
	SCAN_NOTHING = 0,
	SCAN_CATEGORIES = 1 << 0,
	SCAN_CLONES = 1 << 1,
	SCAN_OPTION_DEFAULT_DESCRIPTIONS = 1 << 2,
	SCAN_OPTIONS = 1 << 3,
	SCAN_UNKNOWN_TARGETS = 1 << 4,
	SCAN_UNKNOWN_VARIABLES = 1 << 5,
	SCAN_VARIABLE_VALUES = 1 << 6,
	SCAN_PARTIAL = 1 << 7,
	SCAN_COMMENTS = 1 << 8,
};

enum ScanLongopts {
	SCAN_LONGOPT_ALL,
	SCAN_LONGOPT_CATEGORIES,
	SCAN_LONGOPT_CLONES,
	SCAN_LONGOPT_COMMENTS,
	SCAN_LONGOPT_OPTION_DEFAULT_DESCRIPTIONS,
	SCAN_LONGOPT_OPTIONS,
	SCAN_LONGOPT_PROGRESS,
	SCAN_LONGOPT_UNKNOWN_TARGETS,
	SCAN_LONGOPT_UNKNOWN_VARIABLES,
	SCAN_LONGOPT_VARIABLE_VALUES,
	SCAN_LONGOPT__N
};

struct ScanLongoptsState {
	int flag;
	const char *optarg;
};

struct ScanResult {
	struct Mempool *pool;
	char *origin;
	struct Set *comments;
	struct Set *errors;
	struct Set *unknown_variables;
	struct Set *unknown_targets;
	struct Set *clones;
	struct Set *option_default_descriptions;
	struct Set *option_groups;
	struct Set *options;
	struct Set *variable_values;
	enum ScanFlags flags;
};

struct ScanPortArgs {
	enum ScanFlags flags;
	int portsdir;
	const char *path;
	struct Regexp *keyquery;
	struct Regexp *query;
	ssize_t editdist;
	struct Map *default_option_descriptions;
	struct ScanResult *result;
};

struct CategoryReaderData {
	int portsdir;
	struct Array *categories;
	atomic_size_t *categories_index;
	enum ScanFlags flags;
};

struct CategoryReaderResult {
	struct Mempool *pool;
	struct Array *error_origins;
	struct Array *error_msgs;
	struct Array *nonexistent;
	struct Array *origins;
	struct Array *unhooked;
	struct Array *unsorted;
};

struct PortReaderData {
	int portsdir;
	struct Array *origins;
	atomic_size_t *origins_index;
	struct Regexp *keyquery;
	struct Regexp *query;
	ssize_t editdist;
	enum ScanFlags flags;
	struct Map *default_option_descriptions;
};

struct PortReaderResult {
	struct Mempool *pool;
	struct Array *scan_results;
};

static void lookup_subdirs(int, const char *, const char *, enum ScanFlags, struct Mempool *, struct Array *, struct Array *, struct Array *, struct Array *, struct Array *, struct Array *);
static void scan_port(struct ScanPortArgs *);
static void *lookup_origins_worker(void *);
static enum ParserError process_include(struct Parser *, struct Set *, const char *, int, const char *);
static PARSER_EDIT(extract_includes);
static PARSER_EDIT(get_default_option_descriptions);
static DIR *diropenat(struct Mempool *, int, const char *);
static FILE *fileopenat(struct Mempool *, int, const char *);
static void *scan_ports_worker(void *);
static struct Array *lookup_origins(struct Mempool *, int, enum ScanFlags, struct PortscanLog *);
static void scan_ports(int, struct Array *, enum ScanFlags, struct Regexp *, struct Regexp *, ssize_t, struct PortscanLog *);
static void usage(void);

static struct option longopts[SCAN_LONGOPT__N] = {
	[SCAN_LONGOPT_ALL] = { "all", no_argument, NULL, 1 },
	[SCAN_LONGOPT_CATEGORIES] = { "categories", no_argument, NULL, 1 },
	[SCAN_LONGOPT_CLONES] = { "clones", no_argument, NULL, 1 },
	[SCAN_LONGOPT_COMMENTS] = { "comments", no_argument, NULL, 1 },
	[SCAN_LONGOPT_OPTION_DEFAULT_DESCRIPTIONS] = { "option-default-descriptions", optional_argument, NULL, 1 },
	[SCAN_LONGOPT_OPTIONS] = { "options", no_argument, NULL, 1 },
	[SCAN_LONGOPT_PROGRESS] = { "progress", optional_argument, NULL, 1 },
	[SCAN_LONGOPT_UNKNOWN_TARGETS] = { "unknown-targets", no_argument, NULL, 1 },
	[SCAN_LONGOPT_UNKNOWN_VARIABLES] = { "unknown-variables", no_argument, NULL, 1 },
	[SCAN_LONGOPT_VARIABLE_VALUES] = { "variable-values", optional_argument, NULL, 1 },
};

static void
add_error(struct Set *errors, char *msg)
{
	if (!set_contains(errors, msg)) {
		set_add(errors, str_dup(NULL, msg));
	}
}

DIR *
diropenat(struct Mempool *pool, int root, const char *path)
{
	DIR *dir = mempool_opendirat(pool, root, path);
	if (dir == NULL) {
		return NULL;
	}

#if HAVE_CAPSICUM
	if (caph_limit_stream(dirfd(dir), CAPH_READ | CAPH_READDIR) < 0) {
		err(1, "caph_limit_stream: %s", path);
	}
#endif

	return dir;
}

FILE *
fileopenat(struct Mempool *pool, int root, const char *path)
{
	FILE *f = mempool_fopenat(pool, root, path, "r", 0);
	if (f == NULL) {
		return NULL;
	}

#if HAVE_CAPSICUM
	if (caph_limit_stream(fileno(f), CAPH_READ) < 0) {
		err(1, "caph_limit_stream: %s", path);
	}
#endif

	return f;
}

void
lookup_subdirs(int portsdir, const char *category, const char *path, enum ScanFlags flags, struct Mempool *extpool, struct Array *subdirs, struct Array *nonexistent, struct Array *unhooked, struct Array *unsorted, struct Array *error_origins, struct Array *error_msgs)
{
	SCOPE_MEMPOOL(pool);

	FILE *in = fileopenat(pool, portsdir, path);
	if (in == NULL) {
		array_append(error_origins, str_dup(extpool, path));
		array_append(error_msgs, str_printf(extpool, "fileopenat: %s", strerror(errno)));
		return;
	}

	struct ParserSettings settings;
	parser_init_settings(&settings);
	if (flags & SCAN_CATEGORIES) {
		settings.behavior |= PARSER_OUTPUT_REFORMAT | PARSER_OUTPUT_DIFF;
	}

	struct Parser *parser = parser_new(pool, &settings);
	enum ParserError error = parser_read_from_file(parser, in);
	if (error != PARSER_ERROR_OK) {
		array_append(error_origins, str_dup(extpool, path));
		array_append(error_msgs, parser_error_tostring(parser, extpool));
		return;
	}
	error = parser_read_finish(parser);
	if (error != PARSER_ERROR_OK) {
		array_append(error_origins, str_dup(extpool, path));
		array_append(error_msgs, parser_error_tostring(parser, extpool));
		return;
	}

	struct Array *tmp;
	if (parser_lookup_variable(parser, "SUBDIR", PARSER_LOOKUP_DEFAULT, pool, &tmp, NULL) == NULL) {
		return;
	}

	if (unhooked && (flags & SCAN_CATEGORIES)) {
		DIR *dir = diropenat(pool, portsdir, category);
		if (dir == NULL) {
			array_append(error_origins, str_dup(extpool, category));
			array_append(error_msgs, str_printf(extpool, "diropenat: %s", strerror(errno)));
		} else {
			DIR_FOREACH(dir, dp) {
				if (dp->d_name[0] == '.') {
					continue;
				}
				char *path = str_printf(pool, "%s/%s", category, dp->d_name);
				struct stat sb;
				if (fstatat(portsdir, path, &sb, 0) == -1 ||
				    !S_ISDIR(sb.st_mode)) {
					continue;
				}
				if (array_find(tmp, dp->d_name, str_compare, NULL) == -1) {
					array_append(unhooked, str_dup(extpool, path));
				}
			}
		}
	}

	ARRAY_FOREACH(tmp, char *, port) {
		char *origin;
		if (flags != SCAN_NOTHING) {
			origin = str_printf(pool, "%s/%s", category, port);
		} else {
			origin = port;
		}
		if (flags & SCAN_CATEGORIES) {
			struct stat sb;
			if (nonexistent &&
			    (fstatat(portsdir, origin, &sb, 0) == -1 ||
			     !S_ISDIR(sb.st_mode))) {
				array_append(nonexistent, str_dup(extpool, origin));
			}
		}
		array_append(subdirs, str_dup(extpool, origin));
	}

	if ((flags & SCAN_CATEGORIES) && unsorted &&
	    parser_output_write_to_file(parser, NULL) == PARSER_ERROR_DIFFERENCES_FOUND) {
		array_append(unsorted, str_dup(extpool, category));
	}
}

enum ParserError
process_include(struct Parser *parser, struct Set *errors, const char *curdir, int portsdir, const char *filename)
{
	SCOPE_MEMPOOL(pool);

	const char *path;
	if (str_startswith(filename, "${MASTERDIR}/")) {
		// Do not follow to the master port.  It would already
		// have been processed once, so we do not need to do
		// it again.
		return PARSER_ERROR_OK;
	} else if (str_startswith(filename, "${.PARSEDIR}/")) {
		filename += strlen("${.PARSEDIR}/");
		path = str_printf(pool, "%s/%s", curdir, filename);
	} else if (str_startswith(filename, "${.CURDIR}/")) {
		filename += strlen("${.CURDIR}/");
		path = str_printf(pool, "%s/%s", curdir, filename);
	} else if (str_startswith(filename, "${.CURDIR:H}/")) {
		filename += strlen("${.CURDIR:H}/");
		path = str_printf(pool, "%s/../%s", curdir, filename);
	} else if (str_startswith(filename, "${.CURDIR:H:H}/")) {
		filename += strlen("${.CURDIR:H:H}/");
		path = str_printf(pool, "%s/../../%s", curdir, filename);
	} else if (str_startswith(filename, "${PORTSDIR}/")) {
		filename += strlen("${PORTSDIR}/");
		path = filename;
	} else if (str_startswith(filename, "${FILESDIR}/")) {
		filename += strlen("${FILESDIR}/");
		path = str_printf(pool, "%s/files/%s", curdir, filename);
	} else {
		path = str_printf(pool, "%s/%s", curdir, filename);
	}
	FILE *f = fileopenat(pool, portsdir, path);
	if (f == NULL) {
		add_error(errors, str_printf(pool, "cannot open include: %s: %s", path, strerror(errno)));
		return PARSER_ERROR_OK;
	}
	return parser_read_from_file(parser, f);
}

PARSER_EDIT(extract_includes)
{
	struct Array **retval = userdata;

	struct Array *includes = mempool_array(extpool);
	int found = 0;

	ARRAY_FOREACH(ptokens, struct Token *, t) {
		switch (token_type(t)) {
		case CONDITIONAL_START:
			if (conditional_type(token_conditional(t)) == COND_INCLUDE) {
				found = 1;
			}
			break;
		case CONDITIONAL_TOKEN:
			if (found == 1) {
				found++;
			} else if (found > 1) {
				found = 0;
				char *data = token_data(t);
				if (data && *data == '"' && data[strlen(data) - 1] == '"') {
					data++;
					data[strlen(data) - 1] = 0;
					array_append(includes, data);
				}
			}
			break;
		case CONDITIONAL_END:
			found = 0;
			break;
		default:
			break;
		}
	}

	*retval = includes;

	return NULL;
}

static int
variable_value_filter(struct Parser *parser, const char *value, void *userdata)
{
	struct Regexp *query = userdata;
	return !query || regexp_exec(query, value) == 0;
}

static int
unknown_targets_filter(struct Parser *parser, const char *value, void *userdata)
{
	struct Regexp *query = userdata;
	return !query || regexp_exec(query, value) == 0;
}

static int
unknown_variables_filter(struct Parser *parser, const char *value, void *userdata)
{
	struct Regexp *query = userdata;
	return !query || regexp_exec(query, value) == 0;
}

static int
char_cmp(const void *ap, const void *bp, void *userdata)
{
	char a = *(char *)ap;
	char b = *(char *)bp;
	if (a < b) {
		return -1;
	} else if (a > b) {
		return 1;
	} else {
		return 0;
	}
}

static ssize_t
edit_distance(const char *a, const char *b)
{
	if (!a || !b) {
		return -1;
	}

	ssize_t editdist = -1;
	struct diff d;
	if (diff(&d, char_cmp, NULL, sizeof(char), a, strlen(a), b, strlen(b)) > 0) {
		editdist = d.editdist;
		free(d.ses);
		free(d.lcs);
	}

	return editdist;
}

static void
collect_output_unknowns(struct Mempool *extpool, const char *key, const char *value, const char *hint, void *userdata)
{
	if (!set_contains(userdata, key)) {
		set_add(userdata, str_dup(NULL, key));
	}
}

static void
collect_output_variable_values(struct Mempool *extpool, const char *key, const char *value, const char *hint, void *userdata)
{
	SCOPE_MEMPOOL(pool);

	char *buf = str_printf(pool, "%-30s\t%s", key, value);
	if (!set_contains(userdata, buf)) {
		set_add(userdata, str_dup(NULL, buf));
	}
}

void
scan_port(struct ScanPortArgs *args)
{
	SCOPE_MEMPOOL(pool);

	struct ScanResult *retval = args->result;
	retval->comments = mempool_set(retval->pool, str_compare, NULL, free);
	retval->errors = mempool_set(retval->pool, str_compare, NULL, free);
	retval->option_default_descriptions = mempool_set(retval->pool, str_compare, NULL, free);
	retval->option_groups = mempool_set(retval->pool, str_compare, NULL, free);
	retval->options = mempool_set(retval->pool, str_compare, NULL, free);
	retval->unknown_variables = mempool_set(retval->pool, str_compare, NULL, free);
	retval->unknown_targets = mempool_set(retval->pool, str_compare, NULL, free);
	retval->variable_values = mempool_set(retval->pool, str_compare, NULL, free);

	struct ParserSettings settings;
	parser_init_settings(&settings);
	settings.behavior = PARSER_OUTPUT_RAWLINES;

	FILE *in = fileopenat(pool, args->portsdir, args->path);
	if (in == NULL) {
		add_error(retval->errors, str_printf(pool, "fileopenat: %s", strerror(errno)));
		return;
	}

	struct Parser *parser = parser_new(pool, &settings);
	enum ParserError error = parser_read_from_file(parser, in);
	if (error != PARSER_ERROR_OK) {
		add_error(retval->errors, parser_error_tostring(parser, pool));
		return;
	}

	if (args->flags & SCAN_PARTIAL) {
		error = parser_edit(parser, pool, lint_bsd_port, NULL);
		if (error != PARSER_ERROR_OK) {
			add_error(retval->errors, parser_error_tostring(parser, pool));
			return;
		}
	}

	struct Array *includes = NULL;
	error = parser_edit(parser, retval->pool, extract_includes, &includes);
	if (error != PARSER_ERROR_OK) {
		add_error(retval->errors, parser_error_tostring(parser, pool));
		return;
	}
	ARRAY_FOREACH(includes, char *, include) {
		error = process_include(parser, retval->errors, retval->origin, args->portsdir, include);
		if (error != PARSER_ERROR_OK) {
			add_error(retval->errors, parser_error_tostring(parser, pool));
			return;
		}
	}

	error = parser_read_finish(parser);
	if (error != PARSER_ERROR_OK) {
		add_error(retval->errors, parser_error_tostring(parser, pool));
		return;
	}

	if (retval->flags & SCAN_UNKNOWN_VARIABLES) {
		struct ParserEditOutput param = { unknown_variables_filter, args->query, NULL, NULL, collect_output_unknowns, retval->unknown_variables, 0 };
		error = parser_edit(parser, pool, output_unknown_variables, &param);
		if (error != PARSER_ERROR_OK) {
			add_error(retval->errors, str_printf(pool, "output.unknown-variables: %s", parser_error_tostring(parser, pool)));
			return;
		}
	}

	if (retval->flags & SCAN_UNKNOWN_TARGETS) {
		struct ParserEditOutput param = { unknown_targets_filter, args->query, NULL, NULL, collect_output_unknowns, retval->unknown_targets, 0 };
		error = parser_edit(parser, pool, output_unknown_targets, &param);
		if (error != PARSER_ERROR_OK) {
			add_error(retval->errors, str_printf(pool, "output.unknown-targets: %s", parser_error_tostring(parser, pool)));
			return;
		}
	}

	if (retval->flags & SCAN_CLONES) {
		// XXX: Limit by query?
		error = parser_edit(parser, pool, lint_clones, &retval->clones);
		if (error != PARSER_ERROR_OK) {
			add_error(retval->errors, str_printf(pool, "lint.clones: %s", parser_error_tostring(parser, pool)));
			return;
		}
	}

	if (retval->flags & SCAN_OPTION_DEFAULT_DESCRIPTIONS) {
		struct Map *descs = parser_metadata(parser, PARSER_METADATA_OPTION_DESCRIPTIONS);
		MAP_FOREACH(descs, char *, var, char *, desc) {
			char *default_desc = map_get(args->default_option_descriptions, var);
			if (!default_desc) {
				continue;
			}
			if (!set_contains(retval->option_default_descriptions, var)) {
				ssize_t editdist = edit_distance(default_desc, desc);
				if (strcasecmp(default_desc, desc) == 0 || (editdist > 0 && editdist <= args->editdist)) {
					set_add(retval->option_default_descriptions, str_dup(NULL, var));
				}
			}
		}
	}

	if (retval->flags & SCAN_OPTIONS) {
		struct Set *groups = parser_metadata(parser, PARSER_METADATA_OPTION_GROUPS);
		SET_FOREACH(groups, char *, group) {
			if (!set_contains(retval->option_groups, group) &&
			    (args->query == NULL || regexp_exec(args->query, group) == 0)) {
				set_add(retval->option_groups, str_dup(NULL, group));
			}
		}
		struct Set *options = parser_metadata(parser, PARSER_METADATA_OPTIONS);
		SET_FOREACH(options, char *, option) {
			if (!set_contains(retval->options, option) &&
			    (args->query == NULL || regexp_exec(args->query, option) == 0)) {
				set_add(retval->options, str_dup(NULL, option));
			}
		}
	}

	if (retval->flags & SCAN_VARIABLE_VALUES) {
		struct ParserEditOutput param = { variable_value_filter, args->keyquery, variable_value_filter, args->query, collect_output_variable_values, retval->variable_values, 0 };
		error = parser_edit(parser, pool, output_variable_value, &param);
		if (error != PARSER_ERROR_OK) {
			add_error(retval->errors, str_printf(pool, "output.variable-value: %s", parser_error_tostring(parser, pool)));
			return;
		}
	}

	if (retval->flags & SCAN_COMMENTS) {
		struct Set *commented_portrevision = NULL;
		error = parser_edit(parser, pool, lint_commented_portrevision, &commented_portrevision);
		if (error != PARSER_ERROR_OK) {
			add_error(retval->errors, str_printf(pool, "lint.commented-portrevision: %s", parser_error_tostring(parser, pool)));
			return;
		}
		SET_FOREACH(commented_portrevision, char *, comment) {
			char *msg = str_printf(pool, "commented revision or epoch: %s", comment);
			if (!set_contains(retval->comments, msg)) {
				set_add(retval->comments, mempool_move(pool, msg, retval->pool));
			}
		}
		set_free(commented_portrevision);
	}
}

static char *
next_workitem(struct Array *items, atomic_size_t *items_index)
{
	return array_get(items, (*items_index)++);
}

void *
scan_ports_worker(void *userdata)
{
	struct PortReaderData *data = userdata;
	struct Mempool *pool = mempool_new();
	struct PortReaderResult *result = mempool_alloc(pool, sizeof(struct PortReaderResult));
	result->pool = pool;
	result->scan_results = mempool_array(pool);

	char *origin;
	while ((origin = next_workitem(data->origins, data->origins_index))) {
		portscan_status_print();
		const char *path = str_printf(pool, "%s/Makefile", origin);
		struct ScanResult *scan_result = mempool_alloc(pool, sizeof(struct ScanResult));
		scan_result->pool = pool;
		scan_result->origin = str_dup(pool, origin);
		scan_result->flags = data->flags;
		struct ScanPortArgs scan_port_args = {
			.flags = data->flags,
			.portsdir = data->portsdir,
			.path = path,
			.keyquery = data->keyquery,
			.query = data->query,
			.editdist = data->editdist,
			.result = scan_result,
			.default_option_descriptions = data->default_option_descriptions,
		};
		scan_port(&scan_port_args);
		portscan_status_inc();
		array_append(result->scan_results, scan_result);
	}

	return result;
}

void *
lookup_origins_worker(void *userdata)
{
	struct CategoryReaderData *data = userdata;
	struct Mempool *pool = mempool_new();
	struct CategoryReaderResult *result = mempool_alloc(pool, sizeof(struct CategoryReaderResult));
	result->pool = pool;
	result->error_origins = mempool_array(pool);
	result->error_msgs = mempool_array(pool);
	result->nonexistent = mempool_array(pool);
	result->unhooked = mempool_array(pool);
	result->unsorted = mempool_array(pool);
	result->origins = mempool_array(pool);

	char *category;
	while ((category = next_workitem(data->categories, data->categories_index))) {
		portscan_status_print();
		char *path = str_printf(pool, "%s/Makefile", category);
		lookup_subdirs(data->portsdir, category, path, data->flags, result->pool, result->origins, result->nonexistent, result->unhooked, result->unsorted, result->error_origins, result->error_msgs);
		portscan_status_inc();
	}

	return result;
}

static void *
join_next_thread(pthread_t **tid, ssize_t *n_threads)
{
	if (*n_threads > 0) {
		void *data;
		if (pthread_join(**tid, &data) != 0) {
			err(1, "pthread_join");
		} else {
			(*n_threads)--;
			(*tid)++;
			return data;
		}
	} else {
		return NULL;
	}
}

struct Array *
lookup_origins(struct Mempool *extpool, int portsdir, enum ScanFlags flags, struct PortscanLog *log)
{
	SCOPE_MEMPOOL(pool);
	struct Array *retval = mempool_array(extpool);

	struct Array *categories = mempool_array(pool);
	struct Array *error_origins = mempool_array(pool);
	struct Array *error_msgs = mempool_array(pool);
	lookup_subdirs(portsdir, "", "Makefile", SCAN_NOTHING, pool, categories, NULL, NULL, NULL, error_origins, error_msgs);

	ARRAY_FOREACH(error_origins, char *, origin) {
		char *msg = array_get(error_msgs, origin_index);
		portscan_log_add_entry(log, PORTSCAN_LOG_ENTRY_ERROR, origin, msg);
	}

	portscan_status_reset(PORTSCAN_STATUS_CATEGORIES, array_len(categories));
	ssize_t n_threads = sysconf(_SC_NPROCESSORS_ONLN);
	if (n_threads < 0) {
		err(1, "sysconf");
	}
	atomic_size_t categories_index = 0;
	struct CategoryReaderData data = {
		.portsdir = portsdir,
		.categories = categories,
		.categories_index = &categories_index,
		.flags = flags,
	};
	pthread_t *tid = mempool_take(pool, xrecallocarray(NULL, 0, n_threads, sizeof(pthread_t)));
	for (ssize_t i = 0; i < n_threads; i++) {
		if (pthread_create(&tid[i], NULL, lookup_origins_worker, &data) != 0) {
			err(1, "pthread_create");
		}
	}

	for (struct CategoryReaderResult *result = lookup_origins_worker(&data); result; result = join_next_thread(&tid, &n_threads)) {
		ARRAY_FOREACH(result->error_origins, char *, origin) {
			char *msg = array_get(result->error_msgs, origin_index);
			portscan_log_add_entry(log, PORTSCAN_LOG_ENTRY_ERROR, origin, msg);
		}
		ARRAY_FOREACH(result->nonexistent, char *, origin) {
			portscan_log_add_entry(log, PORTSCAN_LOG_ENTRY_CATEGORY_NONEXISTENT_PORT, origin, "entry without existing directory");
		}
		ARRAY_FOREACH(result->unhooked, char *, origin) {
			portscan_log_add_entry(log, PORTSCAN_LOG_ENTRY_CATEGORY_UNHOOKED_PORT, origin, "unhooked port");
		}
		ARRAY_FOREACH(result->unsorted, char *, origin) {
			portscan_log_add_entry(log, PORTSCAN_LOG_ENTRY_CATEGORY_UNSORTED, origin, "unsorted category or other formatting issues");
		}
		ARRAY_FOREACH(result->origins, char *, origin) {
			array_append(retval, mempool_move(result->pool, origin, extpool));
		}
		mempool_free(result->pool);
	}

	// Get consistent output even when category Makefiles are
	// not sorted correctly
	array_sort(retval, str_compare, NULL);

	return retval;
}

PARSER_EDIT(get_default_option_descriptions)
{
	SCOPE_MEMPOOL(pool);

	struct Array *desctokens = mempool_array(pool);
	struct Map *default_option_descriptions = mempool_map(extpool, str_compare, NULL, free, free);
	ARRAY_FOREACH(ptokens, struct Token *, t) {
		switch (token_type(t)) {
		case VARIABLE_TOKEN:
			if (str_endswith(variable_name(token_variable(t)), "_DESC")) {
				array_append(desctokens, token_data(t));
			}
			break;
		case VARIABLE_END:
			if (!map_contains(default_option_descriptions, variable_name(token_variable(t)))) {
				map_add(default_option_descriptions, str_dup(NULL, variable_name(token_variable(t))), str_join(NULL, desctokens, " "));
			}
			array_truncate(desctokens);
			break;
		default:
			break;
		}
	}

	struct Map **retval = (struct Map **)userdata;
	*retval = default_option_descriptions;

	return NULL;
}

void
scan_ports(int portsdir, struct Array *origins, enum ScanFlags flags, struct Regexp *keyquery, struct Regexp *query, ssize_t editdist, struct PortscanLog *retval)
{
	SCOPE_MEMPOOL(pool);

	if (!(flags & (SCAN_CLONES |
		       SCAN_COMMENTS |
		       SCAN_OPTION_DEFAULT_DESCRIPTIONS |
		       SCAN_OPTIONS |
		       SCAN_UNKNOWN_TARGETS |
		       SCAN_UNKNOWN_VARIABLES |
		       SCAN_VARIABLE_VALUES))) {
		return;
	}

	FILE *in = fileopenat(pool, portsdir, "Mk/bsd.options.desc.mk");
	if (in == NULL) {
		portscan_log_add_entry(retval, PORTSCAN_LOG_ENTRY_ERROR, "Mk/bsd.options.desc.mk",
			str_printf(pool, "fileopenat: %s", strerror(errno)));
		return;
	}

	struct ParserSettings settings;
	parser_init_settings(&settings);
	struct Parser *parser = parser_new(pool, &settings);
	enum ParserError error = parser_read_from_file(parser, in);
	if (error != PARSER_ERROR_OK) {
		portscan_log_add_entry(retval, PORTSCAN_LOG_ENTRY_ERROR, "Mk/bsd.options.desc.mk", parser_error_tostring(parser, pool));
		return;
	}
	error = parser_read_finish(parser);
	if (error != PARSER_ERROR_OK) {
		portscan_log_add_entry(retval, PORTSCAN_LOG_ENTRY_ERROR, "Mk/bsd.options.desc.mk", parser_error_tostring(parser, pool));
		return;
	}

	struct Map *default_option_descriptions = NULL;
	if (parser_edit(parser, pool, get_default_option_descriptions, &default_option_descriptions) != PARSER_ERROR_OK) {
		portscan_log_add_entry(retval, PORTSCAN_LOG_ENTRY_ERROR, "Mk/bsd.options.desc.mk", parser_error_tostring(parser, pool));
		return;
	}
	assert(default_option_descriptions);

	ssize_t n_threads = sysconf(_SC_NPROCESSORS_ONLN);
	if (n_threads < 0) {
		err(1, "sysconf");
	}
	pthread_t *tid = mempool_take(pool, xrecallocarray(NULL, 0, n_threads, sizeof(pthread_t)));
	atomic_size_t origins_index = 0;
	struct PortReaderData data = {
		.portsdir = portsdir,
		.origins = origins,
		.origins_index = &origins_index,
		.keyquery = keyquery,
		.query = query,
		.editdist = editdist,
		.flags = flags,
		.default_option_descriptions = default_option_descriptions,
	};
	for (ssize_t i = 0; i < n_threads; i++) {
		if (pthread_create(&tid[i], NULL, scan_ports_worker, &data) != 0) {
			err(1, "pthread_create");
		}
	}

	for (struct PortReaderResult *result = scan_ports_worker(&data); result; result = join_next_thread(&tid, &n_threads)) {
		ARRAY_FOREACH(result->scan_results, struct ScanResult *, r) {
			portscan_status_print();
			portscan_log_add_entries(retval, PORTSCAN_LOG_ENTRY_ERROR, r->origin, r->errors);
			portscan_log_add_entries(retval, PORTSCAN_LOG_ENTRY_UNKNOWN_VAR, r->origin, r->unknown_variables);
			portscan_log_add_entries(retval, PORTSCAN_LOG_ENTRY_UNKNOWN_TARGET, r->origin, r->unknown_targets);
			portscan_log_add_entries(retval, PORTSCAN_LOG_ENTRY_DUPLICATE_VAR, r->origin, r->clones);
			portscan_log_add_entries(retval, PORTSCAN_LOG_ENTRY_OPTION_DEFAULT_DESCRIPTION, r->origin, r->option_default_descriptions);
			portscan_log_add_entries(retval, PORTSCAN_LOG_ENTRY_OPTION_GROUP, r->origin, r->option_groups);
			portscan_log_add_entries(retval, PORTSCAN_LOG_ENTRY_OPTION, r->origin, r->options);
			portscan_log_add_entries(retval, PORTSCAN_LOG_ENTRY_VARIABLE_VALUE, r->origin, r->variable_values);
			portscan_log_add_entries(retval, PORTSCAN_LOG_ENTRY_COMMENT, r->origin, r->comments);
		}
		mempool_free(result->pool);
	}
}

void
usage()
{
	fprintf(stderr, "usage: portscan [-l <logdir>] [-p <portsdir>] [-q <regexp>] [--<check> ...] [<origin1> ...]\n");
	exit(EX_USAGE);
}

int
main(int argc, char *argv[])
{
	SCOPE_MEMPOOL(pool);

	const char *portsdir_path = getenv("PORTSDIR");
	const char *logdir_path = NULL;
	const char *keyquery = NULL;
	const char *query = NULL;
	unsigned int progressinterval = 0;

	struct ScanLongoptsState opts[SCAN_LONGOPT__N] = {};
	for (enum ScanLongopts i = 0; i < SCAN_LONGOPT__N; i++) {
		longopts[i].flag = &opts[i].flag;
	}

	enum ScanFlags flags = SCAN_NOTHING;
	int ch;
	int longindex;
	while ((ch = getopt_long(argc, argv, "l:q:o:p:", longopts, &longindex)) != -1) {
		switch (ch) {
		case 'l':
			logdir_path = optarg;
			break;
		case 'q':
			query = optarg;
			break;
		case 'o': {
			int found = 0;
			const char *name = NULL;
			for (enum ScanLongopts i = 0; !found && i < SCAN_LONGOPT__N; i++) {
				name = longopts[i].name;
				if (strcasecmp(optarg, name) == 0) {
					opts[i].flag = 1;
					opts[i].optarg = NULL;
					found = 1;
				} else if (longopts[i].has_arg != no_argument) {
					char *buf = str_printf(pool, "%s=", name);
					if (strncasecmp(optarg, buf, strlen(buf)) == 0) {
						opts[i].flag = 1;
						opts[i].optarg = optarg + strlen(buf);
						found = 1;
					}
				}
			}
			if (found) {
				warnx("`-o %s' is deprecated; use `--%s' instead", optarg, optarg);
			} else {
				warnx("unrecognized option `--%s'", optarg);
				usage();
			}
			break;
		} case 'p':
			portsdir_path = optarg;
			break;
		case 0:
			opts[longindex].flag = 1;
			opts[longindex].optarg = optarg;
			break;
		default:
			usage();
			break;
		}
	}
	argc -= optind;
	argv += optind;

	for (enum ScanLongopts i = 0; i < SCAN_LONGOPT__N; i++) {
		if (!opts[i].flag) {
			continue;
		}
		switch (i) {
		case SCAN_LONGOPT_ALL:
			flags = ~SCAN_NOTHING;
			break;
		case SCAN_LONGOPT_CATEGORIES:
			flags |= SCAN_CATEGORIES;
			break;
		case SCAN_LONGOPT_CLONES:
			flags |= SCAN_CLONES;
			break;
		case SCAN_LONGOPT_COMMENTS:
			flags |= SCAN_COMMENTS;
			break;
		case SCAN_LONGOPT_OPTION_DEFAULT_DESCRIPTIONS:
			flags |= SCAN_OPTION_DEFAULT_DESCRIPTIONS;
			break;
		case SCAN_LONGOPT_OPTIONS:
			flags |= SCAN_OPTIONS;
			break;
		case SCAN_LONGOPT_PROGRESS:
			progressinterval = 5;
			break;
		case SCAN_LONGOPT_UNKNOWN_TARGETS:
			flags |= SCAN_UNKNOWN_TARGETS;
			break;
		case SCAN_LONGOPT_UNKNOWN_VARIABLES:
			flags |= SCAN_UNKNOWN_VARIABLES;
			break;
		case SCAN_LONGOPT_VARIABLE_VALUES:
			flags |= SCAN_VARIABLE_VALUES;
			keyquery = opts[i].optarg;
			break;
		case SCAN_LONGOPT__N:
			break;
		}
	}

	if (flags == SCAN_NOTHING) {
		flags = SCAN_CATEGORIES | SCAN_CLONES | SCAN_COMMENTS |
			SCAN_OPTION_DEFAULT_DESCRIPTIONS | SCAN_UNKNOWN_TARGETS |
			SCAN_UNKNOWN_VARIABLES;
	}

	if (portsdir_path == NULL) {
		portsdir_path = "/usr/ports";
	}

#if HAVE_CAPSICUM
	if (caph_limit_stdio() < 0) {
		err(1, "caph_limit_stdio");
	}

	closefrom(STDERR_FILENO + 1);
	close(STDIN_FILENO);
#endif

	int portsdir = open(portsdir_path, O_DIRECTORY);
	if (portsdir == -1) {
		err(1, "open: %s", portsdir_path);
	}

	struct PortscanLogDir *logdir = NULL;
	FILE *out = stdout;
	if (logdir_path != NULL) {
		logdir = portscan_log_dir_open(pool, logdir_path, portsdir);
		if (logdir == NULL) {
			err(1, "portscan_log_dir_open: %s", logdir_path);
		}
		fclose(out);
		out = NULL;
	}

#if HAVE_CAPSICUM
	if (caph_limit_stream(portsdir, CAPH_LOOKUP | CAPH_READ | CAPH_READDIR) < 0) {
		err(1, "caph_limit_stream");
	}

	if (caph_enter() < 0) {
		err(1, "caph_enter");
	}
#endif

	if (opts[SCAN_LONGOPT_PROGRESS].optarg) {
		const char *error;
		progressinterval = strtonum(opts[SCAN_LONGOPT_PROGRESS].optarg, 1, 100000000, &error);
		if (error) {
			errx(1, "--progress=%s is %s (must be >=1)", opts[SCAN_LONGOPT_PROGRESS].optarg, error);
		}
	}
	portscan_status_init(progressinterval);

	struct Regexp *keyquery_regexp = NULL;
	if (keyquery) {
		keyquery_regexp = regexp_new_from_str(pool, keyquery, REG_EXTENDED);
		if (keyquery_regexp == NULL) {
			errx(1, "invalid regexp");
		}
	}
	struct Regexp *query_regexp = NULL;
	if (query) {
		query_regexp = regexp_new_from_str(pool, query, REG_EXTENDED);
		if (query_regexp == NULL) {
			errx(1, "invalid regexp");
		}
	}

	ssize_t editdist = 3;
	if (opts[SCAN_LONGOPT_OPTION_DEFAULT_DESCRIPTIONS].optarg) {
		const char *error;
		editdist = strtonum(opts[SCAN_LONGOPT_OPTION_DEFAULT_DESCRIPTIONS].optarg, 0, INT_MAX, &error);
		if (error) {
			errx(1, "--option-default-descriptions=%s is %s (must be >=0)", opts[SCAN_LONGOPT_OPTION_DEFAULT_DESCRIPTIONS].optarg, error);
		}
	}

	struct PortscanLog *result = portscan_log_new(pool);
	struct Array *origins = NULL;
	if (argc == 0) {
		origins = lookup_origins(pool, portsdir, flags, result);
	} else {
		flags |= SCAN_PARTIAL;
		origins = mempool_array(pool);
		for (int i = 0; i < argc; i++) {
			array_append(origins, str_dup(pool, argv[i]));
		}
	}

	portscan_status_reset(PORTSCAN_STATUS_PORTS, array_len(origins));
	scan_ports(portsdir, origins, flags, keyquery_regexp, query_regexp, editdist, result);
	if (portscan_log_len(result) > 0) {
		if (logdir != NULL) {
			struct PortscanLog *prev_result = portscan_log_read_all(pool, logdir, PORTSCAN_LOG_LATEST);
			if (portscan_log_compare(prev_result, result)) {
				if (progressinterval) {
					portscan_status_reset(PORTSCAN_STATUS_FINISHED, 0);
					portscan_status_print();
				}
				warnx("no changes compared to previous result");
				return 2;
			}
			if (!portscan_log_serialize_to_dir(result, logdir)) {
				err(1, "portscan_log_serialize_to_dir");
			}
		} else {
			if (!portscan_log_serialize_to_file(result, out)) {
				err(1, "portscan_log_serialize");
			}
		}
	}

	if (progressinterval) {
		portscan_status_reset(PORTSCAN_STATUS_FINISHED, 0);
		portscan_status_print();
	}

	return 0;
}
