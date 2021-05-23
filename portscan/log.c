/*-
 * SPDX-License-Identifier: BSD-2-Clause-FreeBSD
 *
 * Copyright (c) 2020 Tobias Kortkamp <tobik@FreeBSD.org>
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

#if HAVE_CAPSICUM
# include <sys/capsicum.h>
#endif
#include <sys/stat.h>
#include <ctype.h>
#if HAVE_ERR
# include <err.h>
#endif
#include <errno.h>
#include <limits.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <libias/array.h>
#include <libias/diff.h>
#include <libias/mempool.h>
#include <libias/set.h>
#include <libias/str.h>
#include <libias/util.h>

#include "capsicum_helpers.h"
#include "portscan/log.h"

struct PortscanLogDir {
	int fd;
	char *path;
	char *commit;
};

struct PortscanLog {
	struct Mempool *pool;
	struct Array *entries;
};

struct PortscanLogEntry {
	enum PortscanLogEntryType type;
	size_t index;
	char *origin;
	char *value;
};

#define PORTSCAN_LOG_DATE_FORMAT "portscan-%Y%m%d%H%M%S"
#define PORTSCAN_LOG_INIT "/dev/null"

static void portscan_log_sort(struct PortscanLog *);
static char *log_entry_tostring(const struct PortscanLogEntry *, struct Mempool *);
static int log_entry_compare(const void *, const void *, void *);
static struct PortscanLogEntry *log_entry_parse(struct Mempool *, const char *);

static FILE *log_open(struct PortscanLogDir *, const char *);
static int log_update_latest(struct PortscanLogDir *, const char *);
static char *log_filename(const char *, struct Mempool *);
static char *log_commit(int, struct Mempool *);

struct PortscanLog *
portscan_log_new(struct Mempool *extpool)
{
	struct Mempool *pool = mempool_new();
	struct PortscanLog *log = mempool_alloc(pool, sizeof(struct PortscanLog));
	log->pool = pool;
	log->entries = mempool_array(pool);
	return mempool_add(extpool, log, portscan_log_free);
}

void
portscan_log_free(struct PortscanLog *log)
{
	if (log == NULL) {
		return;
	}
	mempool_free(log->pool);
}

void
portscan_log_sort(struct PortscanLog *log)
{
	array_sort(log->entries, log_entry_compare, NULL);
}

size_t
portscan_log_len(struct PortscanLog *log)
{
	return array_len(log->entries);
}

char *
log_entry_tostring(const struct PortscanLogEntry *entry, struct Mempool *pool)
{
	switch (entry->type) {
	case PORTSCAN_LOG_ENTRY_UNKNOWN_VAR:
		return str_printf(pool, "%-7c %-40s %s\n", 'V', entry->origin, entry->value);
	case PORTSCAN_LOG_ENTRY_UNKNOWN_TARGET:
		return str_printf(pool, "%-7c %-40s %s\n", 'T', entry->origin, entry->value);
	case PORTSCAN_LOG_ENTRY_DUPLICATE_VAR:
		return str_printf(pool, "%-7s %-40s %s\n", "Vc", entry->origin, entry->value);
	case PORTSCAN_LOG_ENTRY_OPTION_DEFAULT_DESCRIPTION:
		return str_printf(pool, "%-7s %-40s %s\n", "OD", entry->origin, entry->value);
	case PORTSCAN_LOG_ENTRY_OPTION_GROUP:
		return str_printf(pool, "%-7s %-40s %s\n", "OG", entry->origin, entry->value);
	case PORTSCAN_LOG_ENTRY_OPTION:
		return str_printf(pool, "%-7c %-40s %s\n", 'O', entry->origin, entry->value);
	case PORTSCAN_LOG_ENTRY_CATEGORY_NONEXISTENT_PORT:
		return str_printf(pool, "%-7s %-40s %s\n", "Ce", entry->origin, entry->value);
	case PORTSCAN_LOG_ENTRY_CATEGORY_UNHOOKED_PORT:
		return str_printf(pool, "%-7s %-40s %s\n", "Cu", entry->origin, entry->value);
	case PORTSCAN_LOG_ENTRY_CATEGORY_UNSORTED:
		return str_printf(pool, "%-7c %-40s %s\n", 'C', entry->origin, entry->value);
	case PORTSCAN_LOG_ENTRY_ERROR:
		return str_printf(pool, "%-7c %-40s %s\n", 'E', entry->origin, entry->value);
	case PORTSCAN_LOG_ENTRY_VARIABLE_VALUE:
		return str_printf(pool, "%-7s %-40s %s\n", "Vv", entry->origin, entry->value);
	case PORTSCAN_LOG_ENTRY_COMMENT:
		return str_printf(pool, "%-7c %-40s %s\n", '#', entry->origin, entry->value);
	default:
		abort();
	}

	return NULL;
}

void
portscan_log_add_entries(struct PortscanLog *log, enum PortscanLogEntryType type, const char *origin, struct Set *values)
{
	if (values == NULL) {
		return;
	}

	SET_FOREACH (values, const char *, value) {
		portscan_log_add_entry(log, type, origin, value);
	}
}

void
portscan_log_add_entry(struct PortscanLog *log, enum PortscanLogEntryType type, const char *origin, const char *value)
{
	struct PortscanLogEntry *entry = mempool_alloc(log->pool, sizeof(struct PortscanLogEntry));
	entry->type = type;
	entry->index = array_len(log->entries);
	entry->origin = str_dup(log->pool, origin);
	entry->value = str_dup(log->pool, value);
	array_append(log->entries, entry);
}

struct PortscanLogEntry *
log_entry_parse(struct Mempool *pool, const char *s)
{
	enum PortscanLogEntryType type = PORTSCAN_LOG_ENTRY_UNKNOWN_VAR;
	if (str_startswith(s, "V ")) {
		type = PORTSCAN_LOG_ENTRY_UNKNOWN_VAR;
		s++;
	} else if (str_startswith(s, "T ")) {
		type = PORTSCAN_LOG_ENTRY_UNKNOWN_TARGET;
		s++;
	} else if (str_startswith(s, "Vc ")) {
		type = PORTSCAN_LOG_ENTRY_DUPLICATE_VAR;
		s += 2;
	} else if (str_startswith(s, "OD ")) {
		type = PORTSCAN_LOG_ENTRY_OPTION_DEFAULT_DESCRIPTION;
		s += 2;
	} else if (str_startswith(s, "OG ")) {
		type = PORTSCAN_LOG_ENTRY_OPTION_GROUP;
		s += 2;
	} else if (str_startswith(s, "O ")) {
		type = PORTSCAN_LOG_ENTRY_OPTION;
		s++;
	} else if (str_startswith(s, "Ce ")) {
		type = PORTSCAN_LOG_ENTRY_CATEGORY_NONEXISTENT_PORT;
		s += 2;
	} else if (str_startswith(s, "Cu ")) {
		type = PORTSCAN_LOG_ENTRY_CATEGORY_UNHOOKED_PORT;
		s += 2;
	} else if (str_startswith(s, "C ")) {
		type = PORTSCAN_LOG_ENTRY_CATEGORY_UNSORTED;
		s++;
	} else if (str_startswith(s, "E ")) {
		type = PORTSCAN_LOG_ENTRY_ERROR;
		s++;
	} else if (str_startswith(s, "Vv ")) {
		type = PORTSCAN_LOG_ENTRY_VARIABLE_VALUE;
		s += 2;
	} else if (str_startswith(s, "# ")) {
		type = PORTSCAN_LOG_ENTRY_COMMENT;
		s++;
	} else {
		fprintf(stderr, "unable to parse log entry: %s\n", s);
		return NULL;
	}

	while (*s != 0 && isspace(*s)) {
		s++;
	}
	const char *origin_start = s;
	while (*s != 0 && !isspace(*s)) {
		s++;
	}
	const char *value = s;
	while (*value != 0 && isspace(*value)) {
		value++;
	}
	size_t value_len = strlen(value);
	if (value_len > 0 && value[value_len - 1] == '\n') {
		value_len--;
	}

	if ((s - origin_start) == 0 || value_len == 0) {
		fprintf(stderr, "unable to parse log entry: %s\n", s);
		return NULL;
	}

	struct PortscanLogEntry *e = mempool_alloc(pool, sizeof(struct PortscanLogEntry));
	e->type = type;
	e->origin = str_ndup(pool, origin_start, s - origin_start);
	e->value = str_ndup(pool, value, value_len);
	return e;
}

int
log_entry_compare(const void *ap, const void *bp, void *userdata)
{
	const struct PortscanLogEntry *a = *(const struct PortscanLogEntry **)ap;
	const struct PortscanLogEntry *b = *(const struct PortscanLogEntry **)bp;

	int retval = strcmp(a->origin, b->origin);
	if (retval == 0) {
		if (a->type > b->type) {
			retval = 1;
		} else if (a->type < b->type) {
			retval = -1;
		} else {
			retval = strcmp(a->value, b->value);
		}
	}

	return retval;
}

int
portscan_log_compare(struct PortscanLog *prev, struct PortscanLog *log)
{
	SCOPE_MEMPOOL(pool);

	portscan_log_sort(prev);
	portscan_log_sort(log);

	struct diff *p = array_diff(prev->entries, log->entries, pool, log_entry_compare, NULL);
	if (p == NULL) {
		errx(1, "array_diff failed");
	}
	int equal = 1;
	for (size_t i = 0; i < p->sessz; i++) {
		if (p->ses[i].type != DIFF_COMMON) {
			equal = 0;
			break;
		}
	}

	return equal;
}

int
portscan_log_serialize_to_file(struct PortscanLog *log, FILE *out)
{
	SCOPE_MEMPOOL(pool);

	portscan_log_sort(log);

	ARRAY_FOREACH(log->entries, struct PortscanLogEntry *, entry) {
		char *line = log_entry_tostring(entry, pool);
		if (write(fileno(out), line, strlen(line)) == -1) {
			return 0;
		}
	}

	return 1;
}

FILE *
log_open(struct PortscanLogDir *logdir, const char *log_path)
{
	int outfd = openat(logdir->fd, log_path, O_CREAT | O_WRONLY, 0644);
	if (outfd == -1) {
		return NULL;
	}

	FILE *f = fdopen(outfd, "w");
	if (f == NULL) {
		close(outfd);
		return NULL;
	}

	return f;
}

int
log_update_latest(struct PortscanLogDir *logdir, const char *log_path)
{
	SCOPE_MEMPOOL(pool);

	char *prev = NULL;
	if (!update_symlink(logdir->fd, log_path, PORTSCAN_LOG_LATEST, pool, &prev)) {
		return 0;
	}
	if (prev != NULL && !update_symlink(logdir->fd, prev, PORTSCAN_LOG_PREVIOUS, pool, NULL)) {
		return 0;
	}
	return 1;
}

char *
log_filename(const char *commit, struct Mempool *pool)
{
	time_t date = time(NULL);
	if (date == -1) {
		return NULL;
	}
	struct tm *tm = gmtime(&date);

	char buf[PATH_MAX];
	if (strftime(buf, sizeof(buf), PORTSCAN_LOG_DATE_FORMAT, tm) == 0) {
		return NULL;
	}

	return str_printf(pool, "%s-%s.log", buf, commit);
}

int
portscan_log_serialize_to_dir(struct PortscanLog *log, struct PortscanLogDir *logdir)
{
	SCOPE_MEMPOOL(pool);

	char *log_path = log_filename(logdir->commit, pool);
	FILE *out = mempool_add(pool, log_open(logdir, log_path), fclose);
	if (out == NULL) {
		return 0;
	}
	if (!portscan_log_serialize_to_file(log, out) ||
	    !log_update_latest(logdir, log_path)) {
		return 0;
	}

	return 1;
}

char *
log_commit(int portsdir, struct Mempool *pool)
{
	if (fchdir(portsdir) == -1) {
		err(1, "fchdir");
	}

	FILE *fp = popen("git rev-parse HEAD 2>/dev/null", "r");
	if (fp == NULL) {
		err(1, "popen");
	}

	char *revision = NULL;
	char *line = NULL;
	size_t linecap = 0;
	ssize_t linelen;
	if ((linelen = getline(&line, &linecap, fp)) > 0) {
		if (linelen > 0 && line[linelen - 1] == '\n') {
			line[linelen - 1] = 0;
		}
		revision = str_printf(pool, "%s", line);
	}
	free(line);
	pclose(fp);

	if (revision == NULL) {
		revision = str_dup(pool, "unknown");
	}
	return revision;
}

struct PortscanLogDir *
portscan_log_dir_open(struct Mempool *extpool, const char *logdir_path, int portsdir)
{
	SCOPE_MEMPOOL(pool);

	int created_dir = 0;
	int logdir;
	while ((logdir = open(logdir_path, O_DIRECTORY)) == -1) {
		if (errno == ENOENT) {
			if (mkdir(logdir_path, 0777) == -1) {
				return NULL;
			}
			created_dir = 1;
		} else {
			return NULL;
		}
	}
	if (created_dir) {
		if (symlinkat(PORTSCAN_LOG_INIT, logdir, PORTSCAN_LOG_PREVIOUS) == -1) {
			goto error;
		}
		if (symlinkat(PORTSCAN_LOG_INIT, logdir, PORTSCAN_LOG_LATEST) == -1) {
			goto error;
		}
	} else {
		char *prev = read_symlink(logdir, PORTSCAN_LOG_PREVIOUS, pool);
		if (prev == NULL &&
		    symlinkat(PORTSCAN_LOG_INIT, logdir, PORTSCAN_LOG_PREVIOUS) == -1) {
			goto error;
		}

		char *latest = read_symlink(logdir, PORTSCAN_LOG_LATEST, pool);
		if (latest == NULL &&
		    symlinkat(PORTSCAN_LOG_INIT, logdir, PORTSCAN_LOG_LATEST) == -1) {
			goto error;
		}
	}

#if HAVE_CAPSICUM
	if (caph_limit_stream(logdir, CAPH_CREATE | CAPH_READ | CAPH_SYMLINK) < 0) {
		err(1, "caph_limit_stream");
	}
#endif
	struct PortscanLogDir *dir = xmalloc(sizeof(struct PortscanLogDir));
	dir->fd = logdir;
	dir->path = str_dup(NULL, logdir_path);
	dir->commit = str_dup(NULL, log_commit(portsdir, pool));

	return mempool_add(extpool, dir, portscan_log_dir_close);

error:
	close(logdir);
	return NULL;
}

void
portscan_log_dir_close(struct PortscanLogDir *dir)
{
	if (dir == NULL) {
		return;
	}
	close(dir->fd);
	free(dir->path);
	free(dir->commit);
	free(dir);
}

struct PortscanLog *
portscan_log_read_all(struct Mempool *extpool, struct PortscanLogDir *logdir, const char *log_path)
{
	SCOPE_MEMPOOL(pool);

	struct PortscanLog *log = portscan_log_new(extpool);

	char *buf = read_symlink(logdir->fd, log_path, pool);
	if (buf == NULL) {
		if (errno == ENOENT) {
			return log;
		} else if (errno != EINVAL) {
			err(1, "read_symlink: %s", log_path);
		}
	} else if (strcmp(buf, PORTSCAN_LOG_INIT) == 0) {
		return log;
	}

	int fd = mempool_takefd(pool, openat(logdir->fd, log_path, O_RDONLY));
	if (fd == -1) {
		if (errno == ENOENT) {
			return log;
		}
		err(1, "openat: %s", log_path);
	}

	FILE *fp = mempool_add(pool, fdopen(fd, "r"), fclose);
	if (fp == NULL) {
		return log;
	}

	ssize_t linelen;
	size_t linecap = 0;
	char *line = NULL;
	while ((linelen = getline(&line, &linecap, fp)) > 0) {
		struct PortscanLogEntry *entry = log_entry_parse(log->pool, line);
		if (entry != NULL) {
			array_append(log->entries, entry);
		}
	}
	free(line);

	portscan_log_sort(log);

	return log;
}

