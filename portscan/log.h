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
#pragma once

struct PortscanLog;
struct PortscanLogDir;
struct Set;

enum PortscanLogEntryType {
	PORTSCAN_LOG_ENTRY_UNKNOWN_VAR,
	PORTSCAN_LOG_ENTRY_UNKNOWN_TARGET,
	PORTSCAN_LOG_ENTRY_DUPLICATE_VAR,
	PORTSCAN_LOG_ENTRY_OPTION_DEFAULT_DESCRIPTION,
	PORTSCAN_LOG_ENTRY_OPTION_GROUP,
	PORTSCAN_LOG_ENTRY_OPTION,
	PORTSCAN_LOG_ENTRY_CATEGORY_NONEXISTENT_PORT,
	PORTSCAN_LOG_ENTRY_CATEGORY_UNHOOKED_PORT,
	PORTSCAN_LOG_ENTRY_CATEGORY_UNSORTED,
	PORTSCAN_LOG_ENTRY_ERROR,
	PORTSCAN_LOG_ENTRY_VARIABLE_VALUE,
	PORTSCAN_LOG_ENTRY_COMMENT,
};

#define PORTSCAN_LOG_LATEST "portscan-latest.log"
#define PORTSCAN_LOG_PREVIOUS "portscan-previous.log"

struct PortscanLogDir *portscan_log_dir_open(struct Mempool *, const char *, int);
void portscan_log_dir_close(struct PortscanLogDir *);

struct PortscanLog *portscan_log_new(struct Mempool *);
struct PortscanLog *portscan_log_read_all(struct Mempool *, struct PortscanLogDir *, const char *);
void portscan_log_free(struct PortscanLog *);

size_t portscan_log_len(struct PortscanLog *);
void portscan_log_add_entries(struct PortscanLog *, enum PortscanLogEntryType, const char *, struct Set *);
void portscan_log_add_entry(struct PortscanLog *, enum PortscanLogEntryType, const char *, const char *);
int portscan_log_compare(struct PortscanLog *, struct PortscanLog *);
int portscan_log_serialize_to_file(struct PortscanLog *, FILE *);
int portscan_log_serialize_to_dir(struct PortscanLog *, struct PortscanLogDir *);
