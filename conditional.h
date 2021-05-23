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

struct Conditional;
struct Mempool;

enum ConditionalType {
	COND_DINCLUDE,
	COND_ELIF,
	COND_ELIFDEF,
	COND_ELIFMAKE,
	COND_ELIFNDEF,
	COND_ELSE,
	COND_ENDFOR,
	COND_ENDIF,
	COND_ERROR,
	COND_EXPORT_ENV,
	COND_EXPORT_LITERAL,
	COND_EXPORT,
	COND_FOR,
	COND_IF,
	COND_IFDEF,
	COND_IFMAKE,
	COND_IFNDEF,
	COND_IFNMAKE,
	COND_INCLUDE_POSIX,
	COND_INCLUDE,
	COND_INFO,
	COND_SINCLUDE,
	COND_UNDEF,
	COND_UNEXPORT_ENV,
	COND_UNEXPORT,
	COND_WARNING,
};

struct Conditional *conditional_new(char *);
struct Conditional *conditional_clone(struct Conditional *);
void conditional_free(struct Conditional *);
char *conditional_tostring(struct Conditional *, struct Mempool *);
enum ConditionalType conditional_type(struct Conditional *);
