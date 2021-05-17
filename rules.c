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
#include <assert.h>
#include <ctype.h>
#if HAVE_ERR
# include <err.h>
#endif
#include <math.h>
#include <regex.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <libias/array.h>
#include <libias/set.h>
#include <libias/util.h>

#include "conditional.h"
#include "regexp.h"
#include "rules.h"
#include "parser.h"
#include "token.h"
#include "variable.h"

static int case_sensitive_sort(struct Parser *, struct Variable *);
static int compare_rel(const char *[], size_t, const char *, const char *);
static int compare_license_perms(struct Parser *, struct Variable *, const char *, const char *, int *);
static int compare_plist_files(struct Parser *, struct Variable *, const char *, const char *, int *);
static int compare_use_gnome(struct Variable *, const char *, const char *, int *);
static int compare_use_kde(struct Variable *, const char *, const char *, int *);
static int compare_use_pyqt(struct Variable *, const char *, const char *, int *);
static int compare_use_qt(struct Variable *, const char *, const char *, int *);
static char *extract_subpkg(struct Parser *, const char *, char **);
static int is_cabal_datadir_vars(struct Parser *, const char *, char **, char **);
static int is_flavors_helper(struct Parser *, const char *, char **, char **);
static int is_shebang_lang(struct Parser *, const char *, char **, char **);
static int is_valid_license(struct Parser *, const char *);
static int matches_license_name(struct Parser *, const char *);
static int matches_options_group(struct Parser *, const char *, char **);
static char *remove_plist_keyword(const char *);
static void target_extract_opt(struct Parser *, const char *, char **, char **, int *);
static int variable_has_flag(struct Parser *, const char *, int);

static struct {
	const char *pattern;
	int flags;
	regex_t re;
} regular_expressions[] = {
	[RE_CONDITIONAL]      = { "^(include|\\.[[:space:]]*(error|export|export-env|"
				  "export\\.env|export-literal|info|undef|unexport|for|endfor|"
				  "unexport-env|warning|if|ifdef|ifndef|include|"
				  "ifmake|ifnmake|else|elif|elifdef|elifndef|"
				  "elifmake|endif|sinclude))([[:space:]]*|$|\\(|!)",
				  REG_EXTENDED, {} },
};

#include "generated_rules.h"

static const char *license_perms_rel[] = {
	"dist-mirror",
	"no-dist-mirror",
	"dist-sell",
	"no-dist-sell",
	"pkg-mirror",
	"no-pkg-mirror",
	"pkg-sell",
	"no-pkg-sell",
	"auto-accept",
	"no-auto-accept",
	"none",
};


static const char *target_command_wrap_after_each_token_[] = {
	"${INSTALL_DATA}",
	"${INSTALL_LIB}",
	"${INSTALL_MAN}",
	"${INSTALL_PROGRAM}",
	"${INSTALL_SCRIPT}",
	"${INSTALL}",
	"${MKDIR}",
	"${MV}",
	"${REINPLACE_CMD}",
	"${RMDIR}",
	"${SED}",
	"${STRIP_CMD}",
};

static struct {
	const char *name;
	int opthelper;
} target_order_[] = {
	{ "all", 0 },
	{ "post-chroot", 0 },
	{ "pre-everything", 0 },
	{ "fetch", 0 },
	{ "fetch-list", 0 },
	{ "fetch-recursive-list", 0 },
	{ "fetch-recursive", 0 },
	{ "fetch-required-list", 0 },
	{ "fetch-required", 0 },
	{ "fetch-specials", 0 },
	{ "fetch-url-list-int", 0 },
	{ "fetch-url-list", 0 },
	{ "fetch-urlall-list", 0 },
	{ "pre-fetch", 1 },
	{ "pre-fetch-script", 0 },
	{ "do-fetch", 1 },
	{ "post-fetch", 1 },
	{ "post-fetch-script", 0 },
	{ "checksum", 0 },
	{ "checksum-recursive", 0 },
	{ "extract", 0 },
	{ "pre-extract", 1 },
	{ "pre-extract-script", 0 },
	{ "do-extract", 1 },
	{ "post-extract", 1 },
	{ "post-extract-script", 0 },
	{ "patch", 0 },
	{ "pre-patch", 1 },
	{ "pre-patch-script", 0 },
	{ "do-patch", 1 },
	{ "post-patch", 1 },
	{ "post-patch-script", 0 },
	{ "configure", 0 },
	{ "pre-configure", 1 },
	{ "pre-configure-script", 0 },
	{ "do-configure", 1 },
	{ "post-configure", 1 },
	{ "post-configure-script", 0 },
	{ "build", 0 },
	{ "pre-build", 1 },
	{ "pre-build-script", 0 },
	{ "do-build", 1 },
	{ "post-build", 1 },
	{ "post-build-script", 0 },
	{ "install", 0 },
	{ "install-desktop-entries", 0 },
	{ "install-ldconfig-file", 0 },
	{ "install-mtree", 0 },
	{ "install-package", 0 },
	{ "install-rc-script", 0 },
	{ "pre-install", 1 },
	{ "pre-install-script", 0 },
	{ "pre-su-install", 0 },
	{ "do-install", 1 },
	{ "post-install", 1 },
	{ "post-install-script", 0 },
	{ "stage", 0 },
	{ "post-stage", 1 },
	{ "test", 0 },
	{ "pre-test", 1 },
	{ "do-test", 1 },
	{ "post-test", 1 },
	{ "package-name", 0 },
	{ "package-noinstall", 0 },
	{ "pre-package", 1 },
	{ "pre-package-script", 0 },
	{ "do-package", 1 },
	{ "post-package", 1 },
	{ "post-package-script", 0 },
	{ "pre-pkg-script", 0 },
	{ "pkg", 0 },
	{ "post-pkg-script", 0 },
	{ "clean", 0 },
	{ "pre-clean", 0 },
	{ "do-clean", 0 },
	{ "post-clean", 0 },

	{ "add-plist-data", 0 },
	{ "add-plist-docs", 0 },
	{ "add-plist-examples", 0 },
	{ "add-plist-info", 0 },
	{ "add-plist-post", 0 },
	{ "apply-slist", 0 },
	{ "check-already-installed", 0 },
	{ "check-build-conflicts", 0 },
	{ "check-config", 0 },
	{ "check-conflicts", 0 },
	{ "check-deprecated", 0 },
	{ "check-install-conflicts", 0 },
	{ "check-man", 0 },
	{ "check-orphans", 0 },
	{ "check-plist", 0 },
	{ "check-sanity", 0 },
	{ "check-umask", 0 },
	{ "checkpatch", 0 },
	{ "clean-depends", 0 },
	{ "compress-man", 0 },
	{ "config-conditional", 0 },
	{ "config-recursive", 0 },
	{ "config", 0 },
	{ "create-binary-alias", 0 },
	{ "create-binary-wrappers", 0 },
	{ "create-users-groups", 0 },
	{ "deinstall-all", 0 },
	{ "deinstall-depends", 0 },
	{ "deinstall", 0 },
	{ "delete-distfiles-list", 0 },
	{ "delete-distfiles", 0 },
	{ "delete-package-list", 0 },
	{ "delete-package", 0 },
	{ "depends", 0 },
	{ "describe", 0 },
	{ "distclean", 0 },
	{ "fake-pkg", 0 },
	{ "fix-shebang", 0 },
	{ "fixup-lib-pkgconfig", 0 },
	{ "generate-plist", 0 },
	{ "identify-install-conflicts", 0 },
	{ "limited-clean-depends", 0 },
	{ "maintainer", 0 },
	{ "makepatch", 0 },
	{ "makeplist", 0 },
	{ "makesum", 0 },
	{ "post-check-sanity-script", 0 },
	{ "pre-check-config", 0 },
	{ "pre-check-sanity-script", 0 },
	{ "pre-config", 0 },
	{ "pretty-print-build-depends-list", 0 },
	{ "pretty-print-config", 0 },
	{ "pretty-print-run-depends-list", 0 },
	{ "pretty-print-www-site", 0 },
	{ "readme", 0 },
	{ "readmes", 0 },
	{ "reinstall", 0 },
	{ "repackage", 0 },
	{ "restage", 0 },
	{ "rmconfig-recursive", 0 },
	{ "rmconfig", 0 },
	{ "run-autotools-fixup", 0 },
	{ "sanity-config", 0 },
	{ "security-check", 0 },
	{ "showconfig-recursive", 0 },
	{ "showconfig", 0 },
	{ "stage-dir", 0 },
	{ "stage-qa", 0 },
};

static const char *special_sources_[] = {
	".EXEC",
	".IGNORE",
	".MADE",
	".MAKE",
	".META",
	".NOMETA",
	".NOMETA_CMP",
	".NOPATH",
	".NOTMAIN",
	".OPTIONAL",
	".PHONY",
	".PRECIOUS",
	".SILENT",
	".USE",
	".USEBEFORE",
	".WAIT",
};

static const char *special_targets_[] = {
	".BEGIN",
	".DEFAULT",
	".DELETE_ON_ERROR",
	".END",
	".ERROR",
	".EXEC",
	".IGNORE",
	".INTERRUPT",
	".MADE",
	".MAIN",
	".MAKE",
	".MAKEFLAGS",
	".META",
	".NO_PARALLEL",
	".NOMAIN",
	".NOMETA_CMP",
	".NOMETA",
	".NOPATH",
	".NOTPARALLEL",
	".OBJDIR",
	".OPTIONAL",
	".ORDER",
	".PATH",
	".PHONY",
	".PRECIOUS",
	".RECURSIVE",
	".SHELL",
	".SILENT",
	".STALE",
	".SUFFIXES",
	".USE",
	".USEBEFORE",
	".WAIT",
};

enum VariableOrderFlag {
	VAR_DEFAULT = 0,
	VAR_CASE_SENSITIVE_SORT = 1 << 0,
	// Lines that are best not wrapped to 80 columns
	VAR_IGNORE_WRAPCOL = 1 << 1,
	VAR_LEAVE_UNFORMATTED = 1 << 2,
	VAR_NOT_COMPARABLE = 1 << 3,
	VAR_PRINT_AS_NEWLINES = 1 << 4,
	// Do not indent with the rest of the variables in a paragraph
	VAR_SKIP_GOALCOL = 1 << 5,
	VAR_SORTED = 1 << 6,
	VAR_SUBPKG_HELPER = 1 << 7,
	VAR_DEDUP = 1 << 8,
};

struct VariableOrderEntry {
	enum BlockType block;
	const char *var;
	enum VariableOrderFlag flags;
	const char *uses[2];
};

// Based on: https://www.freebsd.org/doc/en/books/porters-handbook/porting-order.html
static struct VariableOrderEntry variable_order_[] = {
	{ BLOCK_PORTNAME, "PORTNAME", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "PORTVERSION", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "DISTVERSIONPREFIX", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_PORTNAME, "DISTVERSION", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "DISTVERSIONSUFFIX", VAR_SKIP_GOALCOL, {} },
	/* XXX: hack to fix inserting PORTREVISION in aspell ports */
	{ BLOCK_PORTNAME, "SPELLVERSION", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "PORTREVISION", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "PORTEPOCH", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "CATEGORIES", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "MASTER_SITES", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_PORTNAME, "MASTER_SITE_SUBDIR", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL, {} },
	{ BLOCK_PORTNAME, "PKGNAMEPREFIX", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "PKGNAMESUFFIX", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "DISTNAME", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "EXTRACT_SUFX", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "DISTFILES", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES, {} },
	VAR_FOR_EACH_ARCH(BLOCK_PORTNAME, "DISTFILES_", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL, {}),
	{ BLOCK_PORTNAME, "DIST_SUBDIR", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "EXTRACT_ONLY", VAR_DEFAULT, {} },
	{ BLOCK_PORTNAME, "EXTRACT_ONLY_7z", VAR_SKIP_GOALCOL, {} },

	{ BLOCK_PATCHFILES, "PATCH_SITES", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_PATCHFILES, "PATCHFILES", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_PATCHFILES, "PATCH_DIST_STRIP", VAR_SKIP_GOALCOL, {} },

	{ BLOCK_MAINTAINER, "MAINTAINER", VAR_IGNORE_WRAPCOL, {} },
	{ BLOCK_MAINTAINER, "COMMENT", VAR_IGNORE_WRAPCOL | VAR_SUBPKG_HELPER, {} },

	{ BLOCK_LICENSE, "LICENSE", VAR_SKIP_GOALCOL | VAR_SORTED, {} },
	{ BLOCK_LICENSE, "LICENSE_COMB", VAR_SKIP_GOALCOL | VAR_SORTED, {} },
	{ BLOCK_LICENSE, "LICENSE_GROUPS", VAR_SKIP_GOALCOL | VAR_SORTED, {} },
	{ BLOCK_LICENSE, "LICENSE_NAME", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_LICENSE, "LICENSE_TEXT", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_LICENSE, "LICENSE_FILE", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_LICENSE, "LICENSE_PERMS", VAR_SKIP_GOALCOL | VAR_SORTED, {} },
	{ BLOCK_LICENSE, "LICENSE_DISTFILES", VAR_SKIP_GOALCOL, {} },

	{ BLOCK_LICENSE_OLD, "RESTRICTED", VAR_IGNORE_WRAPCOL, {} },
	{ BLOCK_LICENSE_OLD, "RESTRICTED_FILES", VAR_DEFAULT, {} },
	{ BLOCK_LICENSE_OLD, "NO_CDROM", VAR_IGNORE_WRAPCOL, {} },
	{ BLOCK_LICENSE_OLD, "NO_PACKAGE", VAR_IGNORE_WRAPCOL, {} },
	{ BLOCK_LICENSE_OLD, "LEGAL_PACKAGE", VAR_DEFAULT, {} },
	{ BLOCK_LICENSE_OLD, "LEGAL_TEXT", VAR_IGNORE_WRAPCOL, {} },

	{ BLOCK_BROKEN, "DEPRECATED", VAR_IGNORE_WRAPCOL, {} },
	{ BLOCK_BROKEN, "EXPIRATION_DATE", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_BROKEN, "FORBIDDEN", VAR_IGNORE_WRAPCOL, {} },
	{ BLOCK_BROKEN, "MANUAL_PACKAGE_BUILD", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {} },

	{ BLOCK_BROKEN, "BROKEN", VAR_IGNORE_WRAPCOL, {} },
	VAR_FOR_EACH_ARCH(BLOCK_BROKEN, "BROKEN_", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {}),
	{ BLOCK_BROKEN, "BROKEN_DragonFly", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {} },
	VAR_FOR_EACH_FREEBSD_VERSION_AND_ARCH(BLOCK_BROKEN, "BROKEN_", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {}),
	{ BLOCK_BROKEN, "IGNORE", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {} },
	VAR_FOR_EACH_ARCH(BLOCK_BROKEN, "IGNORE_", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {}),
	{ BLOCK_BROKEN, "IGNORE_DragonFly", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {} },
	VAR_FOR_EACH_FREEBSD_VERSION_AND_ARCH(BLOCK_BROKEN, "IGNORE_", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {}),
	{ BLOCK_BROKEN, "ONLY_FOR_ARCHS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_BROKEN, "ONLY_FOR_ARCHS_REASON", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {} },
	VAR_FOR_EACH_ARCH(BLOCK_BROKEN, "ONLY_FOR_ARCHS_REASON_", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {}),
	{ BLOCK_BROKEN, "NOT_FOR_ARCHS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_BROKEN, "NOT_FOR_ARCHS_REASON", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {} },
	VAR_FOR_EACH_ARCH(BLOCK_BROKEN, "NOT_FOR_ARCHS_REASON_", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, {}),

	{ BLOCK_DEPENDS, "FETCH_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	VAR_FOR_EACH_ARCH(BLOCK_DEPENDS, "FETCH_DEPENDS_", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	{ BLOCK_DEPENDS, "EXTRACT_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	VAR_FOR_EACH_ARCH(BLOCK_DEPENDS, "EXTRACT_DEPENDS_", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	{ BLOCK_DEPENDS, "PATCH_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	VAR_FOR_EACH_ARCH(BLOCK_DEPENDS, "PATCH_DEPENDS_", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	{ BLOCK_DEPENDS, "CRAN_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_DEPENDS, "BUILD_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	VAR_FOR_EACH_ARCH(BLOCK_DEPENDS, "BUILD_DEPENDS_", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	{ BLOCK_DEPENDS, "LIB_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	VAR_FOR_EACH_ARCH(BLOCK_DEPENDS, "LIB_DEPENDS_", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	{ BLOCK_DEPENDS, "RUN_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	VAR_FOR_EACH_ARCH(BLOCK_DEPENDS, "RUN_DEPENDS_", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	{ BLOCK_DEPENDS, "TEST_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	VAR_FOR_EACH_ARCH(BLOCK_DEPENDS, "TEST_DEPENDS_", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_SORTED, {}),
#if PORTFMT_SUBPACKAGES
	{ BLOCK_DEPENDS, "SELF_DEPENDS", VAR_SUBPKG_HELPER | VAR_SORTED, {} },
#endif

	{ BLOCK_FLAVORS, "FLAVORS", VAR_DEFAULT, {} },
	{ BLOCK_FLAVORS, "FLAVOR", VAR_DEFAULT, {} },

#if PORTFMT_SUBPACKAGES
	{ BLOCK_SUBPACKAGES, "SUBPACKAGES", VAR_SORTED, {} },
#endif

	{ BLOCK_FLAVORS_HELPER, "PKGNAMEPREFIX", VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "PKGNAMESUFFIX", VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "PKG_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "EXTRACT_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "PATCH_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "FETCH_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "BUILD_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "LIB_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "RUN_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "TEST_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "CONFLICTS", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "CONFLICTS_BUILD", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "CONFLICTS_INSTALL", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "DESCR", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_FLAVORS_HELPER, "PLIST", VAR_NOT_COMPARABLE, {} },

	{ BLOCK_USES, "USES", VAR_SORTED, {} },
	{ BLOCK_USES, "BROKEN_SSL", VAR_IGNORE_WRAPCOL | VAR_SORTED, { "ssl" } },
	{ BLOCK_USES, "BROKEN_SSL_REASON", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, { "ssl" } },
	VAR_FOR_EACH_SSL(BLOCK_USES, "BROKEN_SSL_REASON_", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, { "ssl" }),
	{ BLOCK_USES, "IGNORE_SSL", VAR_IGNORE_WRAPCOL | VAR_SORTED, { "ssl" } },
	{ BLOCK_USES, "IGNORE_SSL_REASON", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, { "ssl" } },
	VAR_FOR_EACH_SSL(BLOCK_USES, "IGNORE_SSL_REASON_", VAR_IGNORE_WRAPCOL | VAR_SKIP_GOALCOL, { "ssl" }),
	{ BLOCK_USES, "IGNORE_WITH_MYSQL", VAR_SKIP_GOALCOL | VAR_SORTED, { "mysql" } },
	{ BLOCK_USES, "INVALID_BDB_VER", VAR_SKIP_GOALCOL, { "bdb" } },
	{ BLOCK_USES, "OBSOLETE_BDB_VAR", VAR_SKIP_GOALCOL | VAR_SORTED, { "bdb" } },
	{ BLOCK_USES, "WITH_BDB_HIGHEST", VAR_SKIP_GOALCOL, { "bdb" } },
	{ BLOCK_USES, "WITH_BDB6_PERMITTED", VAR_SKIP_GOALCOL, { "bdb" } },
	{ BLOCK_USES, "CPE_PART", VAR_DEFAULT, { "cpe" } },
	{ BLOCK_USES, "CPE_VENDOR", VAR_DEFAULT, { "cpe" } },
	{ BLOCK_USES, "CPE_PRODUCT", VAR_DEFAULT, { "cpe" } },
	{ BLOCK_USES, "CPE_VERSION", VAR_DEFAULT, { "cpe" } },
	{ BLOCK_USES, "CPE_UPDATE", VAR_DEFAULT, { "cpe" } },
	{ BLOCK_USES, "CPE_EDITION", VAR_DEFAULT, { "cpe" } },
	{ BLOCK_USES, "CPE_LANG", VAR_DEFAULT, { "cpe" } },
	{ BLOCK_USES, "CPE_SW_EDITION", VAR_DEFAULT, { "cpe" } },
	{ BLOCK_USES, "CPE_TARGET_SW", VAR_DEFAULT, { "cpe" } },
	{ BLOCK_USES, "CPE_TARGET_HW", VAR_DEFAULT, { "cpe" } },
	{ BLOCK_USES, "CPE_OTHER", VAR_DEFAULT, { "cpe" } },
	{ BLOCK_USES, "DOS2UNIX_REGEX", VAR_SORTED, { "dos2unix" } },
	{ BLOCK_USES, "DOS2UNIX_FILES", VAR_SORTED, { "dos2unix" } },
	{ BLOCK_USES, "DOS2UNIX_GLOB", VAR_SORTED, { "dos2unix" } },
	{ BLOCK_USES, "DOS2UNIX_WRKSRC", VAR_DEFAULT, { "dos2unix" } },
	{ BLOCK_USES, "FONTNAME", VAR_DEFAULT, { "fonts" } },
	{ BLOCK_USES, "FONTSDIR", VAR_DEFAULT, { "fonts" } },
	{ BLOCK_USES, "FONTPATHD", VAR_DEFAULT, { "fonts" } },
	{ BLOCK_USES, "FONTPATHSPEC", VAR_DEFAULT, { "fonts" } },
	{ BLOCK_USES, "KMODDIR", VAR_DEFAULT, { "kmod" } },
	{ BLOCK_USES, "KERN_DEBUGDIR", VAR_DEFAULT, { "kmod" } },
	{ BLOCK_USES, "NCURSES_IMPL", VAR_DEFAULT, { "ncurses" } },
	{ BLOCK_USES, "PATHFIX_CMAKELISTSTXT", VAR_SKIP_GOALCOL | VAR_SORTED, { "pathfix" } },
	{ BLOCK_USES, "PATHFIX_MAKEFILEIN", VAR_SKIP_GOALCOL | VAR_SORTED, { "pathfix" } },
	{ BLOCK_USES, "PATHFIX_WRKSRC", VAR_DEFAULT, { "pathfix" } },
	{ BLOCK_USES, "QMAIL_PREFIX", VAR_DEFAULT, { "qmail" } },
	{ BLOCK_USES, "QMAIL_SLAVEPORT", VAR_DEFAULT, { "qmail" } },
	{ BLOCK_USES, "WANT_PGSQL", VAR_SORTED, { "pgsql" } },
	{ BLOCK_USES, "USE_ANT", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_ASDF", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_ASDF_FASL", VAR_DEFAULT, {} },
	{ BLOCK_USES, "FASL_BUILD", VAR_DEFAULT, {} },
	{ BLOCK_USES, "ASDF_MODULES", VAR_SORTED, {} },
	{ BLOCK_USES, "USE_BINUTILS", VAR_SORTED, {} },
	{ BLOCK_USES, "USE_CLISP", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_CSTD", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_CXXSTD", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_FPC", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_GCC", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_GECKO", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_GENERIC_PKGMESSAGE", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_GITHUB", VAR_DEFAULT, {} },
	{ BLOCK_USES, "GH_ACCOUNT", VAR_DEFAULT, {} },
	{ BLOCK_USES, "GH_PROJECT", VAR_DEFAULT, {} },
	{ BLOCK_USES, "GH_SUBDIR", VAR_DEFAULT, {} },
	{ BLOCK_USES, "GH_TAGNAME", VAR_DEFAULT, {} },
	{ BLOCK_USES, "GH_TUPLE", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_USES, "USE_GITLAB", VAR_DEFAULT, {} },
	{ BLOCK_USES, "GL_SITE", VAR_DEFAULT, {} },
	{ BLOCK_USES, "GL_ACCOUNT", VAR_DEFAULT, {} },
	{ BLOCK_USES, "GL_PROJECT", VAR_DEFAULT, {} },
	{ BLOCK_USES, "GL_COMMIT", VAR_DEFAULT, {} },
	{ BLOCK_USES, "GL_SUBDIR", VAR_DEFAULT, {} },
	{ BLOCK_USES, "GL_TUPLE", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_USES, "USE_GL", VAR_SORTED, { "gl" } },
	{ BLOCK_USES, "USE_GNOME", VAR_SORTED, { "gnome" } },
	{ BLOCK_USES, "USE_GNOME_SUBR", VAR_DEFAULT, { "gnome" } },
	{ BLOCK_USES, "GCONF_SCHEMAS", VAR_SORTED, { "gnome" } },
	{ BLOCK_USES, "GLIB_SCHEMAS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, { "gnome" } },
	{ BLOCK_USES, "GNOME_LOCALSTATEDIR", VAR_SKIP_GOALCOL, { "gnome" } },
	{ BLOCK_USES, "INSTALLS_ICONS", VAR_DEFAULT, { "gnome" } },
	{ BLOCK_USES, "INSTALLS_OMF", VAR_DEFAULT, { "gnome" } },
	{ BLOCK_USES, "USE_GNUSTEP", VAR_SORTED, { "gnustep" } },
	{ BLOCK_USES, "GNUSTEP_PREFIX", VAR_DEFAULT, { "gnustep" } },
	{ BLOCK_USES, "DEFAULT_LIBVERSION", VAR_DEFAULT, { "gnustep" } },
	{ BLOCK_USES, "ADDITIONAL_CFLAGS", VAR_DEFAULT, { "gnustep" } },
	{ BLOCK_USES, "ADDITIONAL_CPPFLAGS", VAR_DEFAULT, { "gnustep" } },
	{ BLOCK_USES, "ADDITIONAL_CXXFLAGS", VAR_DEFAULT, { "gnustep" } },
	{ BLOCK_USES, "ADDITIONAL_OBJCCFLAGS", VAR_DEFAULT, { "gnustep" } },
	{ BLOCK_USES, "ADDITIONAL_OBJCFLAGS", VAR_DEFAULT, { "gnustep" } },
	{ BLOCK_USES, "ADDITIONAL_LDFLAGS", VAR_DEFAULT, { "gnustep" } },
	{ BLOCK_USES, "ADDITIONAL_FLAGS", VAR_DEFAULT, { "gnustep" } },
	{ BLOCK_USES, "ADDITIONAL_INCLUDE_DIRS", VAR_SORTED, { "gnustep" } },
	{ BLOCK_USES, "ADDITIONAL_LIB_DIRS", VAR_SORTED, { "gnustep" } },
	{ BLOCK_USES, "USE_GSTREAMER", VAR_SORTED, {} },
	{ BLOCK_USES, "USE_GSTREAMER1", VAR_SORTED, {} },
	{ BLOCK_USES, "USE_HORDE_BUILD", VAR_SKIP_GOALCOL, { "horde" } },
	{ BLOCK_USES, "USE_HORDE_RUN", VAR_DEFAULT, { "horde" } },
	{ BLOCK_USES, "HORDE_DIR", VAR_DEFAULT, { "horde" } },
	{ BLOCK_USES, "USE_JAVA", VAR_DEFAULT, {} },
	{ BLOCK_USES, "JAVA_VERSION", VAR_DEFAULT, {} },
	{ BLOCK_USES, "JAVA_OS", VAR_DEFAULT, {} },
	{ BLOCK_USES, "JAVA_VENDOR", VAR_DEFAULT, {} },
	{ BLOCK_USES, "JAVA_EXTRACT", VAR_DEFAULT, {} },
	{ BLOCK_USES, "JAVA_BUILD", VAR_DEFAULT, {} },
	{ BLOCK_USES, "JAVA_RUN", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_KDE", VAR_SORTED, { "kde" } },
	{ BLOCK_USES, "KDE_INVENT", VAR_DEFAULT, { "kde" } },
	{ BLOCK_USES, "KDE_PLASMA_VERSION", VAR_SKIP_GOALCOL, { "kde" } },
	{ BLOCK_USES, "KDE_PLASMA_BRANCH", VAR_SKIP_GOALCOL, { "kde" } },
	{ BLOCK_USES, "KDE_FRAMEWORKS_VERSION", VAR_SKIP_GOALCOL, { "kde" } },
	{ BLOCK_USES, "KDE_FRAMEWORKS_BRANCH", VAR_SKIP_GOALCOL, { "kde" } },
	{ BLOCK_USES, "KDE_APPLICATIONS_VERSION", VAR_SKIP_GOALCOL, { "kde" } },
	{ BLOCK_USES, "KDE_APPLICATIONS_SHLIB_VER", VAR_SKIP_GOALCOL, { "kde" } },
	{ BLOCK_USES, "KDE_APPLICATIONS_BRANCH", VAR_SKIP_GOALCOL, { "kde" } },
	{ BLOCK_USES, "CALLIGRA_VERSION", VAR_SKIP_GOALCOL, { "kde" } },
	{ BLOCK_USES, "CALLIGRA_BRANCH", VAR_SKIP_GOALCOL, { "kde" } },
	{ BLOCK_USES, "USE_LDCONFIG", VAR_SORTED, {} },
	{ BLOCK_USES, "USE_LDCONFIG32", VAR_SORTED, {} },
	{ BLOCK_USES, "USE_LINUX", VAR_SORTED, { "linux" } },
	{ BLOCK_USES, "USE_LINUX_PREFIX", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_LINUX_RPM", VAR_SKIP_GOALCOL, { "linux" } },
	{ BLOCK_USES, "USE_LINUX_RPM_BAD_PERMS", VAR_SKIP_GOALCOL, { "linux" } },
	{ BLOCK_USES, "USE_LOCALE", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_LXQT", VAR_SORTED, { "lxqt" } },
	{ BLOCK_USES, "USE_MATE", VAR_SORTED, { "mate" } },
	{ BLOCK_USES, "USE_MOZILLA", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_MYSQL", VAR_DEFAULT, { "mysql" } },
	{ BLOCK_USES, "USE_OCAML", VAR_DEFAULT, {} },
	{ BLOCK_USES, "NO_OCAML_BUILDDEPENDS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "NO_OCAML_RUNDEPENDS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_OCAML_FINDLIB", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_OCAML_CAMLP4", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_OCAML_TK", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "NO_OCAMLTK_BUILDDEPENDS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "NO_OCAMLTK_RUNDEPENDS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_OCAML_LDCONFIG", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_OCAMLFIND_PLIST", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_OCAML_WASH", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "OCAML_PKGDIRS", VAR_SKIP_GOALCOL | VAR_SORTED, {} },
	{ BLOCK_USES, "OCAML_LDLIBS", VAR_SORTED, {} },
	{ BLOCK_USES, "USE_OPENLDAP", VAR_DEFAULT, {} },
	{ BLOCK_USES, "WANT_OPENLDAP_SASL", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "WANT_OPENLDAP_VER", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_PERL5", VAR_SORTED, { "perl5" } },
	{ BLOCK_USES, "USE_PHP", VAR_SORTED, { "php" } },
	{ BLOCK_USES, "IGNORE_WITH_PHP", VAR_SKIP_GOALCOL, { "php" } },
	{ BLOCK_USES, "PHP_MODNAME", VAR_DEFAULT, { "php" } },
	{ BLOCK_USES, "PHP_MOD_PRIO", VAR_DEFAULT, { "php" } },
	{ BLOCK_USES, "PEAR_CHANNEL", VAR_DEFAULT, { "pear" } },
	{ BLOCK_USES, "PEAR_CHANNEL_VER", VAR_SKIP_GOALCOL, { "pear" } },
	{ BLOCK_USES, "USE_PYQT", VAR_SORTED, { "pyqt" } },
	{ BLOCK_USES, "PYQT_DIST", VAR_DEFAULT, { "pyqt" } },
	{ BLOCK_USES, "PYQT_SIPDIR", VAR_DEFAULT, { "pyqt" } },
	{ BLOCK_USES, "USE_PYTHON", VAR_SORTED, { "python", "waf" } },
	{ BLOCK_USES, "PYTHON_NO_DEPENDS", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYTHON_CMD", VAR_DEFAULT, { "python", "waf" } },
	{ BLOCK_USES, "PYSETUP", VAR_DEFAULT, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_SETUP", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_CONFIGURE_TARGET", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_BUILD_TARGET", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_INSTALL_TARGET", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_CONFIGUREARGS", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_BUILDARGS", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_INSTALLARGS", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_INSTALLNOSINGLE", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_PKGNAME", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_PKGVERSION", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_EGGINFO", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "PYDISTUTILS_EGGINFODIR", VAR_SKIP_GOALCOL, { "python", "waf" } },
	{ BLOCK_USES, "USE_QT", VAR_SORTED, { "qt", "qt-dist" } },
	{ BLOCK_USES, "QT_BINARIES", VAR_DEFAULT, { "qt", "qt-dist" } },
	{ BLOCK_USES, "QT_CONFIG", VAR_DEFAULT, { "qt", "qt-dist" } },
	{ BLOCK_USES, "QT_DEFINES", VAR_DEFAULT, { "qt", "qt-dist" } },
	{ BLOCK_USES, "QT5_VERSION", VAR_DEFAULT, { "qt", "qt-dist" } },
	{ BLOCK_USES, "USE_RC_SUBR", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_RUBY", VAR_DEFAULT, {} },
	VAR_BROKEN_RUBY(BLOCK_USES, VAR_IGNORE_WRAPCOL, {}),
	{ BLOCK_USES, "RUBY_NO_BUILD_DEPENDS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "RUBY_NO_RUN_DEPENDS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_RUBY_EXTCONF", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "RUBY_EXTCONF", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "RUBY_EXTCONF_SUBDIRS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_RUBY_SETUP", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "RUBY_SETUP", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_RUBY_RDOC", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "RUBY_REQUIRE", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_RUBYGEMS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_USES, "USE_SBCL", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_SDL", VAR_SORTED, { "sdl" } },
	{ BLOCK_USES, "USE_SM_COMPAT", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_SUBMAKE", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_TEX", VAR_SORTED, {} },
	{ BLOCK_USES, "USE_WX", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_WX_NOT", VAR_DEFAULT, {} },
	{ BLOCK_USES, "WANT_WX", VAR_DEFAULT, {} },
	{ BLOCK_USES, "WANT_WX_VER", VAR_DEFAULT, {} },
	{ BLOCK_USES, "WITH_WX_VER", VAR_DEFAULT, {} },
	{ BLOCK_USES, "WX_COMPS", VAR_SORTED, {} },
	{ BLOCK_USES, "WX_CONF_ARGS", VAR_DEFAULT, {} },
	{ BLOCK_USES, "WX_PREMK", VAR_DEFAULT, {} },
	{ BLOCK_USES, "USE_XFCE", VAR_SORTED, { "xfce" } },
	{ BLOCK_USES, "USE_XORG", VAR_SORTED, { "xorg", "motif" } },
	{ BLOCK_USES, "WAF_CMD", VAR_DEFAULT, { "waf" } },

	{ BLOCK_SHEBANGFIX, "SHEBANG_FILES", VAR_SORTED, { "shebangfix" } },
	{ BLOCK_SHEBANGFIX, "SHEBANG_GLOB", VAR_SORTED, { "shebangfix" } },
	{ BLOCK_SHEBANGFIX, "SHEBANG_REGEX", VAR_SORTED, { "shebangfix" } },
	{ BLOCK_SHEBANGFIX, "SHEBANG_LANG", VAR_SORTED, { "shebangfix" } },
	{ BLOCK_SHEBANGFIX, "OLD_CMD", VAR_NOT_COMPARABLE, { "shebangfix" } },
	{ BLOCK_SHEBANGFIX, "CMD", VAR_NOT_COMPARABLE, { "shebangfix" } },

	{ BLOCK_UNIQUEFILES, "UNIQUE_PREFIX", VAR_DEFAULT, { "uniquefiles" } },
	{ BLOCK_UNIQUEFILES, "UNIQUE_PREFIX_FILES", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_SORTED, { "uniquefiles" } },
	{ BLOCK_UNIQUEFILES, "UNIQUE_SUFFIX", VAR_DEFAULT, { "uniquefiles" } },
	{ BLOCK_UNIQUEFILES, "UNIQUE_SUFFIX_FILES", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_SORTED, { "uniquefiles" } },

	{ BLOCK_APACHE, "AP_EXTRAS", VAR_DEFAULT, { "apache" } },
	{ BLOCK_APACHE, "AP_INC", VAR_DEFAULT, { "apache" } },
	{ BLOCK_APACHE, "AP_LIB", VAR_DEFAULT, { "apache" } },
	{ BLOCK_APACHE, "AP_FAST_BUILD", VAR_DEFAULT, { "apache" } },
	{ BLOCK_APACHE, "AP_GENPLIST", VAR_DEFAULT, { "apache" } },
	{ BLOCK_APACHE, "MODULENAME", VAR_DEFAULT, { "apache" } },
	{ BLOCK_APACHE, "SHORTMODNAME", VAR_DEFAULT, { "apache" } },
	{ BLOCK_APACHE, "SRC_FILE", VAR_DEFAULT, { "apache" } },

	{ BLOCK_ELIXIR, "ELIXIR_APP_NAME", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "ELIXIR_LIB_ROOT", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "ELIXIR_APP_ROOT", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "ELIXIR_HIDDEN", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "ELIXIR_LOCALE", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_CMD", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_COMPILE", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_REWRITE", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_BUILD_DEPS", VAR_SORTED, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_RUN_DEPS", VAR_SORTED, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_DOC_DIRS", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_DOC_FILES", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_ENV", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_ENV_NAME", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_BUILD_NAME", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_TARGET", VAR_DEFAULT, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_EXTRA_APPS", VAR_SORTED, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_EXTRA_DIRS", VAR_SORTED, { "elixir" } },
	{ BLOCK_ELIXIR, "MIX_EXTRA_FILES", VAR_SORTED, { "elixir" } },

	{ BLOCK_EMACS, "EMACS_FLAVORS_EXCLUDE", VAR_DEFAULT, { "emacs" } },
	{ BLOCK_EMACS, "EMACS_NO_DEPENDS", VAR_DEFAULT, { "emacs" } },

	{ BLOCK_ERLANG, "ERL_APP_NAME", VAR_DEFAULT, { "erlang" } },
	{ BLOCK_ERLANG, "ERL_APP_ROOT", VAR_DEFAULT, { "erlang" } },
	{ BLOCK_ERLANG, "REBAR_CMD", VAR_DEFAULT, { "erlang" } },
	{ BLOCK_ERLANG, "REBAR3_CMD", VAR_DEFAULT, { "erlang" } },
	{ BLOCK_ERLANG, "REBAR_PROFILE", VAR_DEFAULT, { "erlang" } },
	{ BLOCK_ERLANG, "REBAR_TARGETS", VAR_SORTED, { "erlang" } },
	{ BLOCK_ERLANG, "ERL_BUILD_NAME", VAR_DEFAULT, { "erlang" } },
	{ BLOCK_ERLANG, "ERL_BUILD_DEPS", VAR_SORTED, { "erlang" } },
	{ BLOCK_ERLANG, "ERL_RUN_DEPS", VAR_SORTED, { "erlang" } },
	{ BLOCK_ERLANG, "ERL_DOCS", VAR_DEFAULT, { "erlang" } },

	{ BLOCK_CMAKE, "CMAKE_ARGS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, { "cmake" } },
	{ BLOCK_CMAKE, "CMAKE_ON", VAR_SORTED, { "cmake" } },
	{ BLOCK_CMAKE, "CMAKE_OFF", VAR_SORTED, { "cmake" } },
	{ BLOCK_CMAKE, "CMAKE_TESTING_ARGS", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_SORTED, { "cmake" } },
	{ BLOCK_CMAKE, "CMAKE_TESTING_ON", VAR_SKIP_GOALCOL | VAR_SORTED, { "cmake" } },
	{ BLOCK_CMAKE, "CMAKE_TESTING_OFF", VAR_SKIP_GOALCOL | VAR_SORTED, { "cmake" } },
	{ BLOCK_CMAKE, "CMAKE_TESTING_TARGET", VAR_SKIP_GOALCOL | VAR_SORTED, { "cmake" } },
	{ BLOCK_CMAKE, "CMAKE_BUILD_TYPE", VAR_SKIP_GOALCOL, { "cmake" } },
	{ BLOCK_CMAKE, "CMAKE_INSTALL_PREFIX", VAR_SKIP_GOALCOL, { "cmake" } },
	{ BLOCK_CMAKE, "CMAKE_SOURCE_PATH", VAR_SKIP_GOALCOL, { "cmake" } },

	{ BLOCK_CONFIGURE, "HAS_CONFIGURE", VAR_DEFAULT, {} },
	{ BLOCK_CONFIGURE, "GNU_CONFIGURE", VAR_DEFAULT, {} },
	{ BLOCK_CONFIGURE, "GNU_CONFIGURE_PREFIX", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_CONFIGURE, "CONFIGURE_CMD", VAR_DEFAULT, {} },
	{ BLOCK_CONFIGURE, "CONFIGURE_LOG", VAR_DEFAULT, {} },
	{ BLOCK_CONFIGURE, "CONFIGURE_SCRIPT", VAR_DEFAULT, {} },
	{ BLOCK_CONFIGURE, "CONFIGURE_SHELL", VAR_DEFAULT, {} },
	{ BLOCK_CONFIGURE, "CONFIGURE_ARGS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_CONFIGURE, "CONFIGURE_ENV", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_CONFIGURE, "CONFIGURE_OUTSOURCE", VAR_DEFAULT, {} },
	{ BLOCK_CONFIGURE, "CONFIGURE_TARGET", VAR_DEFAULT, {} },
	{ BLOCK_CONFIGURE, "WITHOUT_FBSD10_FIX", VAR_SKIP_GOALCOL, {} },

	{ BLOCK_QMAKE, "QMAKE_ARGS", VAR_SORTED, { "qmake" } },
	{ BLOCK_QMAKE, "QMAKE_ENV", VAR_SORTED, { "qmake" } },
	{ BLOCK_QMAKE, "QMAKE_CONFIGURE_ARGS", VAR_SORTED, { "qmake" } },
	{ BLOCK_QMAKE, "QMAKE_SOURCE_PATH", VAR_DEFAULT, { "qmake" } },

	{ BLOCK_MESON, "MESON_ARGS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, { "meson" } },
	{ BLOCK_MESON, "MESON_BUILD_DIR", VAR_DEFAULT, { "meson" } },

	{ BLOCK_SCONS, "CCFLAGS", VAR_DEFAULT, { "scons" } },
	{ BLOCK_SCONS, "CPPPATH", VAR_SORTED, { "scons" } },
	{ BLOCK_SCONS, "LINKFLAGS", VAR_DEFAULT, { "scons" } },
	{ BLOCK_SCONS, "LIBPATH", VAR_DEFAULT, { "scons" } },

	{ BLOCK_CABAL, "USE_CABAL", VAR_CASE_SENSITIVE_SORT | VAR_PRINT_AS_NEWLINES | VAR_SORTED, { "cabal" } },
	{ BLOCK_CABAL, "CABAL_BOOTSTRAP", VAR_SKIP_GOALCOL, { "cabal" } },
	{ BLOCK_CABAL, "CABAL_FLAGS", VAR_DEFAULT, { "cabal" } },
	{ BLOCK_CABAL, "EXECUTABLES", VAR_SORTED, { "cabal" } },
	{ BLOCK_CABAL, "DATADIR_VARS", VAR_NOT_COMPARABLE | VAR_SKIP_GOALCOL | VAR_SORTED, { "cabal" } },
	{ BLOCK_CABAL, "SKIP_CABAL_PLIST", VAR_SKIP_GOALCOL | VAR_SORTED, { "cabal" } },

	{ BLOCK_CARGO, "CARGO_CRATES", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_USE_GITHUB", VAR_DEFAULT, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_USE_GITLAB", VAR_DEFAULT, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_GIT_SUBDIR", VAR_PRINT_AS_NEWLINES | VAR_SORTED, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_CARGOLOCK", VAR_SORTED, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_CARGOTOML", VAR_SORTED, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_FEATURES", VAR_SORTED, { "cargo" } },

	{ BLOCK_CARGO, "CARGO_BUILDDEP", VAR_DEFAULT, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_BUILD", VAR_DEFAULT, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_BUILD_ARGS", VAR_SORTED, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_INSTALL", VAR_DEFAULT, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_INSTALL_ARGS", VAR_SORTED, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_INSTALL_PATH", VAR_DEFAULT, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_TEST", VAR_DEFAULT, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_TEST_ARGS", VAR_SORTED, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_UPDATE_ARGS", VAR_SORTED, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_CARGO_BIN", VAR_DEFAULT, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_DIST_SUBDIR", VAR_DEFAULT, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_ENV", VAR_PRINT_AS_NEWLINES | VAR_SORTED, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_TARGET_DIR", VAR_DEFAULT, { "cargo" } },
	{ BLOCK_CARGO, "CARGO_VENDOR_DIR", VAR_DEFAULT, { "cargo" } },

	{ BLOCK_GO, "GO_MODULE", VAR_DEFAULT, { "go" } },
	{ BLOCK_GO, "GO_PKGNAME", VAR_DEFAULT, { "go" } },
	{ BLOCK_GO, "GO_TARGET", VAR_SORTED, { "go" } },
	{ BLOCK_GO, "GO_BUILDFLAGS", VAR_LEAVE_UNFORMATTED, { "go" } },
	{ BLOCK_GO, "GO_TESTTARGET", VAR_DEFAULT, { "go" } },
	{ BLOCK_GO, "GO_TESTFLAGS", VAR_LEAVE_UNFORMATTED, { "go" } },
	{ BLOCK_GO, "CGO_ENABLED", VAR_DEFAULT, { "go" } },
	{ BLOCK_GO, "CGO_CFLAGS", VAR_SORTED, { "go" } },
	{ BLOCK_GO, "CGO_LDFLAGS", VAR_DEFAULT, { "go" } },

	{ BLOCK_LAZARUS, "NO_LAZBUILD", VAR_DEFAULT, { "lazarus" } },
	{ BLOCK_LAZARUS, "LAZARUS_PROJECT_FILES", VAR_DEFAULT, { "lazarus" } },
	{ BLOCK_LAZARUS, "LAZARUS_DIR", VAR_DEFAULT, { "lazarus" } },
	{ BLOCK_LAZARUS, "LAZBUILD_ARGS", VAR_SORTED, { "lazarus" } },
	{ BLOCK_LAZARUS, "LAZARUS_NO_FLAVORS", VAR_DEFAULT, { "lazarus" } },

	{ BLOCK_LINUX, "BIN_DISTNAMES", VAR_DEFAULT, { "linux" } },
	{ BLOCK_LINUX, "LIB_DISTNAMES", VAR_DEFAULT, { "linux" } },
	{ BLOCK_LINUX, "SHARE_DISTNAMES", VAR_DEFAULT, { "linux" } },
	{ BLOCK_LINUX, "SRC_DISTFILES", VAR_DEFAULT, { "linux" } },

	{ BLOCK_NUGET, "NUGET_DEPENDS", VAR_SORTED, { "mono" } },
	{ BLOCK_NUGET, "NUGET_PACKAGEDIR", VAR_DEFAULT, { "mono" } },
	{ BLOCK_NUGET, "NUGET_LAYOUT", VAR_DEFAULT, { "mono" } },
	{ BLOCK_NUGET, "NUGET_FEEDS", VAR_DEFAULT, { "mono" } },
	// TODO: These need to be handled specially
	//{ BLOCK_NUGET, "_URL", VAR_DEFAULT, { "mono" } },
	//{ BLOCK_NUGET, "_FILE", VAR_DEFAULT, { "mono" } },
	//{ BLOCK_NUGET, "_DEPENDS", VAR_DEFAULT, { "mono" } },
	{ BLOCK_NUGET, "PAKET_PACKAGEDIR", VAR_DEFAULT, { "mono" } },
	{ BLOCK_NUGET, "PAKET_DEPENDS", VAR_SORTED, { "mono" } },

	{ BLOCK_MAKE, "MAKEFILE", VAR_DEFAULT, {} },
	{ BLOCK_MAKE, "MAKE_CMD", VAR_DEFAULT, {} },
	{ BLOCK_MAKE, "MAKE_ARGS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	// MAKE_ARGS_arch/gcc/clang is not a framework
	// but is in common use so list it here too.
	{ BLOCK_MAKE, "MAKE_ARGS_clang", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_MAKE, "MAKE_ARGS_gcc", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	VAR_FOR_EACH_ARCH(BLOCK_MAKE, "MAKE_ARGS_", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {}),
	{ BLOCK_MAKE, "MAKE_ENV", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_MAKE, "MAKE_ENV_clang", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_MAKE, "MAKE_ENV_gcc", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	VAR_FOR_EACH_ARCH(BLOCK_MAKE, "MAKE_ENV_", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {}),
	{ BLOCK_MAKE, "SCRIPTS_ENV", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_MAKE, "DESTDIRNAME", VAR_DEFAULT, {} },
	{ BLOCK_MAKE, "MAKE_FLAGS", VAR_DEFAULT, {} },
	{ BLOCK_MAKE, "MAKE_JOBS_UNSAFE", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_MAKE, "ALL_TARGET", VAR_DEFAULT, {} },
	{ BLOCK_MAKE, "INSTALL_TARGET", VAR_DEFAULT, {} },
	{ BLOCK_MAKE, "TEST_ARGS", VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_MAKE, "TEST_ENV", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_MAKE, "TEST_TARGET", VAR_DEFAULT, {} },
	{ BLOCK_MAKE, "DO_MAKE_BUILD", VAR_IGNORE_WRAPCOL, {} },
	{ BLOCK_MAKE, "DO_MAKE_TEST", VAR_IGNORE_WRAPCOL, {} },

	{ BLOCK_CFLAGS, "CFLAGS", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "CFLAGS_clang", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "CFLAGS_gcc", VAR_DEFAULT, {} },
	VAR_FOR_EACH_ARCH(BLOCK_CFLAGS, "CFLAGS_", VAR_DEFAULT, {}),
	{ BLOCK_CFLAGS, "CPPFLAGS", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "CPPFLAGS_clang", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "CPPFLAGS_gcc", VAR_DEFAULT, {} },
	VAR_FOR_EACH_ARCH(BLOCK_CFLAGS, "CPPFLAGS_", VAR_DEFAULT, {}),
	{ BLOCK_CFLAGS, "CXXFLAGS", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "CXXFLAGS_clang", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "CXXFLAGS_gcc", VAR_DEFAULT, {} },
	VAR_FOR_EACH_ARCH(BLOCK_CFLAGS, "CXXFLAGS_", VAR_DEFAULT, {}),
	{ BLOCK_CFLAGS, "FFLAGS", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "FCFLAGS", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "RUSTFLAGS", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "LDFLAGS", VAR_DEFAULT, {} },
	VAR_FOR_EACH_ARCH(BLOCK_CFLAGS, "LDFLAGS_", VAR_DEFAULT, {}),
	{ BLOCK_CFLAGS, "LIBS", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "LLD_UNSAFE", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "SSP_UNSAFE", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "SSP_CFLAGS", VAR_DEFAULT, {} },
	{ BLOCK_CFLAGS, "WITHOUT_CPU_CFLAGS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_CFLAGS, "WITHOUT_NO_STRICT_ALIASING", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_CFLAGS, "WITHOUT_SSP", VAR_DEFAULT, {} },

	{ BLOCK_CONFLICTS, "CONFLICTS", VAR_SORTED, {} },
	{ BLOCK_CONFLICTS, "CONFLICTS_BUILD", VAR_SORTED, {} },
	{ BLOCK_CONFLICTS, "CONFLICTS_INSTALL", VAR_SORTED, {} },

	{ BLOCK_STANDARD, "AR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "AS", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "CC", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "CPP", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "CXX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "LD", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "STRIP", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "ETCDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "ETCDIR_REL", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "DATADIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "DATADIR_REL", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "DOCSDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "DOCSDIR_REL", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "EXAMPLESDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "FILESDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MASTERDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MANDIRS", VAR_SORTED, {} },
	{ BLOCK_STANDARD, "MANPREFIX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MAN1PREFIX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MAN2PREFIX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MAN3PREFIX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MAN4PREFIX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MAN5PREFIX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MAN6PREFIX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MAN7PREFIX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MAN8PREFIX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MAN9PREFIX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "PATCHDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "PKGDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "SCRIPTDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "STAGEDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "SRC_BASE", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "TMPDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "WWWDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "WWWDIR_REL", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "BINARY_ALIAS", VAR_SORTED, {} },
	{ BLOCK_STANDARD, "BINARY_WRAPPERS", VAR_SKIP_GOALCOL | VAR_SORTED, {} },
	{ BLOCK_STANDARD, "BINMODE", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MANMODE", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "_SHAREMODE", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "BUNDLE_LIBS", VAR_SORTED, {} },
	{ BLOCK_STANDARD, "DESKTOP_ENTRIES", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL, {} },
	{ BLOCK_STANDARD, "DESKTOPDIR", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "EXTRA_PATCHES", VAR_DEFAULT, {} },
	VAR_FOR_EACH_ARCH(BLOCK_STANDARD, "EXTRA_PATCHES_", VAR_DEFAULT, {}),
	{ BLOCK_STANDARD, "EXTRACT_CMD", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "EXTRACT_BEFORE_ARGS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_STANDARD, "EXTRACT_AFTER_ARGS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_STANDARD, "FETCH_CMD", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "FETCH_ARGS", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "FETCH_REGET", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "FETCH_ENV", VAR_SORTED, {} },
	{ BLOCK_STANDARD, "FETCH_BEFORE_ARGS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_STANDARD, "FETCH_AFTER_ARGS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_STANDARD, "PATCH_STRIP", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "PATCH_ARGS", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "PATCH_DIST_ARGS", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "REINPLACE_CMD", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "REINPLACE_ARGS", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "DISTORIG", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "IA32_BINARY_PORT", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "IS_INTERACTIVE", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "NO_ARCH", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "NO_ARCH_IGNORE", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "NO_BUILD", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "NOCCACHE", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "NO_CCACHE", VAR_IGNORE_WRAPCOL, {} },
	{ BLOCK_STANDARD, "NO_CHECKSUM", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "NO_INSTALL", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "NO_MTREE", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "NOT_REPRODUCIBLE", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_STANDARD, "MASTER_SORT", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MASTER_SORT_REGEX", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MTREE_CMD", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MTREE_ARGS", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "MTREE_FILE", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "NOPRECIOUSMAKEVARS", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_STANDARD, "NO_TEST", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "PORTSCOUT", VAR_DEFAULT, {} },
	{ BLOCK_STANDARD, "SUB_FILES", VAR_SORTED, {} },
	{ BLOCK_STANDARD, "SUB_LIST", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_STANDARD, "TARGET_ORDER_OVERRIDE", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_STANDARD, "UID_FILES", VAR_SORTED, {} },

	{ BLOCK_WRKSRC, "NO_WRKSUBDIR", VAR_DEFAULT, {} },
	{ BLOCK_WRKSRC, "AUTORECONF_WRKSRC", VAR_DEFAULT, {} },
	{ BLOCK_WRKSRC, "BUILD_WRKSRC", VAR_DEFAULT, {} },
	{ BLOCK_WRKSRC, "CONFIGURE_WRKSRC", VAR_DEFAULT, {} },
	{ BLOCK_WRKSRC, "INSTALL_WRKSRC", VAR_DEFAULT, {} },
	{ BLOCK_WRKSRC, "PATCH_WRKSRC", VAR_DEFAULT, {} },
	{ BLOCK_WRKSRC, "TEST_WRKSRC", VAR_DEFAULT, {} },
	{ BLOCK_WRKSRC, "WRKDIR", VAR_DEFAULT, {} },
	{ BLOCK_WRKSRC, "WRKSRC", VAR_DEFAULT, {} },
	{ BLOCK_WRKSRC, "WRKSRC_SUBDIR", VAR_DEFAULT, {} },

	{ BLOCK_USERS, "USERS", VAR_SORTED, {} },
	{ BLOCK_USERS, "GROUPS", VAR_SORTED, {} },

	{ BLOCK_PLIST, "DESCR", VAR_SUBPKG_HELPER, {} },
	{ BLOCK_PLIST, "DISTINFO_FILE", VAR_DEFAULT, {} },
	{ BLOCK_PLIST, "PKGHELP", VAR_DEFAULT, {} },
	{ BLOCK_PLIST, "PKGPREINSTALL", VAR_SUBPKG_HELPER, {} },
	{ BLOCK_PLIST, "PKGINSTALL", VAR_SUBPKG_HELPER, {} },
	{ BLOCK_PLIST, "PKGPOSTINSTALL", VAR_SUBPKG_HELPER, {} },
	{ BLOCK_PLIST, "PKGPREDEINSTALL", VAR_SUBPKG_HELPER, {} },
	{ BLOCK_PLIST, "PKGDEINSTALL", VAR_SUBPKG_HELPER, {} },
	{ BLOCK_PLIST, "PKGPOSTDEINSTALL", VAR_SUBPKG_HELPER, {} },
	{ BLOCK_PLIST, "PKGMESSAGE", VAR_SUBPKG_HELPER, {} },
	{ BLOCK_PLIST, "PKG_DBDIR", VAR_DEFAULT, {} },
	{ BLOCK_PLIST, "PKG_SUFX", VAR_DEFAULT, {} },
	{ BLOCK_PLIST, "PLIST", VAR_DEFAULT, {} },
	{ BLOCK_PLIST, "POST_PLIST", VAR_DEFAULT, {} },
	{ BLOCK_PLIST, "TMPPLIST", VAR_DEFAULT, {} },
	{ BLOCK_PLIST, "INFO", VAR_DEFAULT, {} },
	{ BLOCK_PLIST, "INFO_PATH", VAR_DEFAULT, {} },
	{ BLOCK_PLIST, "PLIST_DIRS", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_PLIST, "PLIST_FILES", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_PLIST, "PLIST_SUB", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_PLIST, "PORTDATA", VAR_CASE_SENSITIVE_SORT | VAR_SORTED, {} },
	{ BLOCK_PLIST, "PORTDOCS", VAR_CASE_SENSITIVE_SORT | VAR_SORTED, {} },
	{ BLOCK_PLIST, "PORTEXAMPLES", VAR_CASE_SENSITIVE_SORT | VAR_SORTED, {} },

	{ BLOCK_OPTDEF, "OPTIONS_DEFINE", VAR_SORTED, {} },
	// These do not exist in the framework but some ports
	// define them themselves
	{ BLOCK_OPTDEF, "OPTIONS_DEFINE_DragonFly", VAR_SKIP_GOALCOL | VAR_SORTED, {} },
	VAR_FOR_EACH_FREEBSD_VERSION(BLOCK_OPTDEF, "OPTIONS_DEFINE_", VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	VAR_FOR_EACH_ARCH(BLOCK_OPTDEF, "OPTIONS_DEFINE_", VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	{ BLOCK_OPTDEF, "OPTIONS_DEFAULT", VAR_SORTED, {} },
	{ BLOCK_OPTDEF, "OPTIONS_DEFAULT_DragonFly", VAR_SKIP_GOALCOL | VAR_SORTED, {} },
	VAR_FOR_EACH_FREEBSD_VERSION(BLOCK_OPTDEF, "OPTIONS_DEFAULT_", VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	VAR_FOR_EACH_ARCH(BLOCK_OPTDEF, "OPTIONS_DEFAULT_", VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	{ BLOCK_OPTDEF, "OPTIONS_GROUP", VAR_SORTED, {} },
	{ BLOCK_OPTDEF, "OPTIONS_MULTI", VAR_SORTED, {} },
	{ BLOCK_OPTDEF, "OPTIONS_RADIO", VAR_SORTED, {} },
	{ BLOCK_OPTDEF, "OPTIONS_SINGLE", VAR_SORTED, {} },
	{ BLOCK_OPTDEF, "OPTIONS_EXCLUDE", VAR_SORTED, {} },
	{ BLOCK_OPTDEF, "OPTIONS_EXCLUDE_DragonFly", VAR_SKIP_GOALCOL | VAR_SORTED, {} },
	VAR_FOR_EACH_FREEBSD_VERSION(BLOCK_OPTDEF, "OPTIONS_EXCLUDE_", VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	VAR_FOR_EACH_ARCH(BLOCK_OPTDEF, "OPTIONS_EXCLUDE_", VAR_SKIP_GOALCOL | VAR_SORTED, {}),
	{ BLOCK_OPTDEF, "OPTIONS_SLAVE", VAR_SORTED, {} },
	{ BLOCK_OPTDEF, "OPTIONS_OVERRIDE", VAR_SORTED, {} },
	{ BLOCK_OPTDEF, "NO_OPTIONS_SORT", VAR_SKIP_GOALCOL, {} },
	{ BLOCK_OPTDEF, "OPTIONS_SUB", VAR_DEFAULT, {} },

	{ BLOCK_OPTDESC, "DESC", VAR_IGNORE_WRAPCOL | VAR_NOT_COMPARABLE, {} },

	{ BLOCK_OPTHELPER, "IMPLIES", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PREVENTS", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PREVENTS_MSG", VAR_NOT_COMPARABLE, {} },
#if PORTFMT_SUBPACKAGES
	{ BLOCK_OPTHELPER, "SUBPACKAGES", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
#endif
	{ BLOCK_OPTHELPER, "CATEGORIES", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CATEGORIES_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "MASTER_SITES", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "MASTER_SITES_OFF", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "DISTFILES", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "DISTFILES_OFF", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "EXTRACT_ONLY", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "EXTRACT_ONLY_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PATCH_SITES", VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PATCH_SITES_OFF", VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PATCHFILES", VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PATCHFILES_OFF", VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "BROKEN", VAR_IGNORE_WRAPCOL | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "BROKEN_OFF", VAR_IGNORE_WRAPCOL | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "IGNORE", VAR_IGNORE_WRAPCOL | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "IGNORE_OFF", VAR_IGNORE_WRAPCOL | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PKG_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PKG_DEPENDS_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "FETCH_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "FETCH_DEPENDS_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "EXTRACT_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "EXTRACT_DEPENDS_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PATCH_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PATCH_DEPENDS_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "BUILD_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "BUILD_DEPENDS_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "LIB_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "LIB_DEPENDS_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "RUN_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "RUN_DEPENDS_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "TEST_DEPENDS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "TEST_DEPENDS_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_SUBPKG_HELPER | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "USES", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "USES_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "USE", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "USE_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GH_ACCOUNT", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GH_ACCOUNT_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GH_PROJECT", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GH_PROJECT_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GH_SUBDIR", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GH_SUBDIR_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GH_TAGNAME", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GH_TAGNAME_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GH_TUPLE", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GH_TUPLE_OFF", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_ACCOUNT", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_ACCOUNT_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_COMMIT", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_COMMIT_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_PROJECT", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_PROJECT_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_SITE", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_SITE_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_SUBDIR", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_SUBDIR_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_TUPLE", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "GL_TUPLE_OFF", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CMAKE_BOOL", VAR_SORTED | VAR_NOT_COMPARABLE, { "cmake" } },
	{ BLOCK_OPTHELPER, "CMAKE_BOOL_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, { "cmake" } },
	{ BLOCK_OPTHELPER, "CMAKE_ON", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, { "cmake" } },
	{ BLOCK_OPTHELPER, "CMAKE_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, { "cmake" } },
	{ BLOCK_OPTHELPER, "CONFIGURE_ON", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CONFIGURE_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CONFIGURE_ENABLE", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CONFIGURE_WITH", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CONFIGURE_ENV", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CONFIGURE_ENV_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "QMAKE_ON", VAR_SORTED | VAR_NOT_COMPARABLE, { "qmake" } },
	{ BLOCK_OPTHELPER, "QMAKE_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, { "qmake" } },
	{ BLOCK_OPTHELPER, "MESON_ENABLED", VAR_SORTED | VAR_NOT_COMPARABLE, { "meson" } },
	{ BLOCK_OPTHELPER, "MESON_DISABLED", VAR_SORTED | VAR_NOT_COMPARABLE, { "meson" } },
	{ BLOCK_OPTHELPER, "MESON_ON", VAR_SORTED | VAR_NOT_COMPARABLE, { "meson" } },
	{ BLOCK_OPTHELPER, "MESON_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, { "meson" } },
	{ BLOCK_OPTHELPER, "MESON_TRUE", VAR_SORTED | VAR_NOT_COMPARABLE, { "meson" } },
	{ BLOCK_OPTHELPER, "MESON_FALSE", VAR_SORTED | VAR_NOT_COMPARABLE, { "meson" } },
	{ BLOCK_OPTHELPER, "MESON_YES", VAR_SORTED | VAR_NOT_COMPARABLE, { "meson" } },
	{ BLOCK_OPTHELPER, "MESON_NO", VAR_SORTED | VAR_NOT_COMPARABLE, { "meson" } },
	{ BLOCK_OPTHELPER, "USE_CABAL", VAR_CASE_SENSITIVE_SORT | VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_SORTED | VAR_NOT_COMPARABLE, { "cabal" } },
	{ BLOCK_OPTHELPER, "CABAL_FLAGS", VAR_NOT_COMPARABLE, { "cabal" } },
	{ BLOCK_OPTHELPER, "EXECUTABLES", VAR_SORTED | VAR_NOT_COMPARABLE, { "cabal" } },
	{ BLOCK_OPTHELPER, "MAKE_ARGS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "MAKE_ARGS_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "MAKE_ENV", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "MAKE_ENV_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "ALL_TARGET", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "ALL_TARGET_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "INSTALL_TARGET", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "INSTALL_TARGET_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "TEST_TARGET", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "TEST_TARGET_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CFLAGS", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CFLAGS_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CPPFLAGS", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CPPFLAGS_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CXXFLAGS", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CXXFLAGS_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "LDFLAGS", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "LDFLAGS_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "LIBS", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "LIBS_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CONFLICTS", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CONFLICTS_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CONFLICTS_BUILD", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CONFLICTS_BUILD_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CONFLICTS_INSTALL", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "CONFLICTS_INSTALL_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "BINARY_ALIAS", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "BINARY_ALIAS_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "DESKTOP_ENTRIES", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "DESKTOP_ENTRIES_OFF", VAR_PRINT_AS_NEWLINES | VAR_SKIP_GOALCOL | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "EXTRA_PATCHES", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "EXTRA_PATCHES_OFF", VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "SUB_FILES", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "SUB_FILES_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "SUB_LIST", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "SUB_LIST_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "INFO", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "INFO_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PLIST_DIRS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PLIST_DIRS_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PLIST_FILES", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PLIST_FILES_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PLIST_SUB", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PLIST_SUB_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PORTDOCS", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PORTDOCS_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PORTEXAMPLES", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "PORTEXAMPLES_OFF", VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "VARS", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
	{ BLOCK_OPTHELPER, "VARS_OFF", VAR_PRINT_AS_NEWLINES | VAR_SORTED | VAR_NOT_COMPARABLE, {} },
};

// Variables that are somewhere in the ports framework but that
// ports do not usually set.  Portclippy will flag them as "unknown".
// We can set special formatting rules for them here instead of in
// variable_order_.
static struct VariableOrderEntry special_variables_[] = {
	{ BLOCK_UNKNOWN, "_DISABLE_TESTS", VAR_SORTED, {} },
	{ BLOCK_UNKNOWN, "_IPXE_BUILDCFG", VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_UNKNOWN, "_SRHT_TUPLE", VAR_PRINT_AS_NEWLINES | VAR_SORTED, {} },
	{ BLOCK_UNKNOWN, "CARGO_CARGO_RUN", VAR_IGNORE_WRAPCOL, { "cargo" } },
	{ BLOCK_UNKNOWN, "CO_ENV", VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_UNKNOWN, "D4P_ENV", VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_UNKNOWN, "DEV_ERROR", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_UNKNOWN, "DEV_WARNING", VAR_IGNORE_WRAPCOL | VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_UNKNOWN, "GN_ARGS", VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_UNKNOWN, "GO_ENV", VAR_PRINT_AS_NEWLINES, { "go" } },
	{ BLOCK_UNKNOWN, "IPXE_BUILDCFG", VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_UNKNOWN, "MASTER_SITES_ABBREVS", VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_UNKNOWN, "MOZ_OPTIONS", VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_UNKNOWN, "QA_ENV", VAR_PRINT_AS_NEWLINES, {} },
	{ BLOCK_UNKNOWN, "SUBDIR", VAR_DEDUP | VAR_PRINT_AS_NEWLINES, {} },
};

#undef VAR_FOR_EACH_ARCH
#undef VAR_FOR_EACH_FREEBSD_VERSION
#undef VAR_FOR_EACH_FREEBSD_VERSION_AND_ARCH
#undef VAR_FOR_EACH_SSL

static volatile int rules_initialized = 0;

int
variable_has_flag(struct Parser *parser, const char *var, int flag)
{
	char *helper;
	if (is_options_helper(parser, var, NULL, &helper, NULL)) {
		for (size_t i = 0; i < nitems(variable_order_); i++) {
			if ((variable_order_[i].block == BLOCK_OPTHELPER ||
			     variable_order_[i].block == BLOCK_OPTDESC) &&
			    (variable_order_[i].flags & flag) &&
			    strcmp(helper, variable_order_[i].var) == 0) {
				free(helper);
				return 1;
			}
		}
		free(helper);
	}

	if (is_flavors_helper(parser, var, NULL, &helper)) {
		for (size_t i = 0; i < nitems(variable_order_); i++) {
			if (variable_order_[i].block == BLOCK_FLAVORS_HELPER &&
			    (variable_order_[i].flags & flag) &&
			    strcmp(helper, variable_order_[i].var) == 0) {
				free(helper);
				return 1;
			}
		}
		free(helper);
	}

	char *suffix;
	if (is_shebang_lang(parser, var, NULL, &suffix)) {
		for (size_t i = 0; i < nitems(variable_order_); i++) {
			if (variable_order_[i].block == BLOCK_SHEBANGFIX &&
			    (variable_order_[i].flags & VAR_NOT_COMPARABLE) &&
			    (variable_order_[i].flags & flag) &&
			    strcmp(suffix, variable_order_[i].var) == 0) {
				free(suffix);
				return 1;
			}
		}
		free(suffix);
	}

	if (is_cabal_datadir_vars(parser, var, NULL, &suffix)) {
		for (size_t i = 0; i < nitems(variable_order_); i++) {
			if (variable_order_[i].block == BLOCK_CABAL &&
			    (variable_order_[i].flags & VAR_NOT_COMPARABLE) &&
			    (variable_order_[i].flags & flag) &&
			    strcmp(suffix, variable_order_[i].var) == 0) {
				free(suffix);
				return 1;
			}
		}
		free(suffix);
	}

	char *prefix;
	if (matches_options_group(parser, var, &prefix)) {
		for (size_t i = 0; i < nitems(variable_order_); i++) {
			if (variable_order_[i].block == BLOCK_OPTDEF &&
			    (variable_order_[i].flags & flag) &&
			    strcmp(prefix, variable_order_[i].var) == 0) {
				free(prefix);
				return 1;
			}
		}
		free(prefix);
	}

	for (size_t i = 0; i < nitems(variable_order_); i++) {
		if ((!(variable_order_[i].flags & VAR_NOT_COMPARABLE)) &&
		    (variable_order_[i].flags & flag) &&
		    strcmp(var, variable_order_[i].var) == 0) {
			return 1;
		}
	}

	for (size_t i = 0; i < nitems(special_variables_); i++) {
		if ((special_variables_[i].flags & flag) &&
		    strcmp(var, special_variables_[i].var) == 0) {
			return 1;
		}
	}

	return 0;
}

int
is_valid_license(struct Parser *parser, const char *license)
{
	if (parser_settings(parser).behavior & PARSER_ALLOW_FUZZY_MATCHING) {
		if (strlen(license) == 0) {
			return 0;
		}
		size_t i = 0;
		for (; license[i] != 0; i++) {
			char c = license[i];
			switch (c) {
			case '-':
			case '.':
			case '_':
			case '+':
				break;
			default:
				if (!isalnum(c)) {
					return 0;
				}
				break;
			}
		}
		return i > 0;
	} else {
		return set_contains(parser_metadata(parser, PARSER_METADATA_LICENSES), license);
	}
}

int
matches_license_name(struct Parser *parser, const char *var)
{
	if (strcmp(var, "LICENSE_NAME") == 0 ||
	    strcmp(var, "LICENSE_TEXT") == 0) {
		return 1;
	}

	if (*var == '_') {
		var++;
	}

	if (!str_startswith(var, "LICENSE_NAME_") &&
	    !str_startswith(var, "LICENSE_TEXT_") &&
	    !str_startswith(var, "LICENSE_FILE_")) {
		return 0;
	}

	return is_valid_license(parser, var + strlen("LICENSE_NAME_"));
}

int
ignore_wrap_col(struct Parser *parser, struct Variable *var)
{
	const char *varname = variable_name(var);

	if (variable_modifier(var) == MODIFIER_SHELL ||
	    matches_license_name(parser, varname)) {
		return 1;
	}

	return variable_has_flag(parser, varname, VAR_IGNORE_WRAPCOL);
}

int
indent_goalcol(struct Variable *var)
{
	size_t varlength = strlen(variable_name(var)) + 1;
	switch (variable_modifier(var)) {
	case MODIFIER_ASSIGN:
		varlength += 1;
		break;
	case MODIFIER_APPEND:
	case MODIFIER_EXPAND:
	case MODIFIER_OPTIONAL:
	case MODIFIER_SHELL:
		varlength += 2;
		break;
	default:
		errx(1, "Unknown variable modifier: %d", variable_modifier(var));
	}
	if (((varlength + 1) % 8) == 0) {
		varlength++;
	}
	return ceil(varlength / 8.0) * 8;
}

int
is_comment(struct Token *token)
{
	if (token == NULL || token_data(token) == NULL) {
		return 0;
	}

	char *datap = token_data(token);
	for (; *datap != 0 && isspace(*datap); datap++);
	return *datap == '#';
}

int
is_include_bsd_port_mk(struct Token *t)
{
	struct Conditional *c = token_conditional(t);
	return c && token_type(t) == CONDITIONAL_TOKEN &&
		conditional_type(c) == COND_INCLUDE &&
		(strcmp(token_data(t), "<bsd.port.options.mk>") == 0 ||
		strcmp(token_data(t), "<bsd.port.pre.mk>") == 0 ||
		strcmp(token_data(t), "<bsd.port.post.mk>") == 0 ||
		strcmp(token_data(t), "<bsd.port.mk>") == 0);
}

int
case_sensitive_sort(struct Parser *parser, struct Variable *var)
{
	return variable_has_flag(parser, variable_name(var), VAR_CASE_SENSITIVE_SORT);
}

int
leave_unformatted(struct Parser *parser, struct Variable *var)
{
	return variable_has_flag(parser, variable_name(var), VAR_LEAVE_UNFORMATTED);
}

int
should_sort(struct Parser *parser, struct Variable *var)
{
	if (variable_modifier(var) == MODIFIER_SHELL) {
		return 0;
	}
	if ((parser_settings(parser).behavior & PARSER_ALWAYS_SORT_VARIABLES)) {
		return 1;
	}
	return variable_has_flag(parser, variable_name(var), VAR_SORTED);
}

int
print_as_newlines(struct Parser *parser, struct Variable *var)
{
	return variable_has_flag(parser, variable_name(var), VAR_PRINT_AS_NEWLINES);
}

int
skip_conditional(struct Token *t, int *ignore)
{
	if (*ignore > 0) {
		if (token_type(t) == CONDITIONAL_END) {
			switch (conditional_type(token_conditional(t))) {
			case COND_ENDFOR:
			case COND_ENDIF:
				(*ignore)--;
				break;
			default:
				break;
			}
		}
		return 1;
	}

	if (token_type(t) == CONDITIONAL_START) {
		switch (conditional_type(token_conditional(t))) {
		case COND_IF:
		case COND_IFDEF:
		case COND_IFMAKE:
		case COND_IFNDEF:
		case COND_IFNMAKE:
		case COND_FOR:
			(*ignore)++;
			break;
		default:
			break;
		}
	}

	return 0;
}

int
skip_dedup(struct Parser *parser, struct Variable *var)
{
	return !should_sort(parser, var) && !variable_has_flag(parser, variable_name(var), VAR_DEDUP);
}

int
skip_goalcol(struct Parser *parser, struct Variable *var)
{
	const char *varname = variable_name(var);

	if (matches_license_name(parser, varname)) {
		return 1;
	}

	return variable_has_flag(parser, varname, VAR_SKIP_GOALCOL);
}

static int
compare_rel(const char *rel[], size_t rellen, const char *a, const char *b)
{
	ssize_t ai = -1;
	ssize_t bi = -1;
	for (size_t i = 0; i < rellen; i++) {
		if (ai == -1 && strcmp(a, rel[i]) == 0) {
			ai = i;
		}
		if (bi == -1 && strcmp(b, rel[i]) == 0) {
			bi = i;
		}
		if (ai != -1 && bi != -1) {
			if (bi > ai) {
				return -1;
			} else if (ai > bi) {
				return 1;
			} else {
				return 0;
			}
		}
	}

	return strcasecmp(a, b);
}

int
compare_tokens(const void *ap, const void *bp, void *userdata)
{
	struct Parser *parser = userdata;
	struct Token *a = *(struct Token**)ap;
	struct Token *b = *(struct Token**)bp;
	assert(token_type(a) == VARIABLE_TOKEN);
	assert(token_type(b) == VARIABLE_TOKEN);
	assert(variable_cmp(token_variable(a), token_variable(b)) == 0);

	struct Variable *var = token_variable(a);

	/* End-of-line comments always go last */
	if (is_comment(a) && is_comment(b)) {
		return 0;
	}
	if (is_comment(a)) {
		return 1;
	}
	if (is_comment(b)) {
		return -1;
	}

	int result;
	if (compare_license_perms(parser, var, token_data(a), token_data(b), &result) ||
	    compare_plist_files(parser, var, token_data(a), token_data(b), &result) ||
	    compare_use_gnome(var, token_data(a), token_data(b), &result) ||
	    compare_use_kde(var, token_data(a), token_data(b), &result) ||
	    compare_use_pyqt(var, token_data(a), token_data(b), &result) ||
	    compare_use_qt(var, token_data(a), token_data(b), &result)) {
		return result;
	}

	if (case_sensitive_sort(parser, var)) {
		return strcmp(token_data(a), token_data(b));
	} else {
		return strcasecmp(token_data(a), token_data(b));
	}
}

int
compare_license_perms(struct Parser *parser, struct Variable *var, const char *a, const char *b, int *result)
{
	assert(result != NULL);

	// ^(_?LICENSE_PERMS_(-|[A-Z0-9\\._+ ])+|_LICENSE_LIST_PERMS|LICENSE_PERMS)
	const char *varname = variable_name(var);
	if (strcmp(varname, "_LICENSE_LIST_PERMS") != 0 &&
	    strcmp(varname, "LICENSE_PERMS") != 0) {
		if (str_startswith(varname, "_LICENSE_PERMS_")) {
			varname++;
		}
		if (!str_startswith(varname, "LICENSE_PERMS_")) {
			return 0;
		}
		const char *license = varname + strlen("LICENSE_PERMS_");
		if (!is_valid_license(parser, license)) {
			return 0;
		}
	}

	*result = compare_rel(license_perms_rel, nitems(license_perms_rel), a, b);
	return 1;
}

char *
remove_plist_keyword(const char *s)
{
	if (!str_endswith(s, "\"")) {
		return xstrdup(s);
	}

	// "^\"@([a-z]|-)+ "
	const char *ptr = s;
	if (*ptr != '"') {
		return xstrdup(s);
	}
	ptr++;
	if (*ptr != '@') {
		return xstrdup(s);
	}
	ptr++;

	const char *prev = ptr;
	for (; *ptr != 0 && (islower(*ptr) || *ptr == '-'); ptr++);
	if (*ptr == 0 || prev == ptr || *ptr != ' ') {
		return xstrdup(s);
	}
	ptr++;

	return xstrndup(ptr, strlen(ptr) - 1);
}

int
compare_plist_files(struct Parser *parser, struct Variable *var, const char *a, const char *b, int *result)
{
	assert(result != NULL);

	char *helper = NULL;
	if (is_options_helper(parser, variable_name(var), NULL, &helper, NULL)) {
		if (strcmp(helper, "PLIST_FILES_OFF") != 0 &&
		    strcmp(helper, "PLIST_FILES") != 0 &&
		    strcmp(helper, "PLIST_DIRS_OFF") != 0 &&
		    strcmp(helper, "PLIST_DIRS") != 0) {
			free(helper);
			return 0;
		}
		free(helper);
	} else if (strcmp(variable_name(var), "PLIST_FILES") != 0 &&
	    strcmp(variable_name(var), "PLIST_DIRS") != 0) {
		return 0;
	}

	/* Ignore plist keywords */
	char *as = remove_plist_keyword(a);
	char *bs = remove_plist_keyword(b);
	*result = strcasecmp(as, bs);
	free(as);
	free(bs);

	return 1;
}

int
compare_use_gnome(struct Variable *var, const char *a, const char *b, int *result)
{
	assert(result != NULL);

	if (strcmp(variable_name(var), "USE_GNOME") != 0) {
		return 0;
	}

	*result = compare_rel(use_gnome_rel, nitems(use_gnome_rel), a, b);
	return 1;
}

int
compare_use_kde(struct Variable *var, const char *a, const char *b, int *result)
{
	assert(result != NULL);

	if (strcmp(variable_name(var), "USE_KDE") != 0) {
		return 0;
	}

	*result = compare_rel(use_kde_rel, nitems(use_kde_rel), a, b);
	return 1;
}

int
compare_use_pyqt(struct Variable *var, const char *a, const char *b, int *result)
{
	assert(result != NULL);

	if (strcmp(variable_name(var), "USE_PYQT") != 0) {
		return 0;
	}

	*result = compare_rel(use_pyqt_rel, nitems(use_pyqt_rel), a, b);
	return 1;
}

int
compare_use_qt(struct Variable *var, const char *a, const char *b, int *result)
{
	assert(result != NULL);

	if (strcmp(variable_name(var), "USE_QT") != 0) {
		return 0;
	}

	*result = compare_rel(use_qt_rel, nitems(use_qt_rel), a, b);
	return 1;
}

int
is_flavors_helper(struct Parser *parser, const char *var, char **prefix_ret, char **helper_ret)
{
	const char *suffix = NULL;
	for (size_t i = 0; i < nitems(variable_order_); i++) {
		if (variable_order_[i].block != BLOCK_FLAVORS_HELPER) {
			continue;
		}
		const char *helper = variable_order_[i].var;
		if (str_endswith(var, helper) &&
		    strlen(var) > strlen(helper) &&
		    var[strlen(var) - strlen(helper) - 1] == '_') {
			suffix = helper;
			break;
		}
	}
	if (suffix == NULL) {
		return 0;
	}

	// ^[-_[:lower:][:digit:]]+_
	size_t len = strlen(var) - strlen(suffix);
	if (len == 0) {
		return 0;
	}
	if (var[len - 1] != '_') {
		return 0;
	}
	for (size_t i = 0; i < len; i++) {
		char c = var[i];
		if (c != '-' && c != '_' && !islower(c) && !isdigit(c)) {
			return 0;
		}
	}

	if (parser_settings(parser).behavior & PARSER_ALLOW_FUZZY_MATCHING) {
		goto done;
	}

	char *prefix = xstrndup(var, len - 1);
	int found = 0;
	SET_FOREACH(parser_metadata(parser, PARSER_METADATA_FLAVORS), const char *, flavor) {
		if (strcmp(prefix, flavor) == 0) {
			found = 1;
			break;
		}
	}
	free(prefix);
	if (!found) {
		return 0;
	}
done:
	if (prefix_ret) {
		*prefix_ret = xstrndup(var, len);
	}
	if (helper_ret) {
		*helper_ret = xstrdup(suffix);
	}

	return 1;
}

char *
extract_subpkg(struct Parser *parser, const char *var_, char **subpkg_ret)
{
	char *var = NULL;
	const char *subpkg = NULL;
	for (ssize_t i = strlen(var_) - 1; i > -1; i--) {
		char c = var_[i];
		if (c != '-' && c != '_' && !islower(c) && !isdigit(c)) {
			if (c == '.') {
				subpkg = var_ + i + 1;
				var = xstrndup(var_, i);
			} else {
				var = xstrdup(var_);
			}
			break;
		}
	}

	if (var == NULL) {
		if (subpkg_ret) {
			*subpkg_ret = NULL;
		}
		return NULL;
	}

	if (subpkg && !(parser_settings(parser).behavior & PARSER_ALLOW_FUZZY_MATCHING)) {
		int found = 0;
#if PORTFMT_SUBPACKAGES
		struct Set *subpkgs = parser_metadata(parser, PARSER_METADATA_SUBPACKAGES);
		SET_FOREACH (subpkgs, const char *, pkg) {
			if (strcmp(subpkg, pkg) == 0) {
				found = 1;
				break;
			}
		}
#endif
		if (!found) {
			if (subpkg_ret) {
				*subpkg_ret = NULL;
			}
			free(var);
			return NULL;
		}
	}

	if (subpkg_ret) {
		if (subpkg) {
			*subpkg_ret = xstrdup(subpkg);
		} else {
			*subpkg_ret = NULL;
		}
	}

	return var;
}

int
is_options_helper(struct Parser *parser, const char *var_, char **prefix_ret, char **helper_ret, char **subpkg_ret)
{
	char *subpkg;
	char *var;
	if ((var = extract_subpkg(parser, var_, &subpkg)) == NULL) {
		return 0;
	}

	const char *suffix = NULL;
	if (str_endswith(var, "DESC")) {
		suffix = "DESC";
	} else {
		for (size_t i = 0; i < nitems(variable_order_); i++) {
			if (variable_order_[i].block != BLOCK_OPTHELPER) {
				continue;
			}
			const char *helper = variable_order_[i].var;
			if (str_endswith(var, helper) &&
			    strlen(var) > strlen(helper) &&
			    var[strlen(var) - strlen(helper) - 1] == '_') {
				suffix = helper;
				break;
			}
		}
	}
	if (suffix == NULL) {
		free(subpkg);
		free(var);
		return 0;
	}

	if (subpkg) {
		int found = 0;
#if PORTFMT_SUBPACKAGES
		for (size_t i = 0; i < nitems(variable_order_); i++) {
			if (variable_order_[i].block != BLOCK_OPTHELPER ||
			    !(variable_order_[i].flags & VAR_SUBPKG_HELPER)) {
				continue;
			}
			if (strcmp(variable_order_[i].var, suffix) == 0) {
				found = 1;
			}
		}
#endif
		if (!found) {
			free(subpkg);
			free(var);
			return 0;
		}
	}


	// ^[-_[:upper:][:digit:]]+_
	size_t len = strlen(var) - strlen(suffix);
	if (len == 0) {
		free(subpkg);
		free(var);
		return 0;
	}
	if (var[len - 1] != '_') {
		free(subpkg);
		free(var);
		return 0;
	}
	for (size_t i = 0; i < len; i++) {
		char c = var[i];
		if (c != '-' && c != '_' && !isupper(c) && !isdigit(c)) {
			free(subpkg);
			free(var);
			return 0;
		}
	}

	if (parser_settings(parser).behavior & PARSER_ALLOW_FUZZY_MATCHING) {
		goto done;
	}

	char *prefix = xstrndup(var, len - 1);
	struct Set *groups = parser_metadata(parser, PARSER_METADATA_OPTION_GROUPS);
	struct Set *options = parser_metadata(parser, PARSER_METADATA_OPTIONS);
	if (strcmp(suffix, "DESC") == 0) {
		SET_FOREACH (groups, const char *, group) {
			if (strcmp(prefix, group) == 0) {
				free(prefix);
				goto done;
			}
		}
	}
	int found = 0;
	SET_FOREACH (options, const char *, option) {
		if (strcmp(prefix, option) == 0) {
			found = 1;
			break;
		}
	}
	free(prefix);
	if (!found) {
		free(subpkg);
		free(var);
		return 0;
	}

done:
	if (prefix_ret) {
		*prefix_ret = xstrndup(var, len);
	}
	if (helper_ret) {
		*helper_ret = xstrdup(suffix);
	}
	if (subpkg_ret) {
		if (subpkg) {
			*subpkg_ret = xstrdup(subpkg);
		} else {
			*subpkg_ret = NULL;
		}
	}

	free(subpkg);
	free(var);

	return 1;
}

int
matches_options_group(struct Parser *parser, const char *s, char **prefix)
{
	size_t i = 0;
	// ^_?
	if (s[i] == '_') {
		i++;
	}

	const char *var = NULL;
	// OPTIONS_(GROUP|MULTI|RADIO|SINGLE)_
	const char *opts[] = {
		"OPTIONS_GROUP_",
		"OPTIONS_MULTI_",
		"OPTIONS_RADIO_",
		"OPTIONS_SINGLE_",
	};
	int matched = 0;
	for (size_t j = 0; j < nitems(opts); j++) {
		if (str_startswith(s + i, opts[j])) {
			matched = 1;
			i += strlen(opts[j]);
			var = opts[j];
			break;
		}
	}
	if (!matched) {
		return 0;
	}

	if (parser_settings(parser).behavior & PARSER_ALLOW_FUZZY_MATCHING) {
		// [-_[:upper:][:digit:]]+
		if (!(isupper(s[i]) || isdigit(s[i]) || s[i] == '-' || s[i] == '_')) {
			return 0;
		}
		for (size_t len = strlen(s); i < len; i++) {
			if (!(isupper(s[i]) || isdigit(s[i]) || s[i] == '-' || s[i] == '_')) {
				return 0;
			}
		}
		if (prefix) {
			*prefix = xstrndup(var, strlen(var) - 1);
		}
		return 1;
	} else {
		struct Set *groups = parser_metadata(parser, PARSER_METADATA_OPTION_GROUPS);
		// XXX: This could be stricter by checking the group type too
		SET_FOREACH (groups, const char *, group) {
			if (strcmp(s + i, group) == 0) {
				if (prefix) {
					*prefix = xstrndup(var, strlen(var) - 1);
				}
				return 1;
			}
		}
		return 0;
	}

}

static int
is_cabal_datadir_vars_helper(const char *var, const char *exe, char **prefix, char **suffix)
{
	char *buf = str_printf( "%s_DATADIR_VARS", exe);
	if (strcmp(var, buf) == 0) {
		if (prefix) {
			*prefix = xstrdup(exe);
		}
		if (suffix) {
			*suffix = xstrdup("DATADIR_VARS");
		}
		free(buf);
		return 1;
	}
	free(buf);

	return 0;
}

int
is_cabal_datadir_vars(struct Parser *parser, const char *var, char **prefix, char **suffix)
{
	if (parser_settings(parser).behavior & PARSER_ALLOW_FUZZY_MATCHING) {
		if (str_endswith(var, "_DATADIR_VARS")) {
			if (prefix) {
				*prefix = xstrndup(var, strlen(var) - strlen("_DATADIR_VARS"));
			}
			if (suffix) {
				*suffix = xstrdup("DATADIR_VARS");
			}
			return 1;
		}
	}

	// Do we have USES=cabal?
	if (!set_contains(parser_metadata(parser, PARSER_METADATA_USES), "cabal")) {
		return 0;
	}

	SET_FOREACH (parser_metadata(parser, PARSER_METADATA_CABAL_EXECUTABLES), const char *, exe) {
		if (is_cabal_datadir_vars_helper(var, exe, prefix, suffix)) {
			return 1;
		}
	}

	return 0;
}

static int
is_shebang_lang_helper(const char *var, const char *lang, char **prefix, char **suffix)
{
	char *buf = str_printf("%s_OLD_CMD", lang);
	if (strcmp(var, buf) == 0) {
		if (prefix) {
			*prefix = xstrdup(lang);
		}
		if (suffix) {
			*suffix = xstrdup("OLD_CMD");
		}
		free(buf);
		return 1;
	}
	free(buf);

	buf = str_printf("%s_CMD", lang);
	if (strcmp(var, buf) == 0) {
		if (prefix) {
			*prefix = xstrdup(lang);
		}
		if (suffix) {
			*suffix = xstrdup("CMD");
		}
		free(buf);
		return 1;
	}
	free(buf);

	return 0;
}

int
is_shebang_lang(struct Parser *parser, const char *var, char **prefix, char **suffix)
{
	if (parser_settings(parser).behavior & PARSER_ALLOW_FUZZY_MATCHING) {
		if (str_endswith(var, "_OLD_CMD")) {
			if (prefix) {
				*prefix = xstrndup(var, strlen(var) - strlen("_OLD_CMD"));
			}
			if (suffix) {
				*suffix = xstrdup("OLD_CMD");
			}
			return 1;
		}
		if (str_endswith(var, "_CMD")) {
			if (prefix) {
				*prefix = xstrndup(var, strlen(var) - strlen("_CMD"));
			}
			if (suffix) {
				*suffix = xstrdup("CMD");
			}
			return 1;
		}
	}

	// Do we have USES=shebangfix?
	if (!set_contains(parser_metadata(parser, PARSER_METADATA_USES), "shebangfix")) {
		return 0;
	}

	for (size_t i = 0; i < nitems(static_shebang_langs_); i++) {
		const char *lang = static_shebang_langs_[i];
		if (is_shebang_lang_helper(var, lang, prefix, suffix)) {
			return 1;
		}
	}

	int ok = 0;
	SET_FOREACH (parser_metadata(parser, PARSER_METADATA_SHEBANG_LANGS), const char *, lang) {
		if (is_shebang_lang_helper(var, lang, prefix, suffix)) {
			ok = 1;
			break;
		}
	}

	return ok;
}

enum BlockType
variable_order_block(struct Parser *parser, const char *var, struct Set **uses_candidates)
{
	if (uses_candidates) {
		*uses_candidates = NULL;
	}

	if (strcmp(var, "LICENSE") == 0) {
		return BLOCK_LICENSE;
	}
	for (size_t i = 0; i < nitems(variable_order_); i++) {
		if (variable_order_[i].block != BLOCK_LICENSE ||
		    strcmp(variable_order_[i].var, "LICENSE") == 0) {
			continue;
		}
		if (strcmp(variable_order_[i].var, var) == 0) {
			return BLOCK_LICENSE;
		}
		if (str_startswith(var, variable_order_[i].var)) {
			const char *suffix = var + strlen(variable_order_[i].var);
			if (*suffix == '_' && is_valid_license(parser, suffix + 1)) {
				return BLOCK_LICENSE;
			}
		}
	}

	if (is_flavors_helper(parser, var, NULL, NULL)) {
		return BLOCK_FLAVORS_HELPER;
	}

	if (is_shebang_lang(parser, var, NULL, NULL)) {
		return BLOCK_SHEBANGFIX;
	}

	if (is_cabal_datadir_vars(parser, var, NULL, NULL)) {
		return BLOCK_CABAL;
	}

	if (is_options_helper(parser, var, NULL, NULL, NULL)) {
		if (str_endswith(var, "_DESC")) {
			return BLOCK_OPTDESC;
		} else {
			return BLOCK_OPTHELPER;
		}
	}

	if (matches_options_group(parser, var, NULL)) {
		return BLOCK_OPTDEF;
	}

	const char *tmp = var;
	char *var_without_subpkg = extract_subpkg(parser, var, NULL);
	if (var_without_subpkg) {
		tmp = var_without_subpkg;
	}
	for (size_t i = 0; i < nitems(variable_order_); i++) {
		switch (variable_order_[i].block) {
		case BLOCK_FLAVORS_HELPER:
		case BLOCK_OPTHELPER:
		case BLOCK_OPTDESC:
			continue;
		case BLOCK_LICENSE:
		case BLOCK_OPTDEF:
			// RE_LICENSE_*, matches_options_group() do not
			// cover all cases.
		default:
			break;
		}
		if (strcmp(tmp, variable_order_[i].var) == 0) {
			size_t count = 0;
			int satisfies_uses = 1;
			// We skip the USES check if the port is a
			// slave port since often USES only appears
			// in the master.  Since we do not recurse
			// down in the master Makefile we would
			// get many false positives otherwise.
			if (!(parser_settings(parser).behavior & PARSER_ALLOW_FUZZY_MATCHING) &&
			    !parser_metadata(parser, PARSER_METADATA_MASTERDIR)) {
				struct Set *uses = parser_metadata(parser, PARSER_METADATA_USES);
				for (; variable_order_[i].uses[count] && count < nitems(variable_order_[i].uses); count++);
				if (count > 0) {
					satisfies_uses = 0;
					for (size_t j = 0; j < count; j++) {
						const char *requses = variable_order_[i].uses[j];
						if (set_contains(uses, requses)) {
							satisfies_uses = 1;
							break;
						}
					}
				}
			}
			if (satisfies_uses) {
				free(var_without_subpkg);
				return variable_order_[i].block;
			} else if (count > 0 && uses_candidates) {
				if (*uses_candidates == NULL) {
					*uses_candidates = set_new(str_compare, NULL, NULL);
				}
				for (size_t j = 0; j < count; j++) {
					set_add(*uses_candidates, variable_order_[i].uses[j]);
				}
			}
		}
	}
	free(var_without_subpkg);

	return BLOCK_UNKNOWN;
}

int
compare_order(const void *ap, const void *bp, void *userdata)
{
	struct Parser *parser = userdata;
	const char *a = *(const char **)ap;
	const char *b = *(const char **)bp;

	if (strcmp(a, b) == 0) {
		return 0;
	}
	enum BlockType ablock = variable_order_block(parser, a, NULL);
	enum BlockType bblock = variable_order_block(parser, b, NULL);
	if (ablock < bblock) {
		return -1;
	} else if (ablock > bblock) {
		return 1;
	}

	if (ablock == BLOCK_LICENSE) {
		int ascore = -1;
		int bscore = -1;
		for (size_t i = 0; i < nitems(variable_order_); i++) {
			if (variable_order_[i].block != BLOCK_LICENSE) {
				continue;
			}
			if (strcmp(variable_order_[i].var, "LICENSE") == 0) {
				continue;
			}
			if (str_startswith(a, variable_order_[i].var)) {
				ascore = i;
			}
			if (str_startswith(b, variable_order_[i].var)) {
				bscore = i;
			}
		}
		if (ascore < bscore) {
			return -1;
		} else if (ascore > bscore) {
			return 1;
		}
	} else if (ablock == BLOCK_FLAVORS_HELPER) {
		int ascore = -1;
		int bscore = -1;

		char *ahelper = NULL;
		char *aprefix = NULL;
		char *bhelper = NULL;
		char *bprefix = NULL;
		if (!is_flavors_helper(parser, a, &aprefix, &ahelper) ||
		    !is_flavors_helper(parser, b, &bprefix, &bhelper)) {
			abort();
		}
		assert(ahelper != NULL && aprefix != NULL);
		assert(bhelper != NULL && bprefix != NULL);

		// Only compare if common prefix (helper for the same flavor)
		int prefix_score = strcmp(aprefix, bprefix);
		if (prefix_score == 0) {
			for (size_t i = 0; i < nitems(variable_order_); i++) {
				if (variable_order_[i].block != BLOCK_FLAVORS_HELPER) {
					continue;
				}
				if (strcmp(ahelper, variable_order_[i].var) == 0) {
					ascore = i;
				}
				if (strcmp(bhelper, variable_order_[i].var) == 0) {
					bscore = i;
				}
			}
		}

		free(aprefix);
		free(ahelper);
		free(bprefix);
		free(bhelper);

		if (prefix_score != 0) {
			return prefix_score;
		} else if (ascore < bscore) {
			return -1;
		} else if (ascore > bscore) {
			return 1;
		} else {
			return strcmp(a, b);
		}
	} else if (ablock == BLOCK_SHEBANGFIX) {
		if (str_endswith(a, "_CMD") && !str_endswith(b, "_CMD")) {
			return 1;
		} else if (!str_endswith(a, "_CMD") && str_endswith(b, "_CMD")) {
			return -1;
		} else if (str_endswith(a, "_CMD") && str_endswith(b, "_CMD")) {
			char *alang = NULL;
			char *asuffix = NULL;
			char *blang = NULL;
			char *bsuffix = NULL;
			is_shebang_lang(parser, a, &alang, &asuffix);
			is_shebang_lang(parser, b, &blang, &bsuffix);
			assert(alang);
			assert(asuffix);
			assert(blang);
			assert(bsuffix);

			ssize_t ascore = -1;
			ssize_t bscore = -1;
			for (size_t i = 0; i < nitems(static_shebang_langs_); i++) {
				const char *lang = static_shebang_langs_[i];
				if (strcmp(alang, lang) == 0) {
					ascore = i;
				}
				if (strcmp(blang, lang) == 0) {
					bscore = i;
				}
			}
			size_t i = 0;
			SET_FOREACH (parser_metadata(parser, PARSER_METADATA_SHEBANG_LANGS), const char *, lang) {
				if (strcmp(alang, lang) == 0) {
					ascore = i;
				}
				if (strcmp(blang, lang) == 0) {
					bscore = i;
				}
				i++;
			}

			int aold = strcmp(asuffix, "OLD_CMD") == 0;
			int bold = strcmp(bsuffix, "OLD_CMD") == 0;
			free(alang);
			free(asuffix);
			free(blang);
			free(bsuffix);
			if (ascore == bscore) {
				if (aold && !bold) {
					return -1;
				} else if (!aold && bold) {
					return 1;
				} else {
					return 0;
				}
			} else if (ascore < bscore) {
				return -1;
			} else {
				return 1;
			}
		}
	} else if (ablock == BLOCK_CABAL) {
		// XXX: Yikes!
		if (strcmp(a, "SKIP_CABAL_PLIST") == 0) {
			return 1;
		} else if (strcmp(b, "SKIP_CABAL_PLIST") == 0) {
			return -1;
		} else if (str_endswith(a, "_DATADIR_VARS") && !str_endswith(b, "_DATADIR_VARS")) {
			return 1;
		} else if (!str_endswith(a, "_DATADIR_VARS") && str_endswith(b, "_DATADIR_VARS")) {
			return -1;
		} else if (str_endswith(a, "_DATADIR_VARS") && str_endswith(b, "_DATADIR_VARS")) {
			char *aexe = NULL;
			char *asuffix = NULL;
			char *bexe = NULL;
			char *bsuffix = NULL;
			is_cabal_datadir_vars(parser, a, &aexe, &asuffix);
			is_cabal_datadir_vars(parser, b, &bexe, &bsuffix);
			assert(aexe);
			assert(asuffix);
			assert(bexe);
			assert(bsuffix);

			ssize_t ascore = -1;
			ssize_t bscore = -1;
			size_t i = 0;
			SET_FOREACH (parser_metadata(parser, PARSER_METADATA_CABAL_EXECUTABLES), const char *, exe) {
				if (strcmp(aexe, exe) == 0) {
					ascore = i;
				}
				if (strcmp(bexe, exe) == 0) {
					bscore = i;
				}
				i++;
			}

			int aold = strcmp(asuffix, "DATADIR_VARS") == 0;
			int bold = strcmp(bsuffix, "DATADIR_VARS") == 0;
			free(aexe);
			free(asuffix);
			free(bexe);
			free(bsuffix);
			if (ascore == bscore) {
				if (aold && !bold) {
					return -1;
				} else if (!aold && bold) {
					return 1;
				} else {
					return 0;
				}
			} else if (ascore < bscore) {
				return -1;
			} else {
				return 1;
			}
		}
	} else if (ablock == BLOCK_OPTDESC) {
		return strcmp(a, b);
	} else if (ablock == BLOCK_OPTHELPER) {
		int ascore = -1;
		int bscore = -1;

		char *ahelper = NULL;
		char *aprefix = NULL;
		char *bhelper = NULL;
		char *bprefix = NULL;
		// TODO SUBPKG
		if (!is_options_helper(parser, a, &aprefix, &ahelper, NULL) ||
		    !is_options_helper(parser, b, &bprefix, &bhelper, NULL)) {
			abort();
		}
		assert(ahelper != NULL && aprefix != NULL);
		assert(bhelper != NULL && bprefix != NULL);

		// Only compare if common prefix (helper for the same option)
		int prefix_score = strcmp(aprefix, bprefix);
		if (prefix_score == 0) {
			for (size_t i = 0; i < nitems(variable_order_); i++) {
				if (variable_order_[i].block != BLOCK_OPTHELPER) {
					continue;
				}
				if (strcmp(ahelper, variable_order_[i].var) == 0) {
					ascore = i;
				}
				if (strcmp(bhelper, variable_order_[i].var) == 0) {
					bscore = i;
				}
			}
		}

		free(aprefix);
		free(ahelper);
		free(bprefix);
		free(bhelper);

		if (prefix_score != 0) {
			return prefix_score;
		} else if (ascore < bscore) {
			return -1;
		} else if (ascore > bscore) {
			return 1;
		} else {
			return strcmp(a, b);
		}
	} else if (ablock == BLOCK_OPTDEF) {
		int ascore = -1;
		int bscore = -1;

		for (size_t i = 0; i < nitems(variable_order_); i++) {
			if (variable_order_[i].block != BLOCK_OPTDEF) {
				continue;
			}
			if (str_startswith(a, variable_order_[i].var)) {
				ascore = i;
			}
			if (str_startswith(b, variable_order_[i].var)) {
				bscore = i;
			}
		}

		if (ascore < bscore) {
			return -1;
		} else if (ascore > bscore) {
			return 1;
		} else {
			return strcmp(a, b);
		}
	}

	char *asubpkg = NULL;
	char *a_without_subpkg = extract_subpkg(parser, a, &asubpkg);
	if (a_without_subpkg == NULL) {
		a_without_subpkg = xstrdup(a);
	}
	char *bsubpkg = NULL;
	char *b_without_subpkg = extract_subpkg(parser, b, &bsubpkg);
	if (b_without_subpkg == NULL) {
		b_without_subpkg = xstrdup(b);
	}
	int ascore = -1;
	int bscore = -1;
	for (size_t i = 0; i < nitems(variable_order_) && (ascore == -1 || bscore == -1); i++) {
		if (strcmp(a_without_subpkg, variable_order_[i].var) == 0) {
			ascore = i;
		}
		if (strcmp(b_without_subpkg, variable_order_[i].var) == 0) {
			bscore = i;
		}
	}

	int retval = 0;
	if (strcmp(a_without_subpkg, b_without_subpkg) == 0 && asubpkg && bsubpkg) {
		retval = strcmp(asubpkg, bsubpkg);
	} else if (asubpkg && !bsubpkg) {
		retval = 1;
	} else if (!asubpkg && bsubpkg) {
		retval = -1;
	} else if (ascore < bscore) {
		retval = -1;
	} else if (ascore > bscore) {
		retval = 1;
	} else {
		retval = strcmp(a_without_subpkg, b_without_subpkg);
	}
	free(a_without_subpkg);
	free(asubpkg);
	free(b_without_subpkg);
	free(bsubpkg);

	return retval;
}

void
target_extract_opt(struct Parser *parser, const char *target, char **target_out, char **opt_out, int *state)
{
	int colon = str_endswith(target, ":");
	int on;
	if ((colon && ((on = str_endswith(target, "-on:")) || str_endswith(target, "-off:"))) ||
	    (!colon && ((on = str_endswith(target, "-on")) || str_endswith(target, "-off")))) {
		const char *p = target;
		for (; *p == '-' || (islower(*p) && isalpha(*p)); p++);
		size_t opt_suffix_len;
		if (on) {
			opt_suffix_len = strlen("-on");
		} else {
			opt_suffix_len = strlen("-off");
		}
		if (colon) {
			opt_suffix_len++;
		}
		char *opt = xstrndup(p, strlen(p) - opt_suffix_len);
		char *tmp = str_printf("%s_USES", opt);
		if (is_options_helper(parser, tmp, NULL, NULL, NULL)) {
			free(tmp);
			char *target_root = xstrndup(target, strlen(target) - strlen(p) - 1);
			for (size_t i = 0; i < nitems(target_order_); i++) {
				if (target_order_[i].opthelper &&
				    strcmp(target_order_[i].name, target_root) == 0) {
					*state = on;
					*opt_out = opt;
					*target_out = target_root;
					return;
				}
			}
			free(target_root);
		} else {
			free(tmp);
		}
		free(opt);
	}

	*opt_out = NULL;
	*state = 0;
	if (colon) {
		size_t len = strlen(target);
		if (len > 0) {
			*target_out = xstrndup(target, len - 1);
			return;
		}
	}
	*target_out = xstrdup(target);
}

int
is_known_target(struct Parser *parser, const char *target)
{
	char *root, *opt;
	int state;
	target_extract_opt(parser, target, &root, &opt, &state);
	free(opt);

	for (size_t i = 0; i < nitems(target_order_); i++) {
		if (strcmp(target_order_[i].name, root) == 0) {
			free(root);
			return 1;
		}
	}

	free(root);
	return 0;
}

int
is_special_source(const char *source)
{
	for (size_t i = 0; i < nitems(special_sources_); i++) {
		if (strcmp(source, special_sources_[i]) == 0) {
			return 1;
		}
	}
	return 0;
}

int
is_special_target(const char *target)
{
	for (size_t i = 0; i < nitems(special_targets_); i++) {
		if (strcmp(target, special_targets_[i]) == 0) {
			return 1;
		}
	}
	return 0;
}

int
compare_target_order(const void *ap, const void *bp, void *userdata)
{
	struct Parser *parser = userdata;
	int retval = 0;
	const char *a_ = *(const char **)ap;
	const char *b_ = *(const char **)bp;

	if (strcmp(a_, b_) == 0) {
		return 0;
	}

	char *a, *b, *aopt, *bopt;
	int aoptstate, boptstate;
	target_extract_opt(parser, a_, &a, &aopt, &aoptstate);
	target_extract_opt(parser, b_, &b, &bopt, &boptstate);

	ssize_t aindex = -1;
	ssize_t bindex = -1;
	for (size_t i = 0; i < nitems(target_order_) && (aindex == -1 || bindex == -1); i++) {
		if (aindex == -1 && strcmp(target_order_[i].name, a) == 0) {
			aindex = i;
		}
		if (bindex == -1 && strcmp(target_order_[i].name, b) == 0) {
			bindex = i;
		}
	}

	if (aindex == -1) {
		retval = 1;
		goto cleanup;
	} else if (bindex == -1) {
		retval = -1;
		goto cleanup;
	} else if (aindex == bindex) {
		if (aopt == NULL) {
			retval = -1;
			goto cleanup;
		}
		if (bopt == NULL) {
			retval = 1;
			goto cleanup;
		}

		int c = strcmp(aopt, bopt);
		if (c < 0) {
			retval = -1;
			goto cleanup;
		} else if (c > 0) {
			retval = 1;
			goto cleanup;
		}

		if (aoptstate && !boptstate) {
			retval = -1;
			goto cleanup;
		} else if (!aoptstate && boptstate) {
			retval = 1;
			goto cleanup;
		} else {
			// should not happen
			abort();
		}
	} else if (aindex < bindex) {
		retval = -1;
		goto cleanup;
	} else if (aindex > bindex) {
		retval = 1;
		goto cleanup;
	} else {
		// should not happen
		abort();
	}

cleanup:
	free(a);
	free(aopt);
	free(b);
	free(bopt);

	return retval;
}

const char *
blocktype_tostring(enum BlockType block)
{
	switch (block) {
	case BLOCK_APACHE:
		return "USES=apache related variables";
	case BLOCK_BROKEN:
		return "BROKEN/IGNORE/DEPRECATED messages";
	case BLOCK_CABAL:
		return "USES=cabal related variables";
	case BLOCK_CARGO:
		return "USES=cargo related variables";
	case BLOCK_CFLAGS:
		return "CFLAGS/CXXFLAGS/LDFLAGS block";
	case BLOCK_CMAKE:
		return "USES=cmake related variables";
	case BLOCK_CONFIGURE:
		return "Configure block";
	case BLOCK_CONFLICTS:
		return "Conflicts";
	case BLOCK_DEPENDS:
		return "Dependencies";
	case BLOCK_ELIXIR:
		return "USES=elixir related variables";
	case BLOCK_EMACS:
		return "USES=emacs related variables";
	case BLOCK_ERLANG:
		return "USES=erlang related variables";
	case BLOCK_FLAVORS:
		return "Flavors";
	case BLOCK_FLAVORS_HELPER:
		return "Flavors helpers";
	case BLOCK_GO:
		return "USES=go related variables";
	case BLOCK_LAZARUS:
		return "USES=lazarus related variables";
	case BLOCK_LICENSE:
		return "License block";
	case BLOCK_LICENSE_OLD:
		return "Old-school license block (please replace with LICENSE)";
	case BLOCK_LINUX:
		return "USES=linux related variables";
	case BLOCK_MAINTAINER:
		return "Maintainer block";
	case BLOCK_MAKE:
		return "Make block";
	case BLOCK_MESON:
		return "USES=meson related variables";
	case BLOCK_NUGET:
		return "USES=mono related variables";
	case BLOCK_OPTDEF:
		return "Options definitions";
	case BLOCK_OPTDESC:
		return "Options descriptions";
	case BLOCK_OPTHELPER:
		return "Options helpers";
	case BLOCK_PATCHFILES:
		return "Patch files";
	case BLOCK_PLIST:
		return "Packaging list block";
	case BLOCK_PORTNAME:
		return "PORTNAME block";
	case BLOCK_QMAKE:
		return "USES=qmake related variables";
	case BLOCK_SCONS:
		return "USES=scons related variables";
	case BLOCK_SHEBANGFIX:
		return "USES=shebangfix related variables";
	case BLOCK_STANDARD:
		return "Standard bsd.port.mk variables";
#if PORTFMT_SUBPACKAGES
	case BLOCK_SUBPACKAGES:
		return "Subpackages block";
#endif
	case BLOCK_UNIQUEFILES:
		return "USES=uniquefiles block";
	case BLOCK_UNKNOWN:
		return "Unknown variables";
	case BLOCK_USERS:
		return "Users and groups block";
	case BLOCK_USES:
		return "USES block";
	case BLOCK_WRKSRC:
		return "WRKSRC block";
	}

	abort();
}

int
target_command_wrap_after_each_token(const char *command)
{
	if (*command == '@') {
		command++;
	}
	for (size_t i = 0; i < nitems(target_command_wrap_after_each_token_); i++) {
		if (strcmp(command, target_command_wrap_after_each_token_[i]) == 0) {
			return 1;
		}
	}
	return 0;
}

int
target_command_should_wrap(const char *word)
{
	if (strcmp(word, "&&") == 0 ||
	    strcmp(word, "||") == 0 ||
	    strcmp(word, "then") == 0 ||
	    (str_endswith(word, ";") && !str_endswith(word, "\\;")) ||
	    strcmp(word, "|") == 0) {
		return 1;
	}

	return 0;
}

regex_t *
regex(enum RegularExpression re)
{
	return &regular_expressions[re].re;
}

int
matches(enum RegularExpression re, const char *s)
{
	return regexec(&regular_expressions[re].re, s, 0, NULL, 0) == 0;
}

char *
sub(enum RegularExpression re, const char *replacement, const char *s)
{
	assert(replacement != NULL);
	assert(s != NULL);

	size_t len = strlen(replacement) + strlen(s) + 1;
	char *buf = xmalloc(len);
	buf[0] = 0;

	regmatch_t pmatch[1];
	if (regexec(&regular_expressions[re].re, s, 1, pmatch, 0) == 0) {
		strncpy(buf, s, pmatch[0].rm_so);
		xstrlcat(buf, replacement, len);
		strncat(buf, s + pmatch[0].rm_eo, strlen(s) - pmatch[0].rm_eo);
	} else {
		xstrlcat(buf, s, len);
	}

	return buf;
}

void
rules_init()
{
	if (rules_initialized) {
		return;
	}

	for (size_t i = 0; i < nitems(regular_expressions); i++) {
		const char *pattern;
		pattern = regular_expressions[i].pattern;

		int error = regcomp(&regular_expressions[i].re, pattern,
				    regular_expressions[i].flags);
		if (error != 0) {
			size_t errbuflen = regerror(error, &regular_expressions[i].re, NULL, 0);
			char *errbuf = xmalloc(errbuflen);
			regerror(error, &regular_expressions[i].re, errbuf, errbuflen);
			errx(1, "regcomp: %zu: %s", i, errbuf);
		}
	}

	rules_initialized = 1;
}
