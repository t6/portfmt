# Changelog

All notable changes to portfmt are documented in this file.
The sections should follow the order `Packaging`, `Added`, `Changed`, `Fixed` and `Removed`.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## Unreleased

### Added

- portscan: print progress reports on `SIGINFO` or `SIGUSR2` or in
  regular intervals when requested with `--progress`
- portscan: Report commented `PORTEPOCH` or `PORTREVISION` lines
  via new `lint.commented-portrevision` lint, selectable with
  `--comments`, enabled by default
- portedit: `apply list` will now print a list of available edits
- portclippy, portscan: Make sure ports have the required `USES`
  before accepting variables as "known"
- portclippy: provide hints which `USES` might be missing
- portclippy: Check `opt_USE` and `opt_VARS` for unknowns too
- portclippy: provide hints for wrong case variable misspellings, e.g.,
  for `license` it will suggest using `LICENSE` instead

### Changed

- Recognize more framework targets
- Catch up with FreeBSD Ports:
  - Remove support for `PKGUPGRADE` and friends
  - Add `USES=ansible`, `USES=cmake:testing` support
- portclippy, portscan: Report unknown target sources too
- portscan: default `-p` to `/usr/ports` or the value of `PORTSDIR` in the environment
- portedit, portfmt: Stop messing with inline comments.  This should let it
  deal better with the commonly used `PATCHFILES+=<commit>.patch # <pr>`
  pattern. This disables `refactor.sanitize-eol-comments` by default but it is
  still accessible with `portedit apply refactor.sanitize-eol-comments`.
- portedit: `merge` now tries to only append to the last variable in
  "`+=` groups".  Something like
  `portedit merge -e 'PATCHFILES+=deadbeef.patch:-p1 # https://github.com/t6/portfmt/pulls/1'`
  should work now as one would expect.
- portscan: Replaced `-o <check>` with `--<check>`; `-o <check>`
  will continue to work but is deprecated
- portedit merge: Ignore variables in conditionals

### Fixed

- portclippy, portscan: Do not report on targets defined in `POST_PLIST`
- Do not recognize false options helper targets like `makesum-OPT-on`
- Properly split target names and dependencies.  This improves
  overall reporting on targets in portclippy and portscan
- portfmt: Do not try to sort tokens in `*_CMD`
- portedit: print right usage for `apply`
- Ignore `NO_COLOR` when `CLICOLOR_FORCE` is set and force colors
  on per the FAQ on https://no-color.org/
- portclippy: check slave ports again.  The check if a Makefile
  is a FreeBSD Ports Makefile is flawed and is now also positive
  if `MASTERDIR` is set in it.
- portclippy, portscan: Look up `opt_USES_OFF` and `opt_VARS_OFF` too
- portedit set-version: Deal with `PORTREVISION?=` and reset it to 0
- portedit, portfmt: Ignore `-i` when `-D` was specified
- portedit bump-epoch: Reset `PORTREVISION` on `PORTEPOCH` bump

## [g20210321] - 2021-03-21

### Added

- portscan: Report on option descriptions that fuzzy match the default descriptions
  in `Mk/bsd.options.desc.mk`.  Enabled by default but is also
  selectable with `-o option-default-descriptions`.

### Changed

- Format `UNIQUE_PREFIX_FILES` and `UNIQUE_SUFFIX_FILES` similar to `PLIST_FILES`
- Recognize `DO_MAKE_BUILD` and `DO_MAKE_TEST`
- Recognize `makeplist` overrides
- Leave `CFLAGS`, `MAKE_FLAGS`, etc. unsorted
- Catch up with FreeBSD Ports:
  - Add new vars like `GO_MODULE`, `KDE_INVENT`
  - Update known `USES={gnome,kde,pyqt,qt}` components
  - Recognize `*_FreeBSD_14` variables
  - Recognize `USES=emacs` flavors

### Fixed

- portclippy: Refuse to check non-FreeBSD Ports files
- portedit, portfmt: `-D` produces less cluttered unified diffs with reduced context.
  3 lines of context by default but more can be asked for with an
  optional argument to `-D`.  Use `-D0` to get the full context as before.
- portscan: Handle `.include` with `${.PARSEDIR}`

## [g20200924] - 2020-09-24

No changelog for old releases.
