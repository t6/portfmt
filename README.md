# portfmt

Portfmt is a tool for formatting FreeBSD Ports Collection Makefiles.

For the time being portfmt concentrates on formatting individual
variables as such it does not move variables to preferred positions.

## Example

A Makefile like this
```
LICENSE_PERMS=  dist-mirror pkg-mirror auto-accept dist-sell pkg-sell

RUN_DEPENDS+=   ${PYTHON_PKGNAMEPREFIX}paho-mqtt>=0:net/py-paho-mqtt@${PY_FLAVOR}
RUN_DEPENDS+=   ${PYTHON_PKGNAMEPREFIX}supervisor>=0:sysutils/py-supervisor@${PY_FLAVOR}

USES=           cmake \
                compiler:c++11-lib \
                desktop-file-utils \
                gettext-tools \
                pkgconfig \
                qt:5 \
                sqlite \
                gl
USE_QT=         buildtools_build \
                concurrent \
                core \
                dbus \
                gui \
                imageformats \
                linguist_build \
                network \
                opengl \
                qmake_build \
                testlib_build \
                sql \
                widgets \
                x11extras \
                xml

FOOBAR_CXXFLAGS=	-DBLA=foo # workaround for https://github.com/... with a very long explanation
```
is turned into
```
LICENSE_PERMS=	dist-mirror dist-sell pkg-mirror pkg-sell auto-accept

RUN_DEPENDS+=	${PYTHON_PKGNAMEPREFIX}paho-mqtt>=0:net/py-paho-mqtt@${PY_FLAVOR} \
		${PYTHON_PKGNAMEPREFIX}supervisor>=0:sysutils/py-supervisor@${PY_FLAVOR}

USES=		cmake compiler:c++11-lib desktop-file-utils gettext-tools gl \
		pkgconfig qt:5 sqlite
USE_QT=		concurrent core dbus gui imageformats network opengl sql widgets \
		x11extras xml buildtools_build linguist_build qmake_build \
		testlib_build

# workaround for https://github.com/... with a very long explanation
FOOBAR_CXXFLAGS=	-DBLA=foo
```

### But it does not format things like I want to...

Please create an example Makefile and put it into
`tests/${your_example}.in` and create a corresponding
`tests/${your_example}.expected` showing what it should look like
according to you.  Then open a PR.  Some actual code to fix it is
appreciated but not required.  The important thing is to have a
test case for it.  Even if it currently fails.  In the commit message
try to write down and provide some evidence why you think the current
behavior is bad or wrong.

## Usage

Please see `portfmt(1)`. The basic usage is
```
$ portfmt Makefile
```
Portfmt reads from stdin if no Makefile is given on the command
line which facilitates integrating it into your favourite editor.

## Editor integration

You can integrate Portfmt into your editor to conveniently run it
only on parts of the port, e.g., to reformat `USES` after adding a
new item to it.

### Emacs

Add this to `~/.emacs.d/init.el` to format the current region with
`C-c p`.

```
(defun portfmt (&optional b e)
  "PORTFMT(1) on region"
  (interactive "r")
  (shell-command-on-region b e "portfmt " (current-buffer) t
                           "*portfmt errors*" t))
(define-key makefile-bsdmake-mode-map (kbd "C-c p") 'portfmt)
```

### Kakoune

Add this to `~/.config/kak/kakrc` for filtering the current selection
through portfmt with `,1`:
```
map global user 1 '|portfmt<ret>;' -docstring "portfmt on selection"
```

### Vim

Add this to `~/.vimrc` for filtering the current selection through
portfmt with `\1`:
```
xnoremap <leader>1 <esc>:'<,'>!portfmt<CR>
```
