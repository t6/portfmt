BEGIN {
	reset()
}

function reset() {
	varname = "<unknown>"
	tokens_len = 1
	print_as_tokens = 1
}

function print_tokens() {
	if (tokens_len <= 1) {
		return;
	}
	sort_array(tokens, tokens_len)
	if (print_as_tokens == 1) {
		print_token_array(sprintf("%s=", varname), tokens, tokens_len)
	} else {
		print_newline_array(sprintf("%s=", varname), tokens, tokens_len)
	}
	reset()
}

/^[A-Za-z_]+[?+]?=/ {
	print_tokens()
}

/^#/ {
	skip = 1
	print
}

/^[ \t]*$/ {
	skip = 1
	print
}

/^[a-zA-Z_]+_DEPENDS[+?]=/ {
	print_as_tokens = 0
}

/^[A-Z_]+_ARGS[+?]?=/ {
	print_as_tokens = 0
}

!skip {
	if (match($0, /^[A-Z_+?]+=/)) {
		varname = substr($0, RSTART, RLENGTH - 1)
		i = 2
	} else {
		i = 1
	}
	for (; i <= NF; i++) {
		if ($i == "\\") {
			break
		}
		tokens[tokens_len++] = $i
	}
}

skip {
	skip = 0
}

END {
	print_tokens()
}
