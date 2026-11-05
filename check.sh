#!/bin/bash
# usage: ./check.sh FILE.ec [LINE[:COL]]   -- prints only errors (or goals with LINE)
# EasyCrypt: $EASYCRYPT if set; otherwise a local build in ../tools/easycrypt
# (the pinned commit, see README); otherwise `easycrypt` on the PATH.
LOCAL_EC="$(cd "$(dirname "$0")" && pwd)/../tools/easycrypt"
if [ -z "$EASYCRYPT" ]; then
  if [ -x "$LOCAL_EC/_build/install/default/bin/easycrypt" ]; then
    EASYCRYPT="$LOCAL_EC/_build/install/default/bin/easycrypt"
    export PATH="$HOME/.opam/ec/bin:$PATH"   # provers of the local opam switch
  else
    EASYCRYPT=easycrypt
  fi
fi
cd "$(dirname "$0")"
if [ -n "$2" ]; then
  "$EASYCRYPT" llm -I . -timeout 10 -p Alt-Ergo -upto "$2" "$1" 2>&1 | grep -v '^\[warning\]'
  exit "${PIPESTATUS[0]}"
else
  "$EASYCRYPT" llm -I . -timeout 10 -p Alt-Ergo "$1" 2>&1 | grep -v '^\[warning\]'
  status=0
  if grep -nw "admit" "$1"; then echo "ADMITS in $1"; status=1; fi
  if "$EASYCRYPT" compile -I . -timeout 10 -p Alt-Ergo -no-eco "$1" >/dev/null 2>&1; then
    echo "OK: $1"
  else
    echo "FAILED: $1"; status=1
  fi
  exit $status
fi
