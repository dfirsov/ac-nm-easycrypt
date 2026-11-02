#!/bin/bash
# Check every .ec file of the development in one pass, and check that the
# checker rejects two false statements.  Writes check_all.log here.
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
LOG=check_all.log
{
  echo "date:       $(date -Iseconds)"
  ECBIN="$(command -v "$EASYCRYPT")"
  ECSRC="$(cd "$(dirname "$ECBIN")/../../../.." 2>/dev/null && git rev-parse HEAD 2>/dev/null)"
  echo "easycrypt:  $ECBIN ${ECSRC:+(commit $ECSRC)}"
  echo "provers:    $("$EASYCRYPT" config 2>&1 | grep 'known provers')"
  echo "options:    -timeout 10 -p Alt-Ergo -no-eco (each file compiled separately)"
  echo
  fail=0
  for f in *.ec; do
    if grep -qw "admit" "$f"; then echo "ADMIT   $f"; fail=1; continue; fi
    start=$(date +%s)
    if "$EASYCRYPT" compile -I . -timeout 10 -p Alt-Ergo -no-eco "$f" >/dev/null 2>"/tmp/ec_err_$$"; then
      echo "OK      $f  ($(( $(date +%s) - start ))s)"
    else
      echo "FAILED  $f"; sed 's/^/        /' "/tmp/ec_err_$$" | grep -v '^\s*\[warning\]' | head -5; fail=1
    fi
  done
  # negative tests: the checker must reject a false lemma and a false
  # strengthening of a proved bound (cond_unsat: 1/12 -> 1/11)
  NEG=$(mktemp -d)
  cp negtests/Neg_false.ec "$NEG/"
  sed 's|  1%r / 12%r - gamma|  1%r / 11%r - gamma|' Cand_Cond.ec > "$NEG/Neg_cond11.ec"
  if cmp -s Cand_Cond.ec "$NEG/Neg_cond11.ec"; then echo "NEGTEST mutation did not apply"; fail=1; fi
  for n in "$NEG"/*.ec; do
    if "$EASYCRYPT" compile -I . -timeout 10 -p Alt-Ergo -no-eco "$n" >/dev/null 2>&1; then
      echo "NEGTEST ACCEPTED (checker unsound?)  $(basename "$n")"; fail=1
    else
      echo "NEGTEST rejected as expected       $(basename "$n")"
    fi
  done
  rm -rf "$NEG" "/tmp/ec_err_$$"
  echo
  [ $fail = 0 ] && echo "ALL $(ls *.ec | wc -l) FILES OK, NEGATIVE TESTS REJECTED" || echo "SOME FILES FAILED"
} | tee "$LOG"
