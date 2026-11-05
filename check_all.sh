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
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
set -o pipefail

# A negative test passes only if EasyCrypt reports "cannot prove goal" in the
# test file itself, at or after the line of the false statement.  Any other
# failure (missing binary, parse or type error, failed import) counts as a
# failure of the test harness.
negtest() {  # negtest FILE FIRSTLINE
  local f="$1" first="$2" err="$TMP/neg_err"
  if "$EASYCRYPT" compile -I . -timeout 10 -p Alt-Ergo -no-eco "$f" >/dev/null 2>"$err"; then
    echo "NEGTEST ACCEPTED (checker unsound?)  $(basename "$f")"; return 1
  fi
  local line
  line=$(tr '\r' '\n' < "$err" | grep -F "[critical] [$f: line " | grep -F "cannot prove goal" \
         | head -1 | sed -E 's/.*: line ([0-9]+).*/\1/')
  if [ -n "$line" ] && [ "$line" -ge "$first" ]; then
    echo "NEGTEST rejected as expected       $(basename "$f")  (cannot prove goal, line $line)"
  else
    echo "NEGTEST FAILED FOR ANOTHER REASON  $(basename "$f")"
    tr '\r' '\n' < "$err" | grep -F "[critical]" | sed 's/^ */        /' | head -3
    return 1
  fi
}

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
    if "$EASYCRYPT" compile -I . -timeout 10 -p Alt-Ergo -no-eco "$f" >/dev/null 2>"$TMP/err"; then
      echo "OK      $f  ($(( $(date +%s) - start ))s)"
    else
      echo "FAILED  $f"; tr '\r' '\n' < "$TMP/err" | grep -F "[critical]" | sed 's/^ */        /' | head -5; fail=1
    fi
  done
  # negative tests: the checker must reject a false lemma and a false
  # strengthening of a proved bound (cond_unsat: 1/12 -> 1/11)
  NEG="$TMP/neg"; mkdir "$NEG"
  cp negtests/Neg_false.ec "$NEG/"
  negtest "$NEG/Neg_false.ec" "$(grep -n '^lemma bad' negtests/Neg_false.ec | cut -d: -f1)" || fail=1
  sed 's|  1%r / 12%r - gamma|  1%r / 11%r - gamma|' Cand_Cond.ec > "$NEG/Neg_cond11.ec"
  mline=$(grep -n '  1%r / 11%r - gamma' "$NEG/Neg_cond11.ec" | cut -d: -f1)
  if [ -z "$mline" ] || cmp -s Cand_Cond.ec "$NEG/Neg_cond11.ec"; then
    echo "NEGTEST mutation did not apply"; fail=1
  else
    negtest "$NEG/Neg_cond11.ec" "$mline" || fail=1
  fi
  echo
  if [ $fail = 0 ]; then
    echo "ALL $(ls *.ec | wc -l) FILES OK, NEGATIVE TESTS REJECTED"
  else
    echo "SOME CHECKS FAILED"
  fi
  exit $fail
} | tee "$LOG"
