#!/usr/bin/env bash
# Axiom + sorry audit for the GaloisForLFunctions Tier A formalization.
# Fails if audited theorem dependencies deviate from
# [propext, Classical.choice, Quot.sound], or if any real `sorry` token appears.
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")/../formal" && pwd)"
command -v lake > /dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"
SCRATCH="$(mktemp -t galois-axcheck-XXXXXX).lean"
trap 'rm -f "$SCRATCH"' EXIT

cat > "$SCRATCH" << 'EOF'
import GaloisForLFunctions
#print axioms GaloisForLFunctions.sigma_involutive
#print axioms GaloisForLFunctions.cpow_inversion_scale
#print axioms GaloisForLFunctions.norm_cpow_neg_eq_rpow_re
#print axioms GaloisForLFunctions.norm_cpow_eq_critical_iff
#print axioms GaloisForLFunctions.localEulerFactor_relation
#print axioms GaloisForLFunctions.localEulerFactor_ne_zero
#print axioms GaloisForLFunctions.finiteEulerProduct_ne_zero
#print axioms GaloisForLFunctions.primeProduct_factorization
#print axioms GaloisForLFunctions.primeProduct_injective
#print axioms GaloisForLFunctions.log_prime_nat_relation_eq
#print axioms GaloisForLFunctions.log_prime_int_relation_eq_zero
#print axioms GaloisForLFunctions.logPrime_linearIndependent_int
#print axioms GaloisForLFunctions.linearIndependent_log_primes
#print axioms GaloisForLFunctions.logPrime_no_rat_relation
#print axioms GaloisForLFunctions.isMultiplicative_iff_bohr_factorization
#print axioms GaloisForLFunctions.fake_fails_factorization
EOF

cd "$FORMAL_DIR"
OUT="$(lake env lean "$SCRATCH")"
echo "$OUT"

EXPECTED="[propext, Classical.choice, Quot.sound]"
COUNT="$(printf '%s\n' "$OUT" | grep -cF "depends on axioms: $EXPECTED")"
if [ "$COUNT" -ne 16 ]; then
  echo "FAIL: expected all 16 audited theorems to depend on exactly $EXPECTED" >&2
  exit 1
fi
if printf '%s\n' "$OUT" | grep -q "sorryAx"; then
  echo "FAIL: sorryAx present" >&2
  exit 1
fi
if grep -rnE '(^|[^A-Za-z_])sorry([^A-Za-z_]|$)' --include='*.lean' GaloisForLFunctions/ GaloisForLFunctions.lean \
    | grep -vE '^\S+:[0-9]+:\s*(--|/-|`| \*)'; then
  echo "FAIL: sorry token found in tree" >&2
  exit 1
fi

echo "PASS: Tier A/B elementary theorems axiom-clean ($EXPECTED), no sorry (16 theorems audited)."
