# WP03: improving prime variance from Toeplitz ceilings alone

- **ID:** weil-work-03-toeplitz-prime-variance
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** docs/reports/weil-work/03-singular-arithmetic-detection.md;
  in-progress/weil-work-03-singular-arithmetic.md, cycles23–27.
- **Statement:** The complete logarithmic multiplicative Toeplitz ceiling
  forces eventual prime-square mass at most theta*(log N)^2 for some theta<1.

## Goal

Improve the corpus's constant1 to the canonical constant1/2 by increasingly
coupled prime/divisor resonators. This subroute uses only the extracted
ceilings. The conjecture with the full Weil-positive source remains OPEN.

## Gates

- [x] Exact relaxation and all-cutoff counterexample specified.
- [x] Dependency-closed paper proof in WP03 PROOF.md, cycle27.
- [x] Positive survivor formalized; leaf build, direct check, axioms audited.
- [ ] Publication-level novelty established. No such claim is made.

## Approach

For N<p^2, multiplication by p on[1,N] gives a matching, so its symmetric
shift form has budget1. At arbitrary N its budget is at most2. Choose primes
p_j with log p_j >=2*(j+2)*sum_(i<j)log p_i. Set
b_j=(j+1)/(j+2)*log p_j and lambda(p_j)=sqrt(p_j)*b_j, zero elsewhere.
At each cutoff, the newest matching plus all older shifts costs at most
log N. After its square enters, twice the complete amplitude sum still
costs at most log N. This retains all complex test vectors and cutoffs.

## No-go closure

- **Exact killing theorem:**
  `RHTower.WeilSingularArithmetic.exists_sharp_prime_supported_toeplitz_weight`.
  One nonnegative prime-supported sequence satisfies every logarithmic
  Toeplitz ceiling with C=0 and exceeds each smaller prime-square constant
  at arbitrarily large cutoffs.
- **Strongest positive survivor:** the same explicit infinite construction
  has square mass <=(log N)^2 at every N>=1. The leading constant1 is sharp
  for the entire relaxation, not merely for one star or four-point matrix.
- **New insight:** adding divisor layers or varying the cutoff cannot recover
  a constant<1 from this extracted family. A source-level improvement must
  use information lost by the Toeplitz estimate. The sparse witness is not
  asserted Weil-positive; the corpus's sparse-support obstruction excludes
  this type of source. No detector counterexample is claimed.
- **Status:** positive survivor LEAN in
  `formal/GaloisForLFunctions/RHTower/WeilWorkSingularArithmeticToeplitzSharpness.lean`.
  Targeted `lake build --old +...` and final `lake env lean <leaf>` exit0;
  all six public theorem axioms are propext, Classical.choice, Quot.sound.
  Import wired into RHTower; no umbrella build or heartbeat increase.
- **Novelty:** exact new corpus barrier; classical shift bounds and lacunary
  separation are parent mechanisms. Corpus searches were partial, with
  returned candidates inspected; no publication novelty claim. Primary
  operator calibration: Gaaya, arXiv:1202.3962, Theorem1.6.

## Log

- 2026-10-07 — all-cutoff counterexample and matching positive survivor
  proved and formalized; retire only the Toeplitz-only variance subroute.
