# Sharp integral torsion interpolation

- **ID:** alst-sharp-integral-torsion-interpolation
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Modulo `J_q^r`, every integer polynomial has a unique Newton remainder supported on `Σ_p floor(a_p/q)<r`; it minimizes arithmetic length in its class. For nonempty `P` and `r>0`, all integral classes admit representatives of length at most `N` exactly when `N ≥ (∏_p p^(q−1)) p_max^(q(r−1))`.

## Purpose
Determine the exact length needed to interpolate every admissible integral torsion jet. This is an arithmetic interpolation threshold for S1/S3 on the full torsion grid, not a claim about zeros on the prime orbit or separation of zeta from other Euler products.

## Proof route
Split the integral Newton coordinates into quotient orders below and at least `r`. The latter part is exactly `J_q^r`; the former is the unique remainder. Exact preservation of arithmetic length by Newton synthesis makes its length minimal in its congruence class. Every low-order index has remainder exponents at most `q−1` and at most `r−1` quotient blocks, so its weight is at most the displayed threshold. Equality is attained by putting every remainder exponent at `q−1` and all quotient blocks on the largest prime. That single Newton class forces the lower bound for every representative.

## Gates
- [x] Corpus search found no exact integral interpolation threshold or length-minimizing quotient representative.
- [ ] Dependency-closed paper proof and boundary cases.
- [ ] Lean formalization and transitive axiom audit.

## Dependency
Filtered integral torsion normal form; its final Lean audit is pending. No interpolation result is counted as proved.
