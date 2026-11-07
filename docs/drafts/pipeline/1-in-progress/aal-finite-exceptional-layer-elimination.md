# AAL: elimination of a finite exceptional zero layer

- **ID:** aal-finite-exceptional-layer-elimination
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** `RHTower.AsymptoticAbscissaLaw` for the actual Riemann zeta function, without additional mathematical hypotheses.

## Goal

Prove or disprove AAL, then formalize the decision and its consequences. Structural implications and model counterexamples do not decide this statement.

## Current mathematical target

Under negated AAL, the existing spectral-gap theorem isolates finitely many zeros at `β* > β₁ ≥ 1/2`. Eliminate this configuration using the ordinary integer Dirichlet series together with the high-height zero-free region. A return bound must hold at the selected phase-return heights; a density-one estimate is insufficient.

## Proof status

No unconditional decision established. The existing transport theorem requires locally bounded translates; the spectral-gap theorem does not supply this bound. No Lean theorem is claimed here.

The two-prime annihilator theorem proves finiteness, not emptiness. The affine Haar obstruction requires an additional kernel extension not supplied by finite zero support. The head-conditioned Euler-tail mean at critical resonator length still lacks its required arithmetic inequality.

`PositiveAnnihilator.exists_xi_zero_annihilator_with_multiplicities` gives every finite set of actual xi zeros, with arbitrary prescribed finite orders, a nonnegative finite Dirichlet annihilator supported on powers of 2 and 3, with constant coefficient 1 and arbitrarily small uniform error from 1 on `Re s ≥ 1`. Positivity and right-half-plane accuracy of finite deflation therefore add no exclusion of a finite layer.

`IntegerNormOneOff.exists_integer_norm_linear_count_one_off` constructs an Euler product with natural-number generator norms, natural Dirichlet coefficients, positive linear counting `N(x) ∼ A x`, and exactly the zero pair `3/5 ± iγ` on `Re s > 1/2`, away from `1`. These properties together are insufficient. A power-saving counting error and the functional equation remain uncontrolled. The actual zeta problem must retain stronger arithmetic information, such as its exact counting function or full functional equation.

`RationalPrimeOneOff.exists_rational_prime_multiplicative_linear_count_one_off` gives a rational-prime analogue with ordinary multiplicative natural coefficients and positive linear counting. Its continuation has exactly the same pair on `Re s>17/30`, away from `1`. Prime labels may repeat; continuation throughout `Re s>1/2`, polynomial vertical growth, and the Riemann functional equation remain unproved for this model. See `3-formalized/rational-prime-beurling-one-off.md`.

## Gates

- [x] Exact statement and existing reductions checked in Lean source.
- [ ] Dependency-closed proof or disproof for the actual zeta function.
- [ ] Lean formalization with transitive axiom audit.
- [ ] Implications and corollaries formalized; relevant umbrellas wired.
