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

The two-prime annihilator theorem proves finiteness, not emptiness. The affine Haar obstruction requires an additional kernel extension not supplied by finite zero support. The next candidate couples the finite prime-error profile to a head-conditioned Euler-tail mean at critical resonator length; its required arithmetic inequality is unproved.

## Gates

- [x] Exact statement and existing reductions checked in Lean source.
- [ ] Dependency-closed proof or disproof for the actual zeta function.
- [ ] Lean formalization with transitive axiom audit.
- [ ] Implications and corollaries formalized; relevant umbrellas wired.
