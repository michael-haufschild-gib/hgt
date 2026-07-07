# Secular odd moments of ξ's zeros vanish (τ_{2m+1}=0 for the actual ξ)

- **ID:** secular-odd-moments
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean
- **Source:** instantiates FunctionalEquationParity.fe_centered_odd_moment_vanish on the genuine ξ-divisor
- **Statement:** `xi_secular_odd_moment_ball_eq_zero (R m)` — for every radius R and every m, the multiplicity-weighted centered odd moment of ξ's zeros in the ball ‖s−½‖<R vanishes: `∑_{ρ: ‖ρ−½‖<R, ξ(ρ)=0} ord_ρ(ξ)·(ρ−½)^{2m+1} = 0`. The FE pairs ρ↦1−ρ (same multiplicity via xi_orderAt_one_sub, reflected through ½); odd power ⟹ cancellation; fixed point ½ contributes 0 (via Finset.sum_involution).
- **Lean:** `RHTower.xi_secular_odd_moment_ball_eq_zero` in `formal/GaloisForLFunctions/RHTower/SecularOddMoments.lean`. Axiom-clean. `lake build` green.

## What this is
The HT-field foundations (§22) prove the abstract σ-parity (odd moments of a negation-invariant multiset vanish) but never instantiate it on the real object. This composes it with the finite ball-zero machinery (xi_zeros_finite_ball) + the FE order symmetry (xi_orderAt_one_sub) to give the secular odd moments for the ACTUAL ξ, unconditionally, on every ½-centered ball. A genuine HT-field theorem about the ξ-divisor, not a reframing.

## Log
- 2026-07-07 — created directly in 3-formalized.
