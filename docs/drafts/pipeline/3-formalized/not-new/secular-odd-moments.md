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

## Update: conjugate parity (critical-line reflection)
`xi_secular_moment_conj_parity (R n)`: the reflection ρ↦1−conj ρ (fixed set = critical line) preserves the ½-ball ξ-divisor, giving `conj(M_n) = (−1)^n M_n` — even centered moments real, odd ones purely imaginary. The FE reality constraint on the ξ-divisor, RH-relevant (this is the reflection whose fixed locus is the critical line). Axiom-clean.

## Update: off-line multiplicity parity
`xi_offline_multiplicity_even_ball (R)`: the total order of off-critical-line ξ-zeros (Re≠½) in a ½-ball is even — the critical-line reflection ρ↦1−conj ρ is a fixed-point-free involution on them, preserving multiplicity (via Finset.sum_involution in ZMod 2). Off-line zeros occur in reflected pairs of equal multiplicity. Axiom-clean.

## Update: Klein-four divisibility-by-4
`xi_generic_multiplicity_div_four_ball (R)`: the total order of ξ-zeros off BOTH symmetry axes (Re≠½ AND Im≠0) in a ½-ball is divisible by 4 — the full Klein-four group ⟨ρ↦1−ρ, ρ↦conj ρ⟩ acts freely, so generic zeros occur in 4-tuples {ρ,1−ρ,conj ρ,1−conj ρ}. Proof: conjugation halves the sum onto the upper half (Im>0), where the critical-line reflection ρ↦1−conj ρ halves it again. Axiom-clean.
