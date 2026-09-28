MC route, 2026-09-28 (root session). New Lean module RHTower/MobiusGammaHankelSubOrthogonality.lean (wired after MobiusLaplaceMellinPlancherelBridge in RHTower.lean; leaf `lake build --old` green; axioms propext/Classical.choice/Quot.sound).

Theorems:
- exists_order_vertical_window_floor_of_canonical_identity: boundary zero of analytic order n ⇒ Mellin floor c/r^n on window radius r at σ+r (generalizes corpus c/r floor).
- memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le: cutoff-uniform energy ceiling B ⇒ infinite source L² norm² ≤ B (Fatou).
- two_mul_analyticOrderAt_toNat_le_of_powerApertureCeiling: E_{2σ}(N) ≤ C/(2σ−1)^k on (1/2,σ₀) ⇒ RH and 2·order ≤ k+1 for every strip zero (blow-up exponent ↔ multiplicity law).
- reciprocalApertureCeiling_of_subOrthogonal: diag ≤ 2/(r−1) on 1<r≤2 (Γ≤1 by convexity, p-series tail).
- riemannHypothesis_and_simple_zeros_of_subOrthogonal: off-diagonal Γ–Hankel Möbius covariance ≤ 0 for all N, r∈(1,2σ₀) ⇒ RH ∧ every strip zero has order 1 and ζ'(ρ)≠0.

Conjecture (open, RH-strength): sub-orthogonality SO. Rank-one kernel version = Mertens (false). Γ version plausible under RH+simple zeros: zero coefficient Σ|Γ(ρ)|²/|ζ'(ρ)|² ~1e-18 vs diagonal 0.304/(r−1). Random multiplicative twists have E[offdiag]=0, so SO is non-generic (μ is antiferromagnetic on the Γ–Hankel graph). SO ⇔ Rayleigh quotient of μ for the Γ–Hankel graph Laplacian ≥ 1 ⇔ Plancherel bound of M_N on Re s=r/2 (circular as producer).

New-field conjecture (loop card cycle 22): discrete multiplicative uncertainty — for discrete Beurling [α,β,γ] (Hilberdink–Neamah exponents), Θ ≤ max(1/2, 2β); implies RH and (β₀>0.315) GRH for χ₋₄. Continuous systems violate maximally; explains every Beurling firewall. Literature: Hilberdink 2005, Hilberdink–Neamah IJNT 2020 (Θ≥1/2, two-equal rule, conj. no [1/2,1/2,0]), Broucke–Vindas arXiv 2102.08478 ([0,1/2,1/2] exist).

Cards: docs/drafts/pipeline/3-formalized/mobius-gamma-hankel-sub-orthogonality.md; loop log docs/drafts/pipeline/1-in-progress/mc-conjecture-loop-2026-09-28.md (23 cycles).