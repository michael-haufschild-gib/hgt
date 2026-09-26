# Hardy rigidity of ξ in the module θ₃·ℝ[h]

- **ID:** route2-charge-line-hardy-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** 1-in-progress/route2-modular-criticality-cusp-charge (cusp-charge law); route-proposals/route2.md steps 3, 5–6.
- **Statement:** For P ∈ ℝ[X], P ≠ 0, let Ξ_P be the transform of the exactly Γ_θ-modular weight-½ form θ₃P(h), h = θ₂⁴θ₄⁴/θ₃⁸. Then Ξ_P has infinitely many real zeros iff deg P = 0 (Ξ_P = cΞ). For deg P ≥ 1: finitely many real zeros, infinitely many nonreal zeros. (Charge line P = 1 + sX is the first case.)

## Goal
Hardy's theorem (infinitely many critical zeros) is itself rigid inside the exactly Γ_θ-modular
weight-½ line through ξ: it holds only at zero cusp-1 charge. For small |s| the source of F_s is
real and strictly positive (`thetaGroup_modular_criticality`), so positivity + exact modularity +
evenness + integer spectrum do not even give infinitely many real zeros.

## Gates
- [x] 0 → 1  well-posed, source-pure
- [x] 1 → 2  paper proof: dominance law ⇒ real zeros bounded; order ≤ 3/2 + two-ray decay ⇒ infinitely many zeros (Hadamard, corpus `zeroSet_infinite_of_subquadratic_twoRayDecay`)
- [x] 2 → 3  Lean: `RHTower.formXi_real_zeros_infinite_iff`, `RHTower.thetaGroupForm_hardy_rigidity` (module ThetaCuspChargePolynomialRigidity; chain ThetaCuspChargePow*), charge-line case `RHTower.chargeLine_hardy_rigidity`; axioms propext/choice/Quot.sound; lint pass
- [ ] 3 → 4  not pursued (no stage 4)

## Approach
1. `cuspCharge_law` ⇒ ‖Ξ(u)‖ ≤ (|s|/2)‖Ξ₁(u)‖ and Re Ξ₁(u) < 0 for u ≥ U(s) ⇒ Ξ_s(u) ≠ 0 there; evenness and isolated zeros ⇒ finitely many real zeros.
2. Cubic source envelope ‖k₁(x)‖ ≤ K e^{−|x|³−|x|} ⇒ ‖Ξ₁(z)‖ ≤ exp(C(1+‖z‖)^{3/2}); `XiC_order` ⇒ same for Ξ.
3. Riemann–Lebesgue ⇒ Ξ_s → 0 on both real rays ⇒ infinitely many zeros; minus finitely many real ones.

## General-degree mechanism
Top degree n+1 has pole order m = 8n+7 at cusp 1: window law θ₃hⁿ⁺¹(1−1/v) = (−1)ⁿ⁺¹(−iv)^{1/2}2^{−m}e^{−mπiv/4}(1+ε);
exact saddle u = mπ/(8a²), unit phase (−1)ⁿ⁺¹·(−1)ⁿ⁺¹ = 1; Farey cap R₀/3; lower orders j ≤ n are smaller on the same
line by e^{−(R₀−R₀')} ≤ e^{−1/t²}; Ξ itself by e^{−R₀}.

## No-go closure
- **Killing mechanism:** nonzero charge at cusp 1 makes Ξ₁ dominate Ξ on the whole real tail (saddle at the pole cusp).
- **Strongest positive survivor:** this theorem (ξ is the unique point of its charge line with infinitely many real zeros).
- **New insight:** on this line, "infinitely many real zeros" ⟺ s = 0 ⟺ R₂ (prime-2 relation, F10). The Mellin-diagonal R₂ is recovered as a zero-counting property on the line, but only through the pole-cusp saddle, not through a diagonal mechanism.
- **Status:** dependency-closed; Lean-certified.

## Log
- 2026-09-26 — conjectured from the cusp-charge law (dominance holds for every s ≠ 0); proved and formalized the same day.
- 2026-09-26 — affine form with levels (`formXi_level_real_infinite_iff`) and route step 4 (`XiC_level_specificity`), module ThetaCuspChargeLevelSpecificity.
- 2026-09-26 — generalized to all of θ₃·ℝ[h] (pole order 8n+7 saddles, same-line lower-order domination, linearity); Lean-certified.
