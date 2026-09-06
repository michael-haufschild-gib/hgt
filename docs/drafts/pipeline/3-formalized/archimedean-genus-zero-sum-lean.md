# The archimedean genus equals the regularised zero count (Lean)

- **ID:** `archimedean-genus-zero-sum-lean`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional, no RH premise)
- **Lean:** `RHTower.ArchimedeanGenusZeroSum` (wired into `RHTower`; axioms
  `[propext, Classical.choice, Quot.sound]`; 8805-job closure through `XiHadamardGrowth`,
  `CanonicalProductE1LogDeriv`, `PoleSelfEnergyLimit`).
- **Parents:** `1-in-progress/fixed-pole-zero-margin-law.md`, `3-formalized/mertens-euler-constant-lean.md`.

## Statement

`tsum_inv_zero_mul_one_sub_zero : ∑' q : XiZeroCopy, 1/(ρ_q(1−ρ_q)) = 2 + γ − log 4π` (as complex
numbers; `tsum_inv_zero_mul_one_sub_zero_re` for the real part), where `XiZeroCopy` enumerates the
nontrivial zeros of `ξ` with their divisor multiplicity. The right side is `poleSharpConstant`, the
limit of `A(a)e^{−a}` for the exponential-pole self-energy (`PoleSelfEnergyLimit`).

Also: `completedRiemannZeta₀_one : Λ₀(1) = 1 + (γ − log 4π)/2` (the first Li coefficient
`λ₁ = ξ'(1)/ξ(1)`), `hasDerivAt_xi_one`, `logDeriv_XiC_neg_I_half : logDeriv XiC (−I/2) = I·Λ₀(1)`,
`tsum_logDerivTerm_eq` (reflection symmetrisation of the Mittag-Leffler sum).

## Proof

Mathlib's `ζ(s) − 1/(Γℝ(s)(s−1)) → (γ − log 4π)/2` and `Λ = Λ₀ − 1/s − 1/(1−s)` give
`(Λ₀(s) − 1/s)/Γℝ(s) → Λ₀(1) − 1`, hence `Λ₀(1)`. With `ξ(s) = s(s−1)Λ₀(s)/2 + 1/2`,
`ξ'(1)/ξ(1) = Λ₀(1)`. The corpus's `XiC = XiC(0)·Π_q E₁(z/t_q)` and
`logDeriv_canonicalProductE1Indexed` give `logDeriv XiC z = Σ'_q [(z−t_q)⁻¹ + t_q⁻¹]`; at
`z = −I/2` (the point `s = 1`) the reflection `t ↦ −t` (`xiZeroCopyReflectEquiv`) pairs the terms to
`I/(¼ + t_q²)` and `¼ + t_q² = ρ_q(1−ρ_q)`. Comparing, `Σ' 1/(ρ_q(1−ρ_q)) = 2Λ₀(1)`.

## Novelty

The identity `Σ_ρ 1/ρ = 1 + γ/2 − ½log 4π` is classical (Riemann's era); its role as the exact
leading constant of the two-pole Weil criterion, and the resulting reading of that criterion as the
archimedean Weil bound with regularised genus, are the corpus's (MUST-229/231). The Lean theorem
is the first certified link in this corpus between a prime-side limit (Mertens/Gamma) and a
zero-side sum over the actual divisor of `ξ` counted with multiplicity.
