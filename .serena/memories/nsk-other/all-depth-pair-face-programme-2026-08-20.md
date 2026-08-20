# All-depth pair-face signature theorem — Lean programme (2026-08-20)

Closes the remaining mathematics of **two** stage-2 cards:
`all-depth-pair-face-signature-completeness` and (via its module isomorphism `(5)`) formula `(1)`
of `all-depth-compatible-pair-face-differential-matroid`.

## Depth-two base — already in the tree, axiom-clean

```text
HTGeometry.differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero   (TripticCompleteness)
additiveOrbitalDivisorAt F σ p ℓ = ∑ᶠ m : ℤ, laurentCoeff (Δ_σ F) (p + m σ) ℓ
```
plus `TripticMultiplicativeKernelConverse`, `TripticKummerRootClassification`,
`TripticSourceClassGroup` (`M/M_DA ≅ ℤ[ℂ/H₃]`), `TelescopeIdeal`, `SimultaneousDivisorLifting`.

## Landed modules (all wired, `lake build` green, axiom-clean)

1. `HTGeometry/AllDepthMixedConstraintClass.lean` — function level.
   `shiftDiffFun`, `diffCube τ s F z = ∑_(E⊆s) (−1)^(|s|−|E|) F (z + ∑_(i∈E) τ i)`,
   `diffCube_empty/_insert/_singleton/_pair/_union/_shiftDiffFun_comm`,
   `MixedConstGermSet`, `mixedConstGermSet_pair_iff` (depth two = corpus `MixedConstGerm`).
2. `HTGeometry/AllDepthMeroClass.lean` — the class inside `meroField ℂ`.
   `exists_realizesMero`, `diffCubeMero(_empty/_insert/_union)`, `AllDepthMeroSource`,
   `pairFaceWitnessMero`, `differentialAlgebraicOver_diffCubeMero`,
   `differentialAlgebraicOver_pairFaceWitnessMero`, `realizesMero_translate`,
   `realizesMero_congr`, `periodicOneGerm_of_realizesMero`, `realizesMero_diffCubeMero`.
3. `HTGeometry/AllDepthPairFaceSignature.lean` — **the forward half**.
   `realizesMero_const`, `diffCubeMero_translate_comm`, `pairFaceWitnessFun`,
   transports (`meromorphicOn_`, `periodicOneGerm_`, `mixedConstGerm_pairFaceWitnessFun`),
   `indepPeriods_of_periodsIntegrallyIndependent`, and
   **`pairFaceSignature_eq_zero_of_differentialAlgebraicOver`**.
4. `HTGeometry/AllDepthBottomCharge.lean` — the bottom charge.
   `bottomWitnessFun/Mero`, **`shiftDiffFun_pairFaceWitnessFun`**,
   **`additiveOrbitalDivisorAt_pairFaceWitnessFun`** (the signature *is* the `τ i`-orbit sum of
   the bottom charge), `periodicOneGerm_bottomWitnessFun`, `shiftConstGerm_bottomWitnessFun`,
   **`exists_mixedConstGermSet_erase_of_bottomCharge_eq_zero`** (kernel of the bottom charge =
   next class; uses `TripticEntireRigidity.const_of_entire_periodic_of_shift_const`),
   `laurentCoeff_bottomWitnessFun_add_one/_add_tau`,
   **`exists_finset_bottomCharge_pole_classes`** (finite support on `ℂ/Λ_k`).

## What remains (the descent)

Fix `k`.  `V = ∏_(m≠k) Δ_(τ m) F` is `Λ_k`-quasi-elliptic; `ρ_k(F)(p,ℓ) = laurentCoeff V p ℓ` is
`Λ_k`-invariant and finitely supported.  The pair-face hypothesis says every `τ i`-orbit sum
(`i ≠ k`) of `ρ_k(F)` vanishes.

(T) **Multi-telescoping.**  A finite-support divisor on `ℂ/Λ_k` whose `τ i`-orbit sums vanish for
    every `i ≠ k` equals `(∏_(i≠k)(t_i − 1))·C`.  Per free `ℤ^{d−1}`-orbit this is
    `⋂_i (u_i − 1) = (∏_i (u_i − 1))` in `ℂ[u^{±1}]` — owned as
    `TelescopeIdeal.iInf_span_singleton_eq_span_prod_of_primes`; the orbit gluing is
    `SimultaneousDivisorLifting`.
(R) **Theta realization.**  `Z = C·λ_k` with `λ_k` the theta logarithmic derivative for
    `Λ_k = ℤ + ℤτ k` (`thetaLogDerivMero`, principal part `[0]` — `EllipticThetaLogPrincipalPart`,
    `JetAtomDifferentiallyAlgebraic` says jets of line atoms are DA).  Then
    `ρ_k(Z) = (∏_(i≠k) x_i) C = ρ_k(F)`, and `Z` is DA.
(D) `E = F − Z ∈ ker ρ_k = Q_(d−1)`; `PairFace_(d−1)(E) = 0` by translation equivariance of `R_2`
    plus "a finite-support divisor invariant under an infinite-order translation is zero";
    induct on `|ι|`.  Base `|ι| = 2` is the depth-two theorem.
(I) Then the realization half of `Q_d/(Q_d ∩ Mer_DA) ≅ Comp_d` for card 2's exact-image theorem.

Useful corpus lemmas already located: `laurentCoeff_comp_add`, `laurentCoeff_congr`,
`laurentCoeff_add_const`, `laurentCoeff_shiftDiff`, `meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero`,
`pole_invariant_of_laurentCoeff_invariant`, `exists_finset_pole_classes`,
`meromorphicNFOn_toMeromorphicNFOn`, `analyticAt_of_nonneg_meromorphicOrderAt`,
`meromorphicOrderAt_nonneg_of_laurentCoeff_neg_eq_zero`,
`eventuallyEq_nhds_of_nhdsNE_of_continuousAt`, `tendsto_nhdsNE_add_const`,
`analyticAt_comp_add_const`, `linearIndependent_one_of_im_pos`,
`differentialAlgebraicOver_ratFunc_of_complex`, `differentiallyAlgebraic_of_realizesMero`.
