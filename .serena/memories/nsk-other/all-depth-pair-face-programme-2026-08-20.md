# All-depth pair-face signature theorem — Lean programme (2026-08-20)

Closes the remaining mathematics of `all-depth-pair-face-signature-completeness` and (via its
module isomorphism `(5)`) formula `(1)` of `all-depth-compatible-pair-face-differential-matroid`.

## Depth-two base — already in the tree, axiom-clean

```text
HTGeometry.differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero   (TripticCompleteness)
additiveOrbitalDivisorAt F σ p ℓ = ∑ᶠ m : ℤ, laurentCoeff (Δ_σ F) (p + m σ) ℓ
```
Also `TripticEntireRigidity.const_of_entire_periodic_of_shift_const`, `TelescopeIdeal`,
`SimultaneousDivisorLifting`, `TripticSourceClassGroup` (depth-two class group `M/M_DA ≅ ℤ[ℂ/H₃]`),
`TripticNormalForm`/`TripticKernelIdentification`/`JetAtomDifferentiallyAlgebraic` (atom sums).

## Landed (all wired, `lake build` green, axiom-clean)

1. `AllDepthMixedConstraintClass` — `shiftDiffFun`, `diffCube τ s F`, `_empty/_insert/_singleton/
   _pair/_union/_shiftDiffFun_comm`, `MixedConstGermSet`, `mixedConstGermSet_pair_iff`.
2. `AllDepthMeroClass` — the class in `meroField ℂ`; `exists_realizesMero`, `diffCubeMero(_insert/
   _union)`, `AllDepthMeroSource`, `pairFaceWitnessMero`,
   `differentialAlgebraicOver_diffCubeMero/_pairFaceWitnessMero`, `realizesMero_translate`,
   `realizesMero_congr`, `periodicOneGerm_of_realizesMero`, `realizesMero_diffCubeMero`.
3. `AllDepthPairFaceSignature` — `realizesMero_const`, `diffCubeMero_translate_comm`,
   `pairFaceWitnessFun` + transports, `indepPeriods_of_periodsIntegrallyIndependent`, and
   **`pairFaceSignature_eq_zero_of_differentialAlgebraicOver`** (the forward half).
4. `AllDepthBottomCharge` — `bottomWitnessFun/Mero`, `shiftDiffFun_pairFaceWitnessFun`,
   **`additiveOrbitalDivisorAt_pairFaceWitnessFun`** (signature = `τ i`-orbit sum of the bottom
   charge), `periodicOneGerm_bottomWitnessFun`, `shiftConstGerm_bottomWitnessFun`,
   **`exists_mixedConstGermSet_erase_of_bottomCharge_eq_zero`** (kernel of the charge = `Q_(d−1)`),
   `laurentCoeff_bottomWitnessFun_add_one/_add_tau`,
   **`exists_finset_bottomCharge_pole_classes`**.
5. `AllDepthTelescope` — `telescopeCube w s C p = ∑_(E ⊆ s) (−1)^(|s|−|E|) C (p − ∑_(i∈E) w i)`,
   `telescopeCube_empty/_insert`, `lineTail w D p = ∑ᶠ_(m ≥ 1) D (p + m•w)`, `lineTail_sub`
   (`lineTail(p−w) − lineTail p = D p`), `exists_finset_support_lineTail`,
   `finsum_lineTail_eq_zero` (transverse line sums are inherited), and
   **`exists_telescopeCube`** — the multi-directional telescoping theorem.

## Remaining

(R) **Theta realization.**  Build `Z` differentially algebraic with `ρ_k(Z) = ρ_k(F)`.  Since
    `ρ_k(F) = telescopeCube (images of τ_i, i ≠ k) C` for a finitely supported `C`
    (by `exists_telescopeCube`, applied on `A = ℂ ⧸ Λ_k` with `Λ_k = ℤ + ℤ τ k`), take
    `Z = C · λ_k` where `λ_k` is the theta logarithmic derivative for `Λ_k` — the corpus's *line
    atom*, whose jets are all DA (`JetAtomDifferentiallyAlgebraic`) and whose principal part is the
    single class `[0]`.  Needs: `R_1` equivariance, `R_1(λ_k) = [0]`, and the atom-sum realization
    (`TripticKernelNormalForm.exists_totalAtomSum_no_principal_part`,
    `TripticKernelIdentification.exists_const_sub_totalAtomSum_of_vanishing_divisor` are the
    depth-two analogues to mirror).
(D) **Descent.**  `E = F − Z ∈ ker ρ_k = Q_(d−1)` (already Lean), `PairFace_(d−1)(E) = 0` by
    translation equivariance of `R_2` plus "a finite-support divisor invariant under an
    infinite-order translation is zero", then induct on `|ι|`; base `|ι| = 2` is depth two.
(I) The realization half of `Q_d/(Q_d ∩ Mer_DA) ≅ Comp_d` for card 2's exact-image theorem.

## Useful corpus lemmas located

`laurentCoeff_comp_add`, `laurentCoeff_congr`, `laurentCoeff_add_const`, `laurentCoeff_shiftDiff`,
`meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero`,
`pole_invariant_of_laurentCoeff_invariant`, `exists_finset_pole_classes`,
`meromorphicNFOn_toMeromorphicNFOn`, `analyticAt_of_nonneg_meromorphicOrderAt`,
`meromorphicOrderAt_nonneg_of_laurentCoeff_neg_eq_zero`,
`eventuallyEq_nhds_of_nhdsNE_of_continuousAt`, `tendsto_nhdsNE_add_const`,
`analyticAt_comp_add_const`, `linearIndependent_one_of_im_pos`,
`differentialAlgebraicOver_ratFunc_of_complex`, `differentiallyAlgebraic_of_realizesMero`,
`finsum_curry`, `finsum_comp_equiv`, `finsum_sub_distrib`, `finsum_add_distrib`.
