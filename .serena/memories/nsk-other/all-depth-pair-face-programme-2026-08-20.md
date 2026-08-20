# All-depth pair-face signature theorem — Lean programme (opened 2026-08-20)

Closes the remaining mathematics of **two** stage-2 cards:
`all-depth-pair-face-signature-completeness` and (via its module isomorphism `(5)`) formula `(1)`
of `all-depth-compatible-pair-face-differential-matroid`.

## The depth-two base is already in the tree (checked 2026-08-20, axiom-clean)

```text
HTGeometry.differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero   (TripticCompleteness)
    F meromorphic on ℂ, PeriodicOneGerm F, MixedConstGerm F τ σ Cst, im τ, im σ > 0,
    IndepPeriods τ σ, the two ℝ-independence clauses, ℚ-independence of the source periods
      ⇒  ( DifferentiallyAlgebraic (toMeromorphicNFOn F ℂ)
             ↔ ∀ p, ∀ ℓ < 0, additiveOrbitalDivisorAt F σ p ℓ = 0 )
additiveOrbitalDivisorAt F σ p ℓ = ∑ᶠ m : ℤ, laurentCoeff (Δ_σ F) (p + m σ) ℓ
```
Halves: `additiveOrbitalDivisorAt_eq_zero_of_differentiallyAlgebraic`,
`differentiallyAlgebraic_toMeromorphicNFOn_of_vanishing_orbital_divisor`.
Multiplicative counterparts + depth-two class group with `M/M_DA ≅ ℤ[ℂ/H₃]`:
`TripticMultiplicativeKernelConverse`, `TripticKummerRootClassification`,
`TripticSourceClassGroup`.  Algebraic lemmas owned: `TelescopeIdeal`,
`SimultaneousDivisorLifting`.

## Built so far (both wired, built, axiom-clean)

`HTGeometry/AllDepthMixedConstraintClass.lean` — function level:
```text
shiftDiffFun h F,  diffCube τ s F z = ∑_(E ⊆ s) (−1)^(|s|−|E|) F (z + ∑_(i∈E) τ i)
diffCube_empty / _insert / _singleton / _pair
MixedConstGermSet τ s F Cst,  mixedConstGermSet_pair_iff  (= corpus MixedConstGerm at a pair)
MixedConstGermSet.shiftDiff
```

`HTGeometry/AllDepthMeroClass.lean` — germ-field level (the working setting):
```text
exists_realizesMero               every x : meroField ℂ is realized by a function
                                  (meroField = Frac(analyticSubring), IsFractionRing.div_surjective)
diffCubeMero τ s x,  diffCubeMero_empty / _insert
AllDepthMeroSource τ x Cst        the class Q_d on germs
pairFaceWitnessMero τ i j x       W_ij = diffCubeMero over univ \ {i,j}
differentialAlgebraicOver_diffCubeMero
differentialAlgebraicOver_pairFaceWitnessMero        **the forward half's algebra**
```
Reused: `OrderTwoStructuralTranslateDecomposition.differentialAlgebraicOver_addTranslationMeroEquiv`
and `..._finset_sum`.

## Why the germ field

Function-level `DifferentiallyAlgebraic` (pointwise ∀ z) is only known closed under sums for
*entire* functions; for meromorphic ones the corpus routes through `RealizesMero` /
`daOverRatFuncField`.  Inside `meroField ℂ` sums, translates and DA are field algebra, and every
element has a realization, so the depth-two interface is available through
`differentiallyAlgebraic_of_realizesMero` / `differentialAlgebraicOver_of_realizesMero`.

## Next bricks

1. Germ→function transport of the class: from `AllDepthMeroSource τ x Cst` and a realization `f`,
   derive `MeromorphicOn f ℂ`, `PeriodicOneGerm f`, and `MixedConstGerm (W_ij realization) (τ i) (τ j) Cst`.
2. `pairFaceSignature τ x i j p ℓ := additiveOrbitalDivisorAt (realization of W_ij x) (τ j) p ℓ`,
   with independence of the realization (two realizations agree off a discrete set).
3. Forward half of the main theorem: `x` DA ⇒ every signature vanishes (uses 1, 2, depth two).
4. Bottom charge `ρ_d`, `ker ρ_d = Q_(d−1)`, `S_(i,d) = q_i ∘ ρ_d`, multi-telescoping over the
   group algebra, theta realization `Z = C·λ_d`, translation equivariance of `R_2`, the induction.
5. Realization half of `Q_d/(Q_d ∩ Mer_DA) ≅ Comp_d`.
