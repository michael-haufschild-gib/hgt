import GaloisForLFunctions.HTGeometry.MvPolynomialHomogeneousDehomogenization
import GaloisForLFunctions.HTGeometry.SimplePoleJetScaleSeparatedHorizon

/-!
# The boundary grading of the scale-separated simple-pole profile

The pole variable and moving scale have boundary weight zero, while every regular-unit jet has
weight one.  This module flattens those coordinates into one multivariate polynomial ring and
proves that every pole-grade coefficient of a degree-`d` source remains boundary-homogeneous of
degree `d`.

This is the coefficient interface needed to specialize the universal Rees profile at a unit with
fixed value `U₀ = 1`: homogeneous chart faithfulness can then be applied coefficient by
coefficient, rather than assumed as an external noncancellation hypothesis.
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Flattened weight: pole and scale have weight zero; regular boundary jets have weight one. -/
def scaleSeparatedFlattenWeight : Option (Option ℕ) → ℕ
  | none => 0
  | some o => simplePoleBoundaryWeight o

/-- Embed the universal flattened coordinates `(T,U₀,U₁,...)` into
`(T,S,U₀,U₁,...)`, omitting the new scale coordinate. -/
def universalToScaleSeparatedFlatten : Option ℕ → Option (Option ℕ)
  | none => none
  | some k => some (some k)

/-- The scale-separated jet profile in the single flattened polynomial ring. -/
def scaleSeparatedSimplePoleJetProfileMV (n : ℕ) (j : Fin (n + 1)) :
    MvPolynomial (Option (Option ℕ)) ℂ :=
  (MvPolynomial.optionEquivLeft ℂ (Option ℕ)).symm
    (scaleSeparatedSimplePoleJetProfile n j)

theorem optionEquivLeft_rename_universalToScaleSeparatedFlatten
    (p : MvPolynomial (Option ℕ) ℂ) :
    MvPolynomial.optionEquivLeft ℂ (Option ℕ)
        (MvPolynomial.rename universalToScaleSeparatedFlatten p) =
      (MvPolynomial.optionEquivLeft ℂ ℕ p).map simplePoleBoundaryInclude := by
  let lhs : MvPolynomial (Option ℕ) ℂ →+*
      Polynomial ScaleSeparatedPoleBoundaryRing :=
    (MvPolynomial.optionEquivLeft ℂ (Option ℕ)).toRingHom.comp
      (MvPolynomial.rename universalToScaleSeparatedFlatten).toRingHom
  let rhs : MvPolynomial (Option ℕ) ℂ →+*
      Polynomial ScaleSeparatedPoleBoundaryRing :=
    (Polynomial.mapRingHom simplePoleBoundaryInclude).comp
      (MvPolynomial.optionEquivLeft ℂ ℕ).toRingHom
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs, simplePoleBoundaryInclude]
    · intro o
      rcases o with (_ | k)
      · simp [lhs, rhs, universalToScaleSeparatedFlatten,
          simplePoleBoundaryInclude]
      · simp [lhs, rhs, universalToScaleSeparatedFlatten,
          simplePoleBoundaryInclude]
  exact RingHom.congr_fun h p

theorem scaleSeparatedSimplePoleJetProfileMV_eq (n : ℕ) (j : Fin (n + 1)) :
    scaleSeparatedSimplePoleJetProfileMV n j =
      MvPolynomial.X (some none) ^ (n - (j : ℕ)) *
        MvPolynomial.rename universalToScaleSeparatedFlatten
          (universalSimplePoleJetProfileMV (j : ℕ)) := by
  apply (MvPolynomial.optionEquivLeft ℂ (Option ℕ)).injective
  rw [scaleSeparatedSimplePoleJetProfileMV, AlgEquiv.apply_symm_apply,
    map_mul, map_pow, MvPolynomial.optionEquivLeft_X_some,
    optionEquivLeft_rename_universalToScaleSeparatedFlatten,
    optionEquivLeft_universalSimplePoleJetProfileMV]
  simp [scaleSeparatedSimplePoleJetProfile]

theorem scaleSeparatedSimplePoleJetProfileMV_isWeightedHomogeneous
    (n : ℕ) (j : Fin (n + 1)) :
    MvPolynomial.IsWeightedHomogeneous scaleSeparatedFlattenWeight
      (scaleSeparatedSimplePoleJetProfileMV n j) 1 := by
  rw [scaleSeparatedSimplePoleJetProfileMV_eq]
  have hS :=
    (MvPolynomial.isWeightedHomogeneous_X ℂ scaleSeparatedFlattenWeight (some none)).pow
      (n - (j : ℕ))
  have hU := GaloisForLFunctions.rename_isWeightedHomogeneous
    (wτ := scaleSeparatedFlattenWeight)
    (universalSimplePoleJetProfileMV_isWeightedHomogeneous (j : ℕ))
    universalToScaleSeparatedFlatten (by
      intro o
      rcases o with (_ | k) <;> rfl)
  simpa [scaleSeparatedFlattenWeight] using! hS.mul hU

/-- The complete finite scale-separated profile in the flattened coordinate ring. -/
def finiteScaleSeparatedSimplePoleProfileEvalMV (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Option (Option ℕ)) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (scaleSeparatedSimplePoleJetProfileMV n)

theorem finiteScaleSeparatedSimplePoleProfileEvalMV_isWeightedHomogeneous
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d) :
    MvPolynomial.IsWeightedHomogeneous scaleSeparatedFlattenWeight
      (finiteScaleSeparatedSimplePoleProfileEvalMV n P) d := by
  simpa using! isWeightedHomogeneous_eval₂_of_isHomogeneous_mul hP
    scaleSeparatedFlattenWeight (scaleSeparatedSimplePoleJetProfileMV n)
    (scaleSeparatedSimplePoleJetProfileMV_isWeightedHomogeneous n)

theorem optionEquivLeft_finiteScaleSeparatedSimplePoleProfileEvalMV
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.optionEquivLeft ℂ (Option ℕ)
        (finiteScaleSeparatedSimplePoleProfileEvalMV n P) =
      finiteScaleSeparatedSimplePoleProfileEval n P := by
  let lhs : MvPolynomial (Fin (n + 1)) ℂ →+*
      Polynomial ScaleSeparatedPoleBoundaryRing :=
    (MvPolynomial.optionEquivLeft ℂ (Option ℕ)).toRingHom.comp
      (finiteScaleSeparatedSimplePoleProfileEvalMV n)
  have h : lhs = finiteScaleSeparatedSimplePoleProfileEval n := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, finiteScaleSeparatedSimplePoleProfileEvalMV,
        finiteScaleSeparatedSimplePoleProfileEval]
    · intro j
      simp [lhs, finiteScaleSeparatedSimplePoleProfileEvalMV,
        finiteScaleSeparatedSimplePoleProfileEval,
        scaleSeparatedSimplePoleJetProfileMV]
  exact RingHom.congr_fun h P

/-- **Scale-separated coefficient grading.**  Every pole-grade coefficient of a homogeneous
degree-`d` source retains boundary degree exactly `d`; the pole and moving scale carry weight
zero. -/
theorem finiteScaleSeparatedSimplePoleProfileEval_coeff_isWeightedHomogeneous
    {n d : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.IsHomogeneous d)
    (q : ℕ) :
    MvPolynomial.IsWeightedHomogeneous simplePoleBoundaryWeight
      ((finiteScaleSeparatedSimplePoleProfileEval n P).coeff q) d := by
  have h := GaloisForLFunctions.optionEquivLeft_coeff_isWeightedHomogeneous
    scaleSeparatedFlattenWeight
    (finiteScaleSeparatedSimplePoleProfileEvalMV_isWeightedHomogeneous hP) q
  rw [optionEquivLeft_finiteScaleSeparatedSimplePoleProfileEvalMV] at h
  simpa [scaleSeparatedFlattenWeight] using h

end

end GaloisForLFunctions.HTGeometry
