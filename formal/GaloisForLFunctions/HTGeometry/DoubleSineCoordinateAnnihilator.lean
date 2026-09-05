import GaloisForLFunctions.HTGeometry.CoordinateFieldInTwoCylinderAdjoin
import GaloisForLFunctions.HTGeometry.DoubleSineHypertranscendenceAssembly
import GaloisForLFunctions.HTGeometry.PeriodCotangentMeroDA

/-!
# The double-sine translation annihilator over the coordinate field

The hypertranscendence of the double-sine source is proved over the two-cylinder field
`ℂ(u₁)(u₂)`, but the annihilator statement is over the coordinate field `ℂ(z)`.  Neither field
contains the other; the bridge is that `z` satisfies `z'' = 0`, hence is differentially algebraic
over the two-cylinder field, and that `ℂ(z)` lies inside the differential field the two-cylinder
field generates by adjoining `z`.  Transitivity of differential algebraicity converts one
hypertranscendence statement into the other.

With that base change, and with each cotangent defect differentially algebraic over `ℂ(z)`, the
one-step annihilator theorem applies verbatim: the annihilator is the augmentation ideal, total
exponent is the complete invariant, and every single structural translate stays
hypertranscendental.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {l : Fin 2 → ℂ}

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Base change from the coordinate field to the two-cylinder field.**  Differential
algebraicity over `ℂ(z)` implies differential algebraicity over `ℂ(u₁)(u₂)`: the coordinate `z`
satisfies `z'' = 0`, so it is differentially algebraic over the two-cylinder field, and `ℂ(z)` lies
inside the differential field the two-cylinder field generates by adjoining `z`. -/
theorem differentialAlgebraicOver_twoCylinder_of_ratFunc (hl : LinearIndependent ℚ l)
    {Ψ : meroField (Set.univ : Set ℂ)} (h : DifferentialAlgebraicOver (RatFunc ℂ) Ψ) :
    letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
    letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      (twoCylinderEmbed hl).toAlgebra
    letI : Differential (RatFunc (RatFunc ℂ)) :=
      twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
    letI : DifferentialAlgebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      ⟨fun y => meroFieldDeriv_twoCylinderEmbed hl y⟩
    DifferentialAlgebraicOver (RatFunc (RatFunc ℂ)) Ψ := by
  letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
  letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    (twoCylinderEmbed hl).toAlgebra
  letI : Differential (RatFunc (RatFunc ℂ)) :=
    twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
  letI : DifferentialAlgebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    ⟨fun y => meroFieldDeriv_twoCylinderEmbed hl y⟩
  set B : IntermediateField (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    differentialAdjoin (RatFunc (RatFunc ℂ))
      ({coordinateMero} : Set (meroField (Set.univ : Set ℂ))) with hB
  letI : Algebra (RatFunc ℂ) B :=
    (RingHom.codRestrict (ratMero : RatFunc ℂ →+* meroField (Set.univ : Set ℂ)) B
      (fun r => ratMero_mem_differentialAdjoin_coordinate hl r)).toAlgebra
  haveI : IsScalarTower (RatFunc ℂ) B (meroField (Set.univ : Set ℂ)) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  have hy : DifferentialAlgebraicOver B Ψ := differentialAlgebraicOver_mono h
  exact differentialAlgebraicOver_trans (differentialAlgebraicOver_coordinateMero hl) hy

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The double-sine source is hypertranscendental over the coordinate field.**  Hypertranscendence
over the two-cylinder field transfers along the base change. -/
theorem not_differentialAlgebraicOver_doubleSine_source (hl : LinearIndependent ℚ l)
    (ω : Fin 2 → ℂ) (hω0 : ω 0 ≠ 0) (hω1 : ω 1 ≠ 0)
    (hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0)
    (hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1)
    (hper0 : Complex.exp (l 0 * ω 0) = 1)
    (hper1 : Complex.exp (l 1 * ω 1) = 1)
    (htor : ∀ n : ℤ, n ≠ 0 → Complex.exp (l 1 * ω 0) ^ n ≠ 1)
    (hfix : ∀ z : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (ω 0) z = z → addTranslationMeroEquiv (ω 1) z = z →
        ∃ w : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) w = z)
    (M : meroField (Set.univ : Set ℂ)) (cst : ℂ)
    (h0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1))
    (h1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst)) :
    ¬ DifferentialAlgebraicOver (RatFunc ℂ) M := by
  have hHT2 := hypertranscendentalOver_twoCylinder_of_exact_defects hl ω hω0 hω1 hl0 hl1
    hper0 hper1 htor hfix M cst h0 h1
  exact fun hda => hHT2 (differentialAlgebraicOver_twoCylinder_of_ratFunc hl hda)

/-- Each structural defect of the double-sine source is differentially algebraic over `ℂ(z)`. -/
theorem differentialAlgebraicOver_doubleSine_defect (ω : Fin 2 → ℂ)
    (M : meroField (Set.univ : Set ℂ)) (cst : ℂ)
    (h0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1))
    (h1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst)) :
    ∀ j : Fin 2, DifferentialAlgebraicOver (RatFunc ℂ)
      (addTranslationMeroEquiv (ω j) M - M) := by
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [h0]
    exact differentialAlgebraicOver_neg (differentialAlgebraicOver_periodCotMero (ω 1))
  · rw [h1]
    refine differentialAlgebraicOver_add
      (differentialAlgebraicOver_neg (differentialAlgebraicOver_periodCotMero (ω 0))) ?_
    rw [ratMero_ratFuncC]
    exact differentialAlgebraicOver_algebraMap_complex cst

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The augmentation-ideal annihilator of the double-sine source.**  For a two-period frame whose
cylinder frequencies are rationally independent and whose second dilation is non-torsion, a
meromorphic source with the exact cotangent defects has translation annihilator, modulo the
differentially algebraic sector over `ℂ(z)`, exactly the augmentation ideal. -/
theorem daTranslationAnnihilator_doubleSine_eq_augIdeal (hl : LinearIndependent ℚ l)
    (ω : Fin 2 → ℂ) (hω0 : ω 0 ≠ 0) (hω1 : ω 1 ≠ 0)
    (hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0)
    (hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1)
    (hper0 : Complex.exp (l 0 * ω 0) = 1)
    (hper1 : Complex.exp (l 1 * ω 1) = 1)
    (htor : ∀ n : ℤ, n ≠ 0 → Complex.exp (l 1 * ω 0) ^ n ≠ 1)
    (hfix : ∀ z : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (ω 0) z = z → addTranslationMeroEquiv (ω 1) z = z →
        ∃ w : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) w = z)
    (M : meroField (Set.univ : Set ℂ)) (cst : ℂ)
    (h0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1))
    (h1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst)) :
    {Q : MvPolynomial (Fin 2) ℂ |
        DifferentialAlgebraicOver (RatFunc ℂ) (transApply ω Q M)}
      = (augIdeal 2 : Set (MvPolynomial (Fin 2) ℂ)) :=
  daTranslationAnnihilator_eq_augIdeal ω M
    (differentialAlgebraicOver_doubleSine_defect ω M cst h0 h1)
    (not_differentialAlgebraicOver_doubleSine_source hl ω hω0 hω1 hl0 hl1 hper0 hper1 htor hfix M cst h0 h1)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Total exponent is the complete invariant for the double sine.**  A translation operator sends
the source into the differentially algebraic sector exactly when its coefficients sum to zero. -/
theorem differentialAlgebraicOver_transApply_doubleSine_iff (hl : LinearIndependent ℚ l)
    (ω : Fin 2 → ℂ) (hω0 : ω 0 ≠ 0) (hω1 : ω 1 ≠ 0)
    (hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0)
    (hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1)
    (hper0 : Complex.exp (l 0 * ω 0) = 1)
    (hper1 : Complex.exp (l 1 * ω 1) = 1)
    (htor : ∀ n : ℤ, n ≠ 0 → Complex.exp (l 1 * ω 0) ^ n ≠ 1)
    (hfix : ∀ z : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (ω 0) z = z → addTranslationMeroEquiv (ω 1) z = z →
        ∃ w : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) w = z)
    (M : meroField (Set.univ : Set ℂ)) (cst : ℂ)
    (h0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1))
    (h1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst))
    (Q : MvPolynomial (Fin 2) ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (transApply ω Q M)
      ↔ ∑ n ∈ Q.support, MvPolynomial.coeff n Q = 0 :=
  differentialAlgebraicOver_transApply_iff_sum_coeff_eq_zero ω M
    (differentialAlgebraicOver_doubleSine_defect ω M cst h0 h1)
    (not_differentialAlgebraicOver_doubleSine_source hl ω hω0 hω1 hl0 hl1 hper0 hper1 htor hfix M cst h0 h1) Q

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Every structural translate of the double-sine source is hypertranscendental.** -/
theorem not_differentialAlgebraicOver_transApply_doubleSine_monomial (hl : LinearIndependent ℚ l)
    (ω : Fin 2 → ℂ) (hω0 : ω 0 ≠ 0) (hω1 : ω 1 ≠ 0)
    (hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0)
    (hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1)
    (hper0 : Complex.exp (l 0 * ω 0) = 1)
    (hper1 : Complex.exp (l 1 * ω 1) = 1)
    (htor : ∀ n : ℤ, n ≠ 0 → Complex.exp (l 1 * ω 0) ^ n ≠ 1)
    (hfix : ∀ z : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (ω 0) z = z → addTranslationMeroEquiv (ω 1) z = z →
        ∃ w : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) w = z)
    (M : meroField (Set.univ : Set ℂ)) (cst : ℂ)
    (h0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1))
    (h1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst))
    (n : Fin 2 →₀ ℕ) {c : ℂ} (hc : c ≠ 0) :
    ¬ DifferentialAlgebraicOver (RatFunc ℂ)
      (transApply ω (MvPolynomial.monomial n c) M) :=
  not_differentialAlgebraicOver_transApply_monomial ω M
    (differentialAlgebraicOver_doubleSine_defect ω M cst h0 h1)
    (not_differentialAlgebraicOver_doubleSine_source hl ω hω0 hω1 hl0 hl1 hper0 hper1 htor hfix M cst h0 h1) n hc

end

end GaloisForLFunctions.HTGeometry
