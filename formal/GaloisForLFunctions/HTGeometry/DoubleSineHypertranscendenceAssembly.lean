import GaloisForLFunctions.HTGeometry.DoubleSineIncrementBaseForm
import GaloisForLFunctions.HTGeometry.DoubleSineImaginaryRaySource
import GaloisForLFunctions.HTGeometry.DoubleSineCylinderHypertranscendence
import GaloisForLFunctions.HTGeometry.EllipticGammaFlatNonvanishing

/-!
# The double-sine source is hypertranscendental over the two-cylinder field

All the inputs of the arbitrary-family differential Ostrowski criterion are available for the
constructed multiple-sine source of a two-period frame:

* its two structural translation defects are exactly the cotangents of the other period, up to one
  constant;
* each cotangent lies in one cylinder of the two-cylinder function field;
* the translations act on that field by dilating the outer coordinate and by scaling the
  coefficient field;
* that field is a differential subfield of the meromorphic field, and the jets of a
  constant-coefficient element are the one-variable cylinder jets;
* the common fixed field of the two translations is `ℂ`.

Feeding them to the criterion gives hypertranscendence of the source over `ℂ(u₁)(u₂)`.
-/

open Filter Set Topology Complex Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance dsaDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance dsaComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance dsaMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- An embedded constant rational function is an embedded complex constant. -/
theorem ratMero_C (c : ℂ) :
    ratMero (RatFunc.C c) = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c := by
  rw [← RatFunc.algebraMap_C, ratfuncToMero_algebraMap_polynomial]
  show (polyToMero (Set.univ : Set ℂ)) (Polynomial.C c) = _
  rw [polyToMero, RingHom.comp_apply, polyToAnalytic_C]
  rfl

variable {l : Fin 2 → ℂ}

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Hypertranscendence of a source with exact cotangent defects.**  A meromorphic source whose two
structural translation defects are the cotangents of the other period, up to a constant, is
hypertranscendental over the two-cylinder function field. -/
theorem hypertranscendentalOver_twoCylinder_of_exact_defects (hl : LinearIndependent ℚ l)
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
    letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
    letI : Differential (RatFunc (RatFunc ℂ)) :=
      twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
    letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      (twoCylinderEmbed hl).toAlgebra
    HypertranscendentalOver (RatFunc (RatFunc ℂ)) M := by
  classical
  letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
  letI : Differential (RatFunc (RatFunc ℂ)) :=
    twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
  letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    (twoCylinderEmbed hl).toAlgebra
  have halg : ∀ y : RatFunc (RatFunc ℂ),
      algebraMap (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) y
        = twoCylinderEmbed hl y := fun _ => rfl
  letI : IsScalarTower ℂ (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) := by
    refine IsScalarTower.of_algebraMap_eq (R := ℂ) (S := RatFunc (RatFunc ℂ))
      (A := meroField (Set.univ : Set ℂ)) fun c => ?_
    rw [halg]
    have hc : algebraMap ℂ (RatFunc (RatFunc ℂ)) c
        = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (algebraMap ℂ (RatFunc ℂ) c) :=
      IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (RatFunc (RatFunc ℂ)) c
    rw [hc, twoCylinderEmbed_coeff]
    exact ((cylinderEmbed hl 0).commutes c).symm
  letI : DifferentialAlgebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) := by
    refine ⟨fun y => ?_⟩
    rw [halg, halg]
    exact meroFieldDeriv_twoCylinderEmbed hl y
  -- the two automorphisms of the base
  set q0 : ℂ := Complex.exp (l 1 * ω 0) with hq0def
  have hq0 : q0 ≠ 0 := Complex.exp_ne_zero _
  have hq0R : algebraMap ℂ (RatFunc ℂ) q0 ≠ 0 := by simpa using hq0
  set q1 : ℂ := Complex.exp (l 0 * ω 1) with hq1def
  have hq1 : q1 ≠ 0 := Complex.exp_ne_zero _
  set tau : Fin 2 → RatFunc (RatFunc ℂ) ≃+* RatFunc (RatFunc ℂ) :=
    ![ratFuncScaleEquiv (algebraMap ℂ (RatFunc ℂ) q0) hq0R, cylinderCoeffScaleEquiv hq1]
    with htaudef
  set sigma : Fin 2 → meroField (Set.univ : Set ℂ) ≃+* meroField (Set.univ : Set ℂ) :=
    fun i => addTranslationMeroEquiv (ω i) with hsigmadef
  -- the two increments, inside the base field
  set c0 : ℂ := -((Real.pi : ℂ) / ω 1 * Complex.I) with hc0def
  set b0 : RatFunc (RatFunc ℂ) := coeffExtend (K := RatFunc ℂ) (cotModel c0) with hb0def
  set b1 : RatFunc (RatFunc ℂ) :=
    -algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (cotModel ((Real.pi : ℂ) / ω 0 * Complex.I))
      + algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (algebraMap ℂ (RatFunc ℂ) cst) with hb1def
  have hb0mero : twoCylinderEmbed hl b0 = -periodCotMero (ω 1) := by
    have hcot : cotModel c0 = -cotModel ((Real.pi : ℂ) / ω 1 * Complex.I) := by
      rw [hc0def, show -((Real.pi : ℂ) / ω 1 * Complex.I)
          = (-1 : ℂ) * ((Real.pi : ℂ) / ω 1 * Complex.I) by ring, cotModel_mul_left]
      simp
    rw [hb0def, hcot, (coeffExtend (C := ℂ) (K := RatFunc ℂ)).map_neg,
      (twoCylinderEmbed hl).map_neg,
      ← periodCotMero_eq_twoCylinderEmbed_coeffExtend hl hω1 hl1]
  have hb1mero : twoCylinderEmbed hl b1
      = -periodCotMero (ω 0) + algebraMap ℂ (meroField (Set.univ : Set ℂ)) cst := by
    rw [hb1def, (twoCylinderEmbed hl).map_add, (twoCylinderEmbed hl).map_neg,
      ← periodCotMero_eq_twoCylinderEmbed_coeff hl hω0 hl0, twoCylinderEmbed_coeff]
    congr 1
    exact (cylinderEmbed hl 0).commutes cst
  -- the criterion
  have hlam : l 1 ≠ 0 := by
    rw [hl1]
    refine div_ne_zero ?_ hω1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hc0 : c0 ≠ 0 := by
    rw [hc0def, neg_ne_zero]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (div_ne_zero hpi hω1) Complex.I_ne_zero
  have hCzero : ∀ c : ℂ, (algebraMap ℂ (RatFunc ℂ) c)′ = 0 := by
    intro c
    rw [cylinderDifferential_deriv (l 0), cylDeriv_algebraMap]
  refine hypertranscendentalOver_of_cotangentCylinderIncrement tau sigma ?_ ?_ ?_ ?_ M
    ![b0, b1] ?_ 0 q0 (l 1) c0 hq0 htor hlam hc0 ?_ ?_
  · intro i k
    fin_cases i
    · show addTranslationMeroEquiv (ω 0) (twoCylinderEmbed hl k)
        = twoCylinderEmbed hl (ratFuncScaleEquiv (algebraMap ℂ (RatFunc ℂ) q0) hq0R k)
      exact addTranslationMeroEquiv_twoCylinderEmbed hl (ω 0) hper0 k
    · show addTranslationMeroEquiv (ω 1) (twoCylinderEmbed hl k)
        = twoCylinderEmbed hl (cylinderCoeffScaleEquiv hq1 k)
      exact addTranslationMeroEquiv_twoCylinderEmbed_coeff hl (ω 1) hper1 k
  · intro i y
    exact addTranslationMeroEquiv_deriv (ω i) y
  · intro i z
    exact addTranslationMeroEquiv_algebraMap_complex_self (ω i) z
  · intro z hz
    exact hfix z (hz 0) (hz 1)
  · intro i
    fin_cases i
    · show addTranslationMeroEquiv (ω 0) M = M + twoCylinderEmbed hl b0
      rw [hb0mero]
      linear_combination h0
    · show addTranslationMeroEquiv (ω 1) M = M + twoCylinderEmbed hl b1
      rw [hb1mero]
      rw [ratMero_C] at h1
      linear_combination h1
  · intro k
    rfl
  · intro n
    have hjet := differentialJet_twoCylinder (C := ℂ) (K := RatFunc ℂ) hCzero (l 1) n
      (cotModel c0)
    show differentialJet n b0
      = (cylDeriv (algebraMap ℂ (RatFunc ℂ) (l 1)))^[n]
        (cotModel (algebraMap ℂ (RatFunc ℂ) c0))
    rw [hb0def]
    rw [hjet, coeffExtend_cotModel]

/-! ### The imaginary-ray specialization -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The double-sine source is hypertranscendental.**  For periods `i a`, `i b` with `a, b > 0` and
`a/b` irrational, the constructed multiple-sine source of the two-period frame is
hypertranscendental over the two-cylinder function field `ℂ(u₁)(u₂)`. -/
theorem hypertranscendental_doubleSine_imaginaryRay {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hirr : Irrational (a / b)) :
    letI : Differential (RatFunc ℂ) :=
      cylinderDifferential (2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (a : ℂ)))
    letI : Differential (RatFunc (RatFunc ℂ)) :=
      twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ)
        (2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (b : ℂ))))
    letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      (twoCylinderEmbed (linearIndependent_cylinderFrequencies_imaginaryRay ha hb hirr)).toAlgebra
    ∃ M : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (Complex.I * (a : ℂ)) M - M
          = -periodCotMero (Complex.I * (b : ℂ)) ∧
        HypertranscendentalOver (RatFunc (RatFunc ℂ)) M := by
  classical
  set ω : Fin 2 → ℂ := ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] with hωdef
  have hω0 : ω 0 = Complex.I * (a : ℂ) := by simp [hωdef]
  have hω1 : ω 1 = Complex.I * (b : ℂ) := by simp [hωdef]
  have haC : ((a : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt ha
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hb
  have hω0ne : ω 0 ≠ 0 := by
    rw [hω0]
    exact mul_ne_zero Complex.I_ne_zero haC
  have hω1ne : ω 1 ≠ 0 := by
    rw [hω1]
    exact mul_ne_zero Complex.I_ne_zero hbC
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  set l : Fin 2 → ℂ :=
    ![2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (a : ℂ)),
      2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (b : ℂ))] with hldef
  have hl : LinearIndependent ℚ l :=
    linearIndependent_cylinderFrequencies_imaginaryRay ha hb hirr
  have hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0 := by
    rw [hldef, hω0]
    simp
  have hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1 := by
    rw [hldef, hω1]
    simp
  have hper0 : Complex.exp (l 0 * ω 0) = 1 := by
    rw [hl0, div_mul_cancel₀ _ hω0ne]
    simp
  have hper1 : Complex.exp (l 1 * ω 1) = 1 := by
    rw [hl1, div_mul_cancel₀ _ hω1ne]
    simp
  have hprod : l 1 * ω 0 = 2 * (Real.pi : ℂ) * Complex.I * ((a / b : ℝ) : ℂ) := by
    rw [hl1, hω1, hω0]
    push_cast
    field_simp
  have htor : ∀ n : ℤ, n ≠ 0 → Complex.exp (l 1 * ω 0) ^ n ≠ 1 := by
    intro n hn
    rw [hprod]
    exact exp_two_pi_I_zpow_ne_one hirr hn
  have hfix : ∀ z : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (ω 0) z = z → addTranslationMeroEquiv (ω 1) z = z →
        ∃ w : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) w = z := by
    intro z h1 h2
    rw [hω0] at h1
    rw [hω1] at h2
    exact exists_constant_of_two_imaginaryPeriods_fixed hirr h1 h2
  obtain ⟨M, cst, hM0, hM1⟩ := exists_doubleSine_source_imaginaryRay ha hb
  refine ⟨M, hM0, ?_⟩
  have hkey := hypertranscendentalOver_twoCylinder_of_exact_defects hl ω hω0ne hω1ne hl0 hl1
    hper0 hper1 htor hfix M cst (by rw [hω0, hω1]; exact hM0) (by rw [hω0, hω1]; exact hM1)
  exact hkey

end

end GaloisForLFunctions.HTGeometry
