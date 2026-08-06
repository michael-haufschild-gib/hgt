import GaloisForLFunctions.HTGeometry.DoubleSineSameClassDependence

/-!
# The coset criterion for the double-sine orbit

The two halves assembled: a family of translates of a source with exact cotangent defects is
differentially independent over the two-cylinder field **exactly when** the shifts lie in pairwise
distinct classes modulo the period lattice.

Independence for distinct classes is the orbit criterion; dependence for a repeated class is the
base-field difference of two translates whose shifts differ by a lattice element.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance docDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance docComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance docMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

variable {l : Fin 2 → ℂ}

/-! ### The two structural defects are base-field defects -/

theorem baseDefectShift_period_zero (hl : LinearIndependent ℚ l) {ω : Fin 2 → ℂ}
    (hω1 : ω 1 ≠ 0) (hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1)
    (M : meroField (Set.univ : Set ℂ))
    (hd0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1)) :
    BaseDefectShift hl M (ω 0) := by
  refine ⟨-coeffExtend (K := RatFunc ℂ) (cotModel ((Real.pi : ℂ) / ω 1 * Complex.I)), ?_⟩
  rw [(twoCylinderEmbed hl).map_neg,
    ← periodCotMero_eq_twoCylinderEmbed_coeffExtend hl hω1 hl1]
  exact hd0

theorem baseDefectShift_period_one (hl : LinearIndependent ℚ l) {ω : Fin 2 → ℂ}
    (hω0 : ω 0 ≠ 0) (hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0)
    (M : meroField (Set.univ : Set ℂ)) (cst : ℂ)
    (hd1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst)) :
    BaseDefectShift hl M (ω 1) := by
  refine ⟨-algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ))
      (cotModel ((Real.pi : ℂ) / ω 0 * Complex.I))
    + algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (algebraMap ℂ (RatFunc ℂ) cst), ?_⟩
  rw [(twoCylinderEmbed hl).map_add, (twoCylinderEmbed hl).map_neg,
    ← periodCotMero_eq_twoCylinderEmbed_coeff hl hω0 hl0, twoCylinderEmbed_coeff]
  rw [ratMero_C] at hd1
  rw [hd1, (cylinderEmbed hl 0).commutes cst]

/-! ### The criterion -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The coset criterion.**  Translates of a source with exact cotangent defects are
differentially independent over the two-cylinder field exactly when their shifts lie in pairwise
distinct classes modulo the period lattice. -/
theorem differentialIndependent_orbit_iff_distinct_classes (hl : LinearIndependent ℚ l)
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
    (hd0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1))
    (hd1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst))
    {κ : Type*} [DecidableEq κ] (sh : κ → ℂ) :
    letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
    letI : Differential (RatFunc (RatFunc ℂ)) :=
      twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
    letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      (twoCylinderEmbed hl).toAlgebra
    (DifferentialIndependent (RatFunc (RatFunc ℂ))
        (fun j : κ => addTranslationMeroEquiv (sh j) M)
      ↔ ∀ i j : κ, i ≠ j → ∀ m n : ℤ,
          sh i - sh j ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1) := by
  classical
  letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
  letI : Differential (RatFunc (RatFunc ℂ)) :=
    twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
  letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    (twoCylinderEmbed hl).toAlgebra
  have hb0 : BaseDefectShift hl M (ω 0) :=
    baseDefectShift_period_zero hl hω1 hl1 M hd0
  have hb1 : BaseDefectShift hl M (ω 1) :=
    baseDefectShift_period_one hl hω0 hl0 M cst hd1
  constructor
  · intro hind i j hij m n hclass
    obtain ⟨y, hy⟩ := translate_sub_translate_eq_embed hl M hb0 hb1 (sh i) (sh j) m n hclass
    exact not_differentialIndependent_of_sub_eq_algebraMap
      (fun j : κ => addTranslationMeroEquiv (sh j) M) hij (y := y) hy hind
  · intro hsep
    exact differentialIndependent_orbit_of_exact_defects hl ω hω0 hω1 hl0 hl1 hper0 hper1
      htor hfix M cst hd0 hd1 sh hsep

/-! ### The imaginary-ray specialization -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The unconditional coset criterion.**  For periods `i a`, `i b` with `a, b > 0` and `a/b`
irrational, translates of the constructed multiple-sine source are differentially independent over
the two-cylinder field exactly when their shifts lie in pairwise distinct classes modulo the period
lattice. -/
theorem differentialIndependent_doubleSineOrbit_iff_imaginaryRay {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hirr : Irrational (a / b)) {κ : Type*} [DecidableEq κ] (sh : κ → ℂ) :
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
        (DifferentialIndependent (RatFunc (RatFunc ℂ))
            (fun j : κ => addTranslationMeroEquiv (sh j) M)
          ↔ ∀ i j : κ, i ≠ j → ∀ m n : ℤ,
              sh i - sh j ≠ (m : ℂ) * (Complex.I * (a : ℂ))
                + (n : ℂ) * (Complex.I * (b : ℂ))) := by
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
  have hiff := differentialIndependent_orbit_iff_distinct_classes hl ω hω0ne hω1ne hl0 hl1
    hper0 hper1 htor hfix M cst (by rw [hω0, hω1]; exact hM0) (by rw [hω0, hω1]; exact hM1) sh
  rw [hiff]
  constructor
  · intro h i j hij m n
    rw [← hω0, ← hω1]
    exact h i j hij m n
  · intro h i j hij m n
    rw [hω0, hω1]
    exact h i j hij m n

end

end GaloisForLFunctions.HTGeometry
