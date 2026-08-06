import GaloisForLFunctions.HTGeometry.DoubleSineOrbitMatroid
import GaloisForLFunctions.HTGeometry.MeromorphicRationalCoordinateDifferentialAdjoin
import GaloisForLFunctions.HTGeometry.CoordinateFieldInTwoCylinderAdjoin

/-!
# The double-sine orbit over the natural rational base

The two-cylinder function field `ℂ(u₁)(u₂)` and the embedded rational coordinate field `ℂ(z)` are
incomparable, so independence over the former is not literally independence over the latter.  The
comparison closes in two steps: restrict along the scalar tower `ℂ → ℂ(u₁)(u₂) → 𝓜`, then adjoin
the coordinate, which is differentially algebraic over the constants and whose differential
adjunction is exactly `ℂ(z)`.

The conclusion is the orbit statement over the coefficient field of algebraic differential
equations: translates of the multiple-sine source by shifts in distinct classes modulo the period
lattice satisfy no algebraic differential relation with rational-function coefficients.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance drbDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance drbComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance drbMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance drbMeroCharZero : CharZero (meroField (Set.univ : Set ℂ)) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField (Set.univ : Set ℂ))).injective

local instance drbComplexDifferential : Differential ℂ where
  deriv := 0

local instance drbComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ⟨fun c => by
    rw [deriv_algebraMap_complex_mero]
    change (0 : meroField (Set.univ : Set ℂ)) = algebraMap ℂ (meroField Set.univ) 0
    rw [map_zero]⟩

local instance drbCoordinateDifferential : Differential meromorphicRationalCoordinateField :=
  derivationClosedDifferential _ meromorphicRationalCoordinateField_derivationClosed

local instance drbCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField (meroField (Set.univ : Set ℂ)) :=
  ⟨fun x => derivationClosedDifferential_apply meromorphicRationalCoordinateField
    meromorphicRationalCoordinateField_derivationClosed x⟩

variable {l : Fin 2 → ℂ}

/-! ### The descent -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The orbit is differentially independent over `ℂ(z)`.**  Translates of a source with exact
cotangent defects, by shifts in pairwise distinct classes modulo the period lattice, satisfy no
algebraic differential relation whose coefficients are rational functions of the variable. -/
theorem doubleSineOrbit_differentialIndependent_rationalBase (hl : LinearIndependent ℚ l)
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
    {κ : Type*} [DecidableEq κ] (sh : κ → ℂ)
    (hsep : ∀ i j : κ, i ≠ j → ∀ m n : ℤ, sh i - sh j ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1) :
    DifferentialIndependent meromorphicRationalCoordinateField
      (fun j : κ => addTranslationMeroEquiv (sh j) M) := by
  classical
  letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
  letI : Differential (RatFunc (RatFunc ℂ)) :=
    twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
  letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    (twoCylinderEmbed hl).toAlgebra
  haveI : IsScalarTower ℂ (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    IsScalarTower.of_algebraMap_eq (R := ℂ) (S := RatFunc (RatFunc ℂ))
      (A := meroField (Set.univ : Set ℂ))
      fun c => (twoCylinderEmbed_algebraMap_complex hl c).symm
  have hTwo : DifferentialIndependent (RatFunc (RatFunc ℂ))
      (fun j : κ => addTranslationMeroEquiv (sh j) M) :=
    differentialIndependent_orbit_of_exact_defects hl ω hω0 hω1 hl0 hl1 hper0 hper1
      htor hfix M cst hd0 hd1 sh hsep
  have hConstants : DifferentialIndependent ℂ
      (fun j : κ => addTranslationMeroEquiv (sh j) M) :=
    DifferentialIndependent.restrictScalarsTower hTwo
  have hCoordinate := DifferentialIndependent.extendScalarsDifferentialAdjoinSingleton
    hConstants differentialAlgebraicOver_meromorphicRationalCoordinate
  rw [differentialAdjoin_meromorphicRationalCoordinate_eq] at hCoordinate
  exact hCoordinate

/-- The represented differential matroid of a separated orbit over `ℂ(z)` is free. -/
theorem doubleSineOrbit_differentialFamilyMatroid_freeOn_rationalBase
    (hl : LinearIndependent ℚ l)
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
    {κ : Type} [DecidableEq κ] (sh : κ → ℂ)
    (hsep : ∀ i j : κ, i ≠ j → ∀ m n : ℤ, sh i - sh j ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (fun j : κ => addTranslationMeroEquiv (sh j) M)
      = Matroid.freeOn Set.univ :=
  differentialFamilyMatroid_eq_freeOn_of_differentialIndependent
    (doubleSineOrbit_differentialIndependent_rationalBase hl ω hω0 hω1 hl0 hl1 hper0 hper1
      htor hfix M cst hd0 hd1 sh hsep)

/-! ### The unconditional statements -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The unconditional orbit independence over `ℂ(z)`.**  For periods `i a`, `i b` with `a, b > 0`
and `a / b` irrational there is a multiple-sine source whose translates by shifts in distinct
classes modulo the period lattice are differentially independent over the rational coordinate
field, and whose own hypertranscendence over that field is the one-element case. -/
theorem doubleSineOrbit_rationalBase_imaginaryRay {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hirr : Irrational (a / b)) {κ : Type*} [DecidableEq κ] (sh : κ → ℂ)
    (hsep : ∀ i j : κ, i ≠ j → ∀ m n : ℤ,
      sh i - sh j ≠ (m : ℂ) * (Complex.I * (a : ℂ)) + (n : ℂ) * (Complex.I * (b : ℂ))) :
    ∃ M : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (Complex.I * (a : ℂ)) M - M
          = -periodCotMero (Complex.I * (b : ℂ)) ∧
        DifferentialIndependent meromorphicRationalCoordinateField
          (fun j : κ => addTranslationMeroEquiv (sh j) M) ∧
        HypertranscendentalOver meromorphicRationalCoordinateField M := by
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
  have hd0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1) := by
    rw [hω0, hω1]; exact hM0
  have hd1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst) := by
    rw [hω0, hω1]; exact hM1
  have hsep' : ∀ i j : κ, i ≠ j → ∀ m n : ℤ,
      sh i - sh j ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1 := by
    intro i j hij m n
    rw [hω0, hω1]
    exact hsep i j hij m n
  refine ⟨M, hM0, ?_, ?_⟩
  · exact doubleSineOrbit_differentialIndependent_rationalBase hl ω hω0ne hω1ne hl0 hl1
      hper0 hper1 htor hfix M cst hd0 hd1 sh hsep'
  · have hunit : ∀ i j : Unit, i ≠ j → ∀ m n : ℤ,
        (fun _ : Unit => (0 : ℂ)) i - (fun _ : Unit => (0 : ℂ)) j
          ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1 := by
      intro i j hij
      exact absurd (Subsingleton.elim i j) hij
    have hone := doubleSineOrbit_differentialIndependent_rationalBase hl ω hω0ne hω1ne hl0 hl1
      hper0 hper1 htor hfix M cst hd0 hd1 (fun _ : Unit => (0 : ℂ)) hunit
    rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
    have hrw : (fun j : Unit => addTranslationMeroEquiv ((fun _ : Unit => (0 : ℂ)) j) M)
        = fun _ : Unit => M := by
      funext j
      exact addTranslationMeroEquiv_zero_apply M
    rw [hrw] at hone
    exact hone

end

end GaloisForLFunctions.HTGeometry
