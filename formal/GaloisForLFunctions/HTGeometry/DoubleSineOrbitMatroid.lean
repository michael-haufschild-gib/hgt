import GaloisForLFunctions.HTGeometry.DoubleSineOrbitCosetCriterion
import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionMatroid
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# The differential matroid of the double-sine orbit

The coset criterion, read as a matroid.  Translates of a multiple-sine source by shifts `sh j`
represent exactly the collision matroid of the classes of the shifts modulo the period lattice:
a subfamily is differentially independent over the two-cylinder field precisely when its shifts
have pairwise distinct classes, and the rank of any subfamily is the number of distinct classes
that it meets.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-! ### The period lattice and its classes -/

/-- The lattice of integer combinations of two complex periods. -/
def doubleSinePeriodLattice (ω : Fin 2 → ℂ) : AddSubgroup ℂ where
  carrier := {z | ∃ m n : ℤ, z = (m : ℂ) * ω 0 + (n : ℂ) * ω 1}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro a b ⟨m₁, n₁, rfl⟩ ⟨m₂, n₂, rfl⟩
    refine ⟨m₁ + m₂, n₁ + n₂, ?_⟩
    push_cast
    ring
  neg_mem' := by
    rintro a ⟨m, n, rfl⟩
    refine ⟨-m, -n, ?_⟩
    push_cast
    ring

theorem mem_periodLattice_iff (ω : Fin 2 → ℂ) (z : ℂ) :
    z ∈ doubleSinePeriodLattice ω ↔ ∃ m n : ℤ, z = (m : ℂ) * ω 0 + (n : ℂ) * ω 1 := Iff.rfl

/-- The class of a shift modulo the period lattice. -/
def periodClass (ω : Fin 2 → ℂ) (z : ℂ) : ℂ ⧸ doubleSinePeriodLattice ω :=
  QuotientAddGroup.mk z

theorem periodClass_eq_iff (ω : Fin 2 → ℂ) (a b : ℂ) :
    periodClass ω a = periodClass ω b ↔
      ∃ m n : ℤ, a - b = (m : ℂ) * ω 0 + (n : ℂ) * ω 1 :=
  QuotientAddGroup.eq_iff_sub_mem

theorem periodClass_ne_iff (ω : Fin 2 → ℂ) (a b : ℂ) :
    periodClass ω a ≠ periodClass ω b ↔
      ∀ m n : ℤ, a - b ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1 := by
  constructor
  · intro h m n hcon
    exact h ((periodClass_eq_iff ω a b).2 ⟨m, n, hcon⟩)
  · intro h hcon
    obtain ⟨m, n, hmn⟩ := (periodClass_eq_iff ω a b).1 hcon
    exact h m n hmn

/-! ### The represented matroid -/

local instance domDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance domComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance domMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance domMeroCharZero : CharZero (meroField (Set.univ : Set ℂ)) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField (Set.univ : Set ℂ))).injective

variable {l : Fin 2 → ℂ}

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The double-sine orbit represents the collision matroid of the shift classes.**  The family
of translates of a source with exact cotangent defects has, as its represented differential
matroid over the two-cylinder function field, exactly the collision matroid of the classes of the
shifts modulo the period lattice. -/
theorem doubleSineOrbit_differentialFamilyMatroid (hl : LinearIndependent ℚ l)
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
    {κ : Type*} (sh : κ → ℂ) :
    letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
    letI : Differential (RatFunc (RatFunc ℂ)) :=
      twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
    letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      (twoCylinderEmbed hl).toAlgebra
    letI : DifferentialAlgebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      ⟨fun y => meroFieldDeriv_twoCylinderEmbed hl y⟩
    differentialFamilyMatroid (F := RatFunc (RatFunc ℂ))
        (fun j : κ => addTranslationMeroEquiv (sh j) M)
      = affineCollisionMatroid (periodClass ω ∘ sh) := by
  classical
  letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
  letI : Differential (RatFunc (RatFunc ℂ)) :=
    twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
  letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    (twoCylinderEmbed hl).toAlgebra
  letI : DifferentialAlgebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    ⟨fun y => meroFieldDeriv_twoCylinderEmbed hl y⟩
  have hb0 : BaseDefectShift hl M (ω 0) :=
    baseDefectShift_period_zero hl hω1 hl1 M hd0
  have hb1 : BaseDefectShift hl M (ω 1) :=
    baseDefectShift_period_one hl hω0 hl0 M cst hd1
  refine differentialFamilyMatroid_eq_affineCollisionMatroid_of_parallel
    (fun j : κ => addTranslationMeroEquiv (sh j) M) (periodClass ω ∘ sh) ?_ ?_
  · intro I hinj
    have hsep : ∀ i j : (I : Set κ), i ≠ j → ∀ m n : ℤ,
        sh i - sh j ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1 := by
      intro i j hij m n hcon
      have hclass : periodClass ω (sh i) = periodClass ω (sh j) :=
        (periodClass_eq_iff ω _ _).2 ⟨m, n, hcon⟩
      exact hij (Subtype.ext (hinj i.2 j.2 hclass))
    exact differentialIndependent_orbit_of_exact_defects hl ω hω0 hω1 hl0 hl1 hper0 hper1
      htor hfix M cst hd0 hd1 (fun i : (I : Set κ) => sh i) hsep
  · intro i j _ hframe
    obtain ⟨m, n, hclass⟩ := (periodClass_eq_iff ω (sh i) (sh j)).1 hframe
    obtain ⟨y, hy⟩ := translate_sub_translate_eq_embed hl M hb0 hb1 (sh i) (sh j) m n hclass
    have hda := differentialAlgebraicOver_algebraMap
      (F := RatFunc (RatFunc ℂ)) (E := meroField (Set.univ : Set ℂ)) y
    rw [hy]
    exact hda

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The exact rank law.**  On every indexed subpacket the differential rank of the orbit is the
number of distinct classes of shifts modulo the period lattice that the packet meets. -/
theorem doubleSineOrbit_eRk (hl : LinearIndependent ℚ l)
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
    {κ : Type*} (sh : κ → ℂ) (I : Set κ) :
    letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
    letI : Differential (RatFunc (RatFunc ℂ)) :=
      twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
    letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      (twoCylinderEmbed hl).toAlgebra
    letI : DifferentialAlgebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      ⟨fun y => meroFieldDeriv_twoCylinderEmbed hl y⟩
    (differentialFamilyMatroid (F := RatFunc (RatFunc ℂ))
        (fun j : κ => addTranslationMeroEquiv (sh j) M)).eRk I
      = ((periodClass ω ∘ sh) '' I).encard := by
  letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
  letI : Differential (RatFunc (RatFunc ℂ)) :=
    twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
  letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    (twoCylinderEmbed hl).toAlgebra
  letI : DifferentialAlgebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    ⟨fun y => meroFieldDeriv_twoCylinderEmbed hl y⟩
  rw [doubleSineOrbit_differentialFamilyMatroid hl ω hω0 hω1 hl0 hl1 hper0 hper1 htor hfix
    M cst hd0 hd1 sh, affineCollisionMatroid_eRk]

/-! ### The unconditional imaginary-ray orbit matroid -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The unconditional orbit matroid.**  For periods `i a`, `i b` with `a, b > 0` and `a / b`
irrational there is a multiple-sine source whose translate family represents exactly the collision
matroid of the shift classes modulo the period lattice, with rank equal to the number of distinct
classes met. -/
theorem doubleSineOrbit_matroid_imaginaryRay {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hirr : Irrational (a / b)) {κ : Type*} (sh : κ → ℂ) :
    letI : Differential (RatFunc ℂ) :=
      cylinderDifferential (2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (a : ℂ)))
    letI : Differential (RatFunc (RatFunc ℂ)) :=
      twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ)
        (2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (b : ℂ))))
    letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      (twoCylinderEmbed (linearIndependent_cylinderFrequencies_imaginaryRay ha hb hirr)).toAlgebra
    letI : DifferentialAlgebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      ⟨fun y => meroFieldDeriv_twoCylinderEmbed
        (linearIndependent_cylinderFrequencies_imaginaryRay ha hb hirr) y⟩
    ∃ M : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (Complex.I * (a : ℂ)) M - M
          = -periodCotMero (Complex.I * (b : ℂ)) ∧
        differentialFamilyMatroid (F := RatFunc (RatFunc ℂ))
            (fun j : κ => addTranslationMeroEquiv (sh j) M)
          = affineCollisionMatroid
            (periodClass ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] ∘ sh) ∧
        ∀ I : Set κ,
          (differentialFamilyMatroid (F := RatFunc (RatFunc ℂ))
              (fun j : κ => addTranslationMeroEquiv (sh j) M)).eRk I
            = ((periodClass ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] ∘ sh) '' I).encard := by
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
  refine ⟨M, hM0, ?_, ?_⟩
  · exact doubleSineOrbit_differentialFamilyMatroid hl ω hω0ne hω1ne hl0 hl1 hper0 hper1
      htor hfix M cst (by rw [hω0, hω1]; exact hM0) (by rw [hω0, hω1]; exact hM1) sh
  · intro I
    exact doubleSineOrbit_eRk hl ω hω0ne hω1ne hl0 hl1 hper0 hper1
      htor hfix M cst (by rw [hω0, hω1]; exact hM0) (by rw [hω0, hω1]; exact hM1) sh I

end

end GaloisForLFunctions.HTGeometry
