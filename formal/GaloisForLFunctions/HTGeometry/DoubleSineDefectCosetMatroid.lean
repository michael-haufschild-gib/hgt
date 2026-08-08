import GaloisForLFunctions.HTGeometry.DoubleSineRationalBaseCollisionMatroid
import GaloisForLFunctions.HTGeometry.MeromorphicRationalBaseOperatorMatroid
import GaloisForLFunctions.HTGeometry.TranslateFamilyIndependence

/-!
# The differential matroid of double-sine translation defects

For an irrational two-period double-sine source, the defect at a shift `h` is the translate at
`h` minus the unshifted source.  The zero period class is therefore a differential-algebraic loop,
equal nonzero period classes are parallel, and distinct nonzero classes are differentially
independent.  This file packages those three facts as the exact pointed collision matroid and its
rank law over the rational coordinate differential field.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance doubleSineDefectCosetDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance doubleSineDefectCosetComplexAlgebra :
    Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance doubleSineDefectCosetMeroDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance doubleSineDefectCosetMeroCharZero :
    CharZero (meroField (Set.univ : Set ℂ)) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField (Set.univ : Set ℂ))).injective

local instance doubleSineDefectCosetComplexDifferential : Differential ℂ where
  deriv := 0

local instance doubleSineDefectCosetComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ⟨fun c => by
    rw [deriv_algebraMap_complex_mero]
    change (0 : meroField (Set.univ : Set ℂ)) = algebraMap ℂ (meroField Set.univ) 0
    rw [map_zero]⟩

local instance doubleSineDefectCosetCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  derivationClosedDifferential _ meromorphicRationalCoordinateField_derivationClosed

local instance doubleSineDefectCosetCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (meroField (Set.univ : Set ℂ)) :=
  ⟨fun x => derivationClosedDifferential_apply meromorphicRationalCoordinateField
    meromorphicRationalCoordinateField_derivationClosed x⟩

/-- The additive double-sine defect family attached to arbitrary shifts. -/
def doubleSineDefectFamily {κ : Type*} (sh : κ → ℂ)
    (M : meroField (Set.univ : Set ℂ)) : κ → meroField (Set.univ : Set ℂ) :=
  fun i => addTranslationMeroEquiv (sh i) M - M

variable {l : Fin 2 → ℂ}

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Exact double-sine defect-coset matroid over `ℂ(z)`.**  The additive defects of a source with
the exact two cotangent increments represent the pointed collision matroid of their period-lattice
classes.  The zero class is the loop class and each nonzero class is one parallel class. -/
theorem doubleSineDefect_differentialFamilyMatroid_rationalBase
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
    {κ : Type*} (sh : κ → ℂ) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (doubleSineDefectFamily sh M) =
      affinePointedCollisionMatroid (periodClass ω ∘ sh) 0 := by
  classical
  have hb0 : BaseDefectShift hl M (ω 0) :=
    baseDefectShift_period_zero hl hω1 hl1 M hd0
  have hb1 : BaseDefectShift hl M (ω 1) :=
    baseDefectShift_period_one hl hω0 hl0 M cst hd1
  apply differentialFamilyMatroid_eq_affinePointedCollisionMatroid_of_parallel
  · intro I hinj hnonloop
    let osh : Option I → ℂ := fun o => o.elim 0 (fun i => sh i)
    have hsep : ∀ i j : Option I, i ≠ j → ∀ m n : ℤ,
        osh i - osh j ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1 := by
      intro i j hij m n hcon
      have hclass : periodClass ω (osh i) = periodClass ω (osh j) :=
        (periodClass_eq_iff ω _ _).2 ⟨m, n, hcon⟩
      cases i with
      | none =>
          cases j with
          | none => exact hij rfl
          | some j =>
              have hj0 : (periodClass ω ∘ sh) j = 0 := by
                simpa [osh, Function.comp_def, periodClass] using hclass.symm
              exact hnonloop j j.property hj0
      | some i =>
          cases j with
          | none =>
              have hi0 : (periodClass ω ∘ sh) i = 0 := by
                simpa [osh, Function.comp_def, periodClass] using hclass
              exact hnonloop i i.property hi0
          | some j =>
              have hijVal : (i : κ) = (j : κ) :=
                hinj i.property j.property (by simpa [osh, Function.comp_def] using hclass)
              exact hij (congrArg some (Subtype.ext hijVal))
    have horbit := doubleSineOrbit_differentialIndependent_rationalBase hl ω hω0 hω1
      hl0 hl1 hper0 hper1 htor hfix M cst hd0 hd1 osh hsep
    have horbit' : DifferentialIndependent meromorphicRationalCoordinateField
        (fun o : Option I => o.elim M
          (fun i => addTranslationMeroEquiv (sh i) M)) := by
      have hfamily :
          (fun o : Option I => addTranslationMeroEquiv (osh o) M) =
            (fun o : Option I => o.elim M
              (fun i => addTranslationMeroEquiv (sh i) M)) := by
        funext o
        cases o with
        | none => exact addTranslationMeroEquiv_zero_apply M
        | some i => rfl
      rw [hfamily] at horbit
      exact horbit
    have hshear := differentialIndependent_option_sub_base M
      (fun i : I => addTranslationMeroEquiv (sh i) M) horbit'
    have hsub := hshear.comp (fun i : I => some i) (Option.some_injective I)
    have hfamily :
        ((fun o : Option I => o.elim M
            (fun i => addTranslationMeroEquiv (sh i) M - M)) ∘
          (fun i : I => some i)) =
        (fun i : I => doubleSineDefectFamily sh M i) := by
      funext i
      rfl
    rw [hfamily] at hsub
    exact hsub
  · intro i hclass
    have hclass' : periodClass ω (sh i) = periodClass ω 0 := by
      simpa [Function.comp_def, periodClass] using hclass
    obtain ⟨m, n, hmn⟩ := (periodClass_eq_iff ω (sh i) 0).1 hclass'
    obtain ⟨y, hy⟩ := translate_sub_translate_eq_embed hl M hb0 hb1 (sh i) 0 m n hmn
    have hy' : doubleSineDefectFamily sh M i = twoCylinderEmbed hl y := by
      simpa [doubleSineDefectFamily, addTranslationMeroEquiv_zero_apply] using hy
    rw [hy']
    exact differentialAlgebraicOver_rationalBase_twoCylinderEmbed hl y
  · intro i j _ hclass
    obtain ⟨m, n, hmn⟩ :=
      (periodClass_eq_iff ω (sh i) (sh j)).1 (by simpa [Function.comp_def] using hclass)
    obtain ⟨y, hy⟩ := translate_sub_translate_eq_embed hl M hb0 hb1 (sh i) (sh j) m n hmn
    have hy' : doubleSineDefectFamily sh M i - doubleSineDefectFamily sh M j =
        twoCylinderEmbed hl y := by
      rw [doubleSineDefectFamily, doubleSineDefectFamily]
      calc
        (addTranslationMeroEquiv (sh i) M - M) -
            (addTranslationMeroEquiv (sh j) M - M) =
          addTranslationMeroEquiv (sh i) M - addTranslationMeroEquiv (sh j) M := by ring
        _ = twoCylinderEmbed hl y := hy
    rw [hy']
    exact differentialAlgebraicOver_rationalBase_twoCylinderEmbed hl y

/-- **Exact arbitrary-subpacket defect rank.**  Differential rank equals the number of distinct
nonzero period classes represented by the selected defects. -/
theorem doubleSineDefect_eRk_rationalBase
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
    {κ : Type*} (sh : κ → ℂ) (I : Set κ) :
    (differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (doubleSineDefectFamily sh M)).eRk I =
      (((periodClass ω ∘ sh) '' I) ∩ {q | q ≠ 0}).encard := by
  rw [doubleSineDefect_differentialFamilyMatroid_rationalBase hl ω hω0 hω1 hl0 hl1
    hper0 hper1 htor hfix M cst hd0 hd1 sh,
    affinePointedCollisionMatroid_eRk]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Exact finite differential-operator superposition rank.**  For any finite packet of shifts
in distinct period-lattice classes and any finite family of constant-coefficient differential-
operator rows, the differential rank of the resulting double-sine superpositions over `ℂ(z)` is
exactly the `ℂ(δ)`-dimension of the localized row span.  Taking the shifts to be representatives
of the common finite support of group-algebra elements gives the full finite `ℂ[δ][ℂ/H]` law. -/
theorem doubleSineSeparatedOrbit_operatorRows_eRk_rationalBase
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
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (sh : κ → ℂ)
    (hsep : ∀ i j : κ, i ≠ j → ∀ m n : ℤ,
      sh i - sh j ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1)
    (L : ι → κ → Polynomial ℂ) (I : Finset ι) :
    (differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (differentialOperatorRowApply L
          (fun j : κ => addTranslationMeroEquiv (sh j) M))).eRk (↑I : Set ι) =
      (Module.finrank (FractionRing (Polynomial ℂ))
        (Submodule.span (FractionRing (Polynomial ℂ))
          ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ι))) : ℕ∞) := by
  exact differentialOperatorRows_eRk_rationalBase_eq_finrank_span L
    (fun j : κ => addTranslationMeroEquiv (sh j) M)
    (doubleSineOrbit_differentialIndependent_rationalBase hl ω hω0 hω1 hl0 hl1
      hper0 hper1 htor hfix M cst hd0 hd1 sh hsep) I

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Unconditional double-sine defect-coset theorem.**  For positive imaginary-ray periods with
irrational ratio there is a meromorphic double-sine source whose additive defects represent over
`ℂ(z)` exactly the pointed period-class collision matroid, and every subpacket has rank equal to
the number of distinct nonzero classes that it meets. -/
theorem doubleSineDefect_rationalBase_matroid_imaginaryRay
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hirr : Irrational (a / b))
    {κ : Type*} (sh : κ → ℂ) :
    ∃ M : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (Complex.I * (a : ℂ)) M - M
          = -periodCotMero (Complex.I * (b : ℂ)) ∧
        differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
            (doubleSineDefectFamily sh M) =
          affinePointedCollisionMatroid
            (periodClass ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] ∘ sh) 0 ∧
        ∀ I : Set κ,
          (differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
              (doubleSineDefectFamily sh M)).eRk I =
            ((((periodClass ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] ∘ sh) '' I) ∩
              {q | q ≠ 0}).encard) := by
  classical
  set ω : Fin 2 → ℂ := ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] with hωdef
  have hω0 : ω 0 = Complex.I * (a : ℂ) := by simp [hωdef]
  have hω1 : ω 1 = Complex.I * (b : ℂ) := by simp [hωdef]
  have haC : ((a : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt ha
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hb
  have hω0ne : ω 0 ≠ 0 := by rw [hω0]; exact mul_ne_zero Complex.I_ne_zero haC
  have hω1ne : ω 1 ≠ 0 := by rw [hω1]; exact mul_ne_zero Complex.I_ne_zero hbC
  set l : Fin 2 → ℂ :=
    ![2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (a : ℂ)),
      2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (b : ℂ))] with hldef
  have hl : LinearIndependent ℚ l :=
    linearIndependent_cylinderFrequencies_imaginaryRay ha hb hirr
  have hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0 := by rw [hldef, hω0]; simp
  have hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1 := by rw [hldef, hω1]; simp
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
    intro z h0 h1
    rw [hω0] at h0
    rw [hω1] at h1
    exact exists_constant_of_two_imaginaryPeriods_fixed hirr h0 h1
  obtain ⟨M, cst, hM0, hM1⟩ := exists_doubleSine_source_imaginaryRay ha hb
  have hd0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1) := by
    rw [hω0, hω1]
    exact hM0
  have hd1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst) := by
    rw [hω0, hω1]
    exact hM1
  refine ⟨M, hM0, ?_, ?_⟩
  · simpa [ω, hωdef] using
      doubleSineDefect_differentialFamilyMatroid_rationalBase hl ω hω0ne hω1ne hl0 hl1
        hper0 hper1 htor hfix M cst hd0 hd1 sh
  · intro I
    simpa [ω, hωdef] using
      doubleSineDefect_eRk_rationalBase hl ω hω0ne hω1ne hl0 hl1 hper0 hper1
        htor hfix M cst hd0 hd1 sh I

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Unconditional finite group-algebra rank law on the imaginary ray.**  For positive periods
with irrational ratio and any finite separated shift support, one constructed double-sine source
realizes the exact `ℂ(δ)` row rank of every finite constant-coefficient differential-translation
superposition over `ℂ(z)`. -/
theorem doubleSineSeparatedOrbit_operatorRows_eRk_imaginaryRay
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hirr : Irrational (a / b))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (sh : κ → ℂ)
    (hsep : ∀ i j : κ, i ≠ j → ∀ m n : ℤ,
      sh i - sh j ≠
        (m : ℂ) * (Complex.I * (a : ℂ)) + (n : ℂ) * (Complex.I * (b : ℂ)))
    (L : ι → κ → Polynomial ℂ) (I : Finset ι) :
    ∃ M : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (Complex.I * (a : ℂ)) M - M
          = -periodCotMero (Complex.I * (b : ℂ)) ∧
        (differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
            (differentialOperatorRowApply L
              (fun j : κ => addTranslationMeroEquiv (sh j) M))).eRk (↑I : Set ι) =
          (Module.finrank (FractionRing (Polynomial ℂ))
            (Submodule.span (FractionRing (Polynomial ℂ))
              ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ι))) : ℕ∞) := by
  classical
  set ω : Fin 2 → ℂ := ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] with hωdef
  have hω0 : ω 0 = Complex.I * (a : ℂ) := by simp [hωdef]
  have hω1 : ω 1 = Complex.I * (b : ℂ) := by simp [hωdef]
  have haC : ((a : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt ha
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hb
  have hω0ne : ω 0 ≠ 0 := by rw [hω0]; exact mul_ne_zero Complex.I_ne_zero haC
  have hω1ne : ω 1 ≠ 0 := by rw [hω1]; exact mul_ne_zero Complex.I_ne_zero hbC
  set l : Fin 2 → ℂ :=
    ![2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (a : ℂ)),
      2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (b : ℂ))] with hldef
  have hl : LinearIndependent ℚ l :=
    linearIndependent_cylinderFrequencies_imaginaryRay ha hb hirr
  have hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0 := by rw [hldef, hω0]; simp
  have hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1 := by rw [hldef, hω1]; simp
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
    intro z h0 h1
    rw [hω0] at h0
    rw [hω1] at h1
    exact exists_constant_of_two_imaginaryPeriods_fixed hirr h0 h1
  obtain ⟨M, cst, hM0, hM1⟩ := exists_doubleSine_source_imaginaryRay ha hb
  have hd0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1) := by
    rw [hω0, hω1]
    exact hM0
  have hd1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst) := by
    rw [hω0, hω1]
    exact hM1
  have hsepω : ∀ i j : κ, i ≠ j → ∀ m n : ℤ,
      sh i - sh j ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1 := by
    intro i j hij m n
    rw [hω0, hω1]
    exact hsep i j hij m n
  refine ⟨M, hM0, ?_⟩
  exact doubleSineSeparatedOrbit_operatorRows_eRk_rationalBase hl ω hω0ne hω1ne
    hl0 hl1 hper0 hper1 htor hfix M cst hd0 hd1 sh hsepω L I

end

end GaloisForLFunctions.HTGeometry
