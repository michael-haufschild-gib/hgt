import GaloisForLFunctions.RHTower.XiShiftPrimeHypertranscendence
import GaloisForLFunctions.HTGeometry.PrimeExpLogFiberRigidity
import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionMatroid
import GaloisForLFunctions.HTGeometry.UpperEndRationalCoordinateDifferentialAdjoin

/-!
# Differential rank of transverse Xi prime-source shift defects

For every positive integer `a`, the coefficient stream

`Lambda(n) * (1 - n^(-a))`

is the prime source exposed by translating the zeta logarithmic derivative by `a`. This module
proves that every finite family of distinct positive shifts is jointly differentially independent,
first as a formal arithmetic family and then as actual upper-end meromorphic carriers over the
genuine rational coordinate field. Finitarity then closes the arbitrary-family interface: the
entire represented differential matroid is the pointed collision matroid of the shift labels.
Thus zero shifts are loops, repetitions are parallel, and the exact rank of any packet is the
number of distinct nonzero shifts.

The proof does not truncate the prime-power tails. It reads a proposed relation on the prime layer,
where the jets are exponential-polynomial columns

`(log p)^(k+1) * (1 - exp(-a * log p))`.

Adding the zero shift turns these differences into a subfamily of the complete prime exp/log
palette. The existing fibre-rigidity theorem kills the relation on every cofinite prime set, and
the exact prime-profile packet theorem promotes that prime-layer detection to differential
independence of the full profiles.

No declaration in this file constrains Xi zeros or proves RH. The exact matroid law shows that
safe shifted-Xi reporters lose differential rank only through the zero shift or literal shift
collisions; there is no further finite or infinite differential compression at source level.
-/

namespace RHTower

open ArithmeticFunction Filter Set
open scoped Differential LSeries.notation

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiTransverseUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiTransverseUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiTransverseUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiTransverseUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiTransverseCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiTransverseCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

/-- The unfiltered von Mangoldt coefficient stream. -/
def vonMangoldtArithmetic : ArithmeticFunction ℂ where
  toFun n := (ArithmeticFunction.vonMangoldt n : ℂ)
  map_zero' := by simp

/-- The von Mangoldt stream as a finite-abscissa source. -/
def vonMangoldtFiniteAbscissaSource : finiteAbscissaArithmeticSubalgebra := by
  refine ⟨vonMangoldtArithmetic, 1, ?_⟩
  intro y hy
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)

/-- The shift defect `Lambda(n) * (1 - n^(-a))`, constructed inside the
translation-stable finite-abscissa algebra. -/
def xiTransverseShiftFiniteAbscissaSource (a : ℕ) :
    finiteAbscissaArithmeticSubalgebra :=
  vonMangoldtFiniteAbscissaSource -
    finiteAbscissaDirichletShift (a : ℂ) vonMangoldtFiniteAbscissaSource

/-- Arithmetic profile of one transverse shift defect. -/
def xiTransverseShiftArithmetic (a : ℕ) : ArithmeticFunction ℂ :=
  (xiTransverseShiftFiniteAbscissaSource a).1

@[simp]
theorem xiTransverseShiftArithmetic_apply (a n : ℕ) :
    xiTransverseShiftArithmetic a n =
      (ArithmeticFunction.vonMangoldt n : ℂ) * (1 - cpowWeight (a : ℂ) n) := by
  change (ArithmeticFunction.vonMangoldt n : ℂ) -
      cpowWeight (a : ℂ) n * (ArithmeticFunction.vonMangoldt n : ℂ) = _
  ring

@[simp]
theorem xiTransverseShiftFiniteAbscissaSource_zero :
    xiTransverseShiftFiniteAbscissaSource 0 = 0 := by
  apply Subtype.ext
  apply ArithmeticFunction.ext
  intro n
  change xiTransverseShiftArithmetic 0 n = 0
  rw [xiTransverseShiftArithmetic_apply]
  simp [cpowWeight]

/-- **Additive source cocycle.** A shift defect at `a+b` is the defect at `a` plus the
Dirichlet-`a` translate of the defect at `b`. -/
theorem xiTransverseShiftFiniteAbscissaSource_add (a b : ℕ) :
    xiTransverseShiftFiniteAbscissaSource (a + b) =
      xiTransverseShiftFiniteAbscissaSource a +
        finiteAbscissaDirichletShift (a : ℂ)
          (xiTransverseShiftFiniteAbscissaSource b) := by
  apply Subtype.ext
  apply ArithmeticFunction.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    change (ArithmeticFunction.vonMangoldt n : ℂ) -
        cpowWeight ((a + b : ℕ) : ℂ) n *
          (ArithmeticFunction.vonMangoldt n : ℂ) =
      ((ArithmeticFunction.vonMangoldt n : ℂ) -
        cpowWeight (a : ℂ) n * (ArithmeticFunction.vonMangoldt n : ℂ)) +
      cpowWeight (a : ℂ) n *
        ((ArithmeticFunction.vonMangoldt n : ℂ) -
          cpowWeight (b : ℂ) n * (ArithmeticFunction.vonMangoldt n : ℂ))
    simp only [cpowWeight]
    push_cast
    rw [show -((a : ℂ) + (b : ℂ)) = -(a : ℂ) + -(b : ℂ) by ring,
      Complex.cpow_add _ _ hnC]
    ring

/-- **Arithmetic relative-shift normal form.** For `b ≤ a`, the difference of the two transverse
Xi sources is the Dirichlet-`b` translate of the source at the relative shift `a-b`. -/
theorem xiTransverseShiftFiniteAbscissaSource_sub_eq_dirichletShift_of_le
    (a b : ℕ) (hba : b ≤ a) :
    xiTransverseShiftFiniteAbscissaSource a -
        xiTransverseShiftFiniteAbscissaSource b =
      finiteAbscissaDirichletShift (b : ℂ)
        (xiTransverseShiftFiniteAbscissaSource (a - b)) := by
  have hadd := xiTransverseShiftFiniteAbscissaSource_add b (a - b)
  rw [Nat.add_sub_of_le hba] at hadd
  rw [hadd]
  ring

/-- Unconditional oriented source classifier: every pairwise source is one translated
nonnegative relative-shift source, with orientation supplying the sign. -/
theorem xiTransverseShiftFiniteAbscissaSource_sub_eq_relativeShift
    (a b : ℕ) :
    xiTransverseShiftFiniteAbscissaSource a -
        xiTransverseShiftFiniteAbscissaSource b =
      if b ≤ a then
        finiteAbscissaDirichletShift (b : ℂ)
          (xiTransverseShiftFiniteAbscissaSource (a - b))
      else
        -finiteAbscissaDirichletShift (a : ℂ)
          (xiTransverseShiftFiniteAbscissaSource (b - a)) := by
  by_cases hba : b ≤ a
  · rw [if_pos hba,
      xiTransverseShiftFiniteAbscissaSource_sub_eq_dirichletShift_of_le a b hba]
  · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hba)
    rw [if_neg hba,
      ← xiTransverseShiftFiniteAbscissaSource_sub_eq_dirichletShift_of_le b a hab]
    ring

/-- Actual upper-end meromorphic carrier of the shift-`a` transverse prime source. -/
def xiTransverseShiftUpperEndCarrier (a : ℕ) : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero (xiTransverseShiftFiniteAbscissaSource a)

@[simp]
theorem xiTransverseShiftUpperEndCarrier_zero :
    xiTransverseShiftUpperEndCarrier 0 = 0 := by
  simp [xiTransverseShiftUpperEndCarrier]

/-- **Meromorphic relative-shift carrier law.** Faithful upper-end realization transports the
arithmetic relative-source identity to literal meromorphic translation. -/
theorem xiTransverseShiftUpperEndCarrier_sub_eq_translation_of_le
    (a b : ℕ) (hba : b ≤ a) :
    xiTransverseShiftUpperEndCarrier a -
        xiTransverseShiftUpperEndCarrier b =
      upperEndTranslationMeroEquiv (Complex.I * (b : ℂ))
        (xiTransverseShiftUpperEndCarrier (a - b)) := by
  rw [xiTransverseShiftUpperEndCarrier,
    xiTransverseShiftUpperEndCarrier,
    xiTransverseShiftUpperEndCarrier,
    ← map_sub finiteAbscissaLSeriesToUpperEndMero,
    xiTransverseShiftFiniteAbscissaSource_sub_eq_dirichletShift_of_le a b hba,
    finiteAbscissaLSeriesToUpperEndMero_dirichletShift]

/-- The meromorphic relative-shift law with endpoint order discharged. -/
theorem xiTransverseShiftUpperEndCarrier_sub_eq_relativeShift
    (a b : ℕ) :
    xiTransverseShiftUpperEndCarrier a -
        xiTransverseShiftUpperEndCarrier b =
      if b ≤ a then
        upperEndTranslationMeroEquiv (Complex.I * (b : ℂ))
          (xiTransverseShiftUpperEndCarrier (a - b))
      else
        -upperEndTranslationMeroEquiv (Complex.I * (a : ℂ))
          (xiTransverseShiftUpperEndCarrier (b - a)) := by
  by_cases hba : b ≤ a
  · rw [if_pos hba,
      xiTransverseShiftUpperEndCarrier_sub_eq_translation_of_le a b hba]
  · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hba)
    rw [if_neg hba,
      ← xiTransverseShiftUpperEndCarrier_sub_eq_translation_of_le b a hab]
    ring

theorem xiTransverseShiftArithmetic_apply_prime (a : ℕ) (p : Nat.Primes) :
    xiTransverseShiftArithmetic a p =
      (Real.log (p : ℕ) : ℂ) * (1 - primeShiftFactor (a : ℂ) p) := by
  rw [xiTransverseShiftArithmetic_apply,
    ArithmeticFunction.vonMangoldt_apply_prime p.2,
    cpowWeight_prime_eq_primeShiftFactor]

/-- Every transverse shift defect is carried on positive prime powers. -/
theorem xiTransverseShiftArithmetic_supportedOnPositivePrimePowers (a : ℕ) :
    PrimeProfileSupportedOnPositivePrimePowers (xiTransverseShiftArithmetic a) := by
  intro n hn
  have hLambda : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro hzero
    apply hn
    simp [xiTransverseShiftArithmetic_apply, hzero]
  have hpow : IsPrimePow n :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLambda
  let x : PrimePowerClockIndex :=
    Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩
  refine ⟨x.1, x.2, ?_⟩
  have hx := congrArg Subtype.val
    (Nat.Primes.prodNatEquiv.apply_symm_apply ⟨n, hpow⟩)
  simpa only [x, Nat.Primes.coe_prodNatEquiv_apply] using hx.symm

/-- Distinct positive shifts give a tail-independent family of all finite
logarithmic jets already on the prime layer. -/
theorem xiTransverseShift_primeJets_tailIndependent
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) (m : ℕ) :
    TailCoefficientIndependent
      (fun ak : A × Fin (m + 1) => fun p : Nat.Primes =>
        primeProfileJetSource (fun a => xiTransverseShiftArithmetic (shift a)) m ak p) := by
  classical
  let alpha : Option A → ℂ
    | none => 0
    | some a => (shift a : ℂ)
  have halpha : Function.Injective (fun a => (alpha a).re) := by
    rintro (_ | a) (_ | b) h
    · rfl
    · exfalso
      have hb0 : (shift b : ℝ) = 0 := by simpa [alpha] using h.symm
      have hb0' : shift b = 0 := by exact_mod_cast hb0
      exact (Nat.ne_of_gt (hpos b)) hb0'
    · exfalso
      have ha0 : (shift a : ℝ) = 0 := by simpa [alpha] using h
      have ha0' : shift a = 0 := by exact_mod_cast ha0
      exact (Nat.ne_of_gt (hpos a)) ha0'
    · congr 1
      apply hinj
      have h' : (shift a : ℝ) = shift b := by simpa [alpha] using h
      exact_mod_cast h'
  have hrigid := primeFactorClockFiberIndependent alpha halpha m
  intro c hfinite
  let d : Option A × Fin (m + 1) → ℂ := fun ok =>
    match ok.1 with
    | none => ∑ a : A, c (a, ok.2) * Complex.I ^ (ok.2 : ℕ)
    | some a => -(c (a, ok.2) * Complex.I ^ (ok.2 : ℕ))
  have hlog_ne (p : Nat.Primes) : primeLogClock p ≠ 0 := by
    have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
    exact Complex.ofReal_ne_zero.mpr (Real.log_pos hp).ne'
  have hrelation (p : Nat.Primes) :
      (∑ ak : A × Fin (m + 1), c ak *
          primeProfileJetSource
            (fun a => xiTransverseShiftArithmetic (shift a)) m ak p) =
        primeLogClock p *
          ∑ ok : Option A × Fin (m + 1),
            d ok * primeShiftFactor (alpha ok.1) p *
              primeLogClock p ^ (ok.2 : ℕ) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [primeProfileJetSource, primeProfileRotatedLogJet_apply,
      xiTransverseShiftArithmetic_apply_prime, d, alpha]
    rw [Fintype.sum_option]
    simp only [primeShiftFactor]
    simp only [primeLogClock, mul_pow]
    conv_rhs =>
      rhs
      rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp only [neg_zero, zero_mul, Complex.exp_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_one]
    calc
      (∑ a, c (a, k) *
          (Complex.I ^ (k : ℕ) * (Real.log (p : ℕ) : ℂ) ^ (k : ℕ) *
            ((Real.log (p : ℕ) : ℂ) *
              (1 - Complex.exp (-(shift a : ℂ) * (Real.log (p : ℕ) : ℂ)))))) =
          (Real.log (p : ℕ) : ℂ) *
            ∑ a, c (a, k) * Complex.I ^ (k : ℕ) *
              (Real.log (p : ℕ) : ℂ) ^ (k : ℕ) *
                (1 - Complex.exp (-(shift a : ℂ) * (Real.log (p : ℕ) : ℂ))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = (Real.log (p : ℕ) : ℂ) *
          (((∑ a, c (a, k) * Complex.I ^ (k : ℕ)) *
              (Real.log (p : ℕ) : ℂ) ^ (k : ℕ)) +
            ∑ a, -(c (a, k) * Complex.I ^ (k : ℕ)) *
              Complex.exp (-(shift a : ℂ) * (Real.log (p : ℕ) : ℂ)) *
                (Real.log (p : ℕ) : ℂ) ^ (k : ℕ)) := by
            congr 1
            rw [Finset.sum_mul]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro a _
            ring
  have hbad :
      {p : Nat.Primes | p ∈ (Set.univ : Set Nat.Primes) ∧
        ∑ ok : Option A × Fin (m + 1),
          d ok * primeShiftFactor (alpha ok.1) p *
            primeLogClock p ^ (ok.2 : ℕ) ≠ 0}.Finite := by
    apply hfinite.subset
    intro p hp
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and] at hp ⊢
    rw [hrelation p]
    exact mul_ne_zero (hlog_ne p) hp
  have hd : d = 0 := hrigid Set.univ Set.infinite_univ d hbad
  funext ak
  have hak := congrFun hd (some ak.1, ak.2)
  simp only [d, Pi.zero_apply, neg_eq_zero] at hak
  exact (mul_eq_zero.mp hak).resolve_right
    (pow_ne_zero _ Complex.I_ne_zero)

/-- The full prime-power profiles of distinct positive transverse shifts have no
finite-prime clock-jet relation. -/
theorem xiTransverseShiftArithmetic_clockTailIndependent
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) (m : ℕ) :
    PrimeProfileTailIndependent
      (primeProfileJetSource
        (fun a => xiTransverseShiftArithmetic (shift a)) m) := by
  classical
  intro c hlocal
  apply xiTransverseShift_primeJets_tailIndependent shift hpos hinj m c
  have hrays := (primePowerClockLocal_coordinateProfile_iff
    (∑ ak, c ak • primeProfileJetSource
      (fun a => xiTransverseShiftArithmetic (shift a)) m ak)).mp hlocal
  apply hrays.subset
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  refine ⟨0, ?_⟩
  simp only [Nat.zero_add, pow_one]
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun f => f p
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ ak, c ak • primeProfileJetSource
    (fun a => xiTransverseShiftArithmetic (shift a)) m ak) ≠ 0
  rw [map_sum]
  simpa only [ev, ArithmeticFunction.smul_map, smul_eq_mul] using hp

/-- **Finite transverse source-rank theorem.** Distinct positive filtered
von-Mangoldt shift defects are differentially independent over `C`. -/
theorem xiTransverseShiftArithmetic_differentialIndependent
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun a => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
          (xiTransverseShiftArithmetic (shift a))) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hEmpty =>
      letI : IsEmpty A := hEmpty
      exact algebraicIndependent_empty_type
  | inr hNonempty =>
      letI : Nonempty A := hNonempty
      have hlarge : GaloisForLFunctions.DifferentialIndependent
          finitePrimeCoefficientField
          (fun a => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField
              (xiTransverseShiftArithmetic (shift a))) := by
        apply (differentialIndependent_fractionPrimeProfiles_iff_clockTailIndependent
          (fun a => xiTransverseShiftArithmetic (shift a))
          (fun a => xiTransverseShiftArithmetic_supportedOnPositivePrimePowers (shift a))).2
        exact xiTransverseShiftArithmetic_clockTailIndependent shift hpos hinj
      unfold GaloisForLFunctions.DifferentialIndependent at hlarge ⊢
      exact AlgebraicIndependent.restrictScalars
        (FaithfulSMul.algebraMap_injective ℂ finitePrimeCoefficientField) hlarge

/-- **Actual analytic transverse-rank theorem.** The upper-end meromorphic
carriers of distinct positive filtered von-Mangoldt shift defects are jointly
differentially independent over the genuine rational coordinate field. -/
theorem xiTransverseShiftUpperEndCarrier_differentialIndependent
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) :
    GaloisForLFunctions.DifferentialIndependent
      upperEndRationalCoordinateField
      (fun a => xiTransverseShiftUpperEndCarrier (shift a)) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hEmpty =>
      letI : IsEmpty A := hEmpty
      exact algebraicIndependent_empty_type
  | inr hNonempty =>
      letI : Nonempty A := hNonempty
      apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
      simpa [xiTransverseShiftArithmetic, xiTransverseShiftUpperEndCarrier] using
        xiTransverseShiftArithmetic_differentialIndependent shift hpos hinj

/-- Injective nonzero transverse shift families are differentially independent without a
finiteness assumption on the index type. -/
theorem xiTransverseShiftUpperEndCarrier_differentialIndependent_of_injective_ne_zero
    {A : Type*} (shift : A → ℕ) (hinj : Function.Injective shift)
    (hne : ∀ a, shift a ≠ 0) :
    GaloisForLFunctions.DifferentialIndependent
      upperEndRationalCoordinateField
      (fun a => xiTransverseShiftUpperEndCarrier (shift a)) := by
  classical
  apply differentialIndependent_of_forall_finite_subfamily
  intro I hIfinite
  by_cases hIempty : I = ∅
  · subst I
    exact algebraicIndependent_empty_type
  letI : Fintype I := hIfinite.fintype
  letI : Nonempty I :=
    Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr hIempty)
  apply xiTransverseShiftUpperEndCarrier_differentialIndependent
    (fun i : I => shift i)
  · intro i
    exact Nat.pos_of_ne_zero (hne i)
  · intro i j hij
    exact Subtype.ext (hinj hij)

/-- **Exact transverse-shift collision law.** For an arbitrary indexed shift family, zero shifts
are loops, repeated positive shifts are parallel, and distinct positive shifts are the only
differential directions. -/
theorem xiTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision
    {A : Type*} (shift : A → ℕ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun a => xiTransverseShiftUpperEndCarrier (shift a)) =
      affinePointedCollisionMatroid shift 0 := by
  apply differentialFamilyMatroid_eq_affinePointedCollisionMatroid_of_parallel
  · intro I hIinj hInonzero
    apply xiTransverseShiftUpperEndCarrier_differentialIndependent_of_injective_ne_zero
      (fun i : I => shift i)
    · intro i j hij
      exact Subtype.ext (hIinj i.2 j.2 hij)
    · intro i
      exact hInonzero i i.2
  · intro i hi
    rw [hi, xiTransverseShiftUpperEndCarrier_zero]
    exact differentialAlgebraicOver_algebraMap 0
  · intro i j _ hij
    rw [hij, sub_self]
    exact differentialAlgebraicOver_algebraMap 0

/-- Prop interface for the exact collision law: a selected packet is differentially independent
exactly when its shifts are injective and nonzero on that packet. -/
theorem xiTransverseShiftUpperEndCarrier_differentialIndependent_iff
    {A : Type*} (shift : A → ℕ) (I : Set A) :
    GaloisForLFunctions.DifferentialIndependent upperEndRationalCoordinateField
        (fun i : I => xiTransverseShiftUpperEndCarrier (shift i)) ↔
      Set.InjOn shift I ∧ ∀ i ∈ I, shift i ≠ 0 := by
  let x := fun a => xiTransverseShiftUpperEndCarrier (shift a)
  constructor
  · intro hI
    have hmatroid : (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField) x).Indep I :=
      (differentialFamilyMatroid_indep_iff x I).mpr hI
    rw [xiTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision,
      affinePointedCollisionMatroid_indep_iff] at hmatroid
    exact hmatroid
  · intro hI
    apply (differentialFamilyMatroid_indep_iff x I).mp
    rw [xiTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision,
      affinePointedCollisionMatroid_indep_iff]
    exact hI

/-- Exact differential rank of any transverse shift packet: the number of distinct nonzero shift
values, with no finiteness assumption. -/
theorem xiTransverseShiftUpperEndCarrier_differentialMatroid_eRk
    {A : Type*} (shift : A → ℕ) (I : Set A) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun a => xiTransverseShiftUpperEndCarrier (shift a))).eRk I =
      ((shift '' I) ∩ {a | a ≠ 0}).encard := by
  rw [xiTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_eRk]

end

end RHTower
