import GaloisForLFunctions.RHTower.XiTransverseShiftDefectDifferentialRank
import GaloisForLFunctions.RHTower.XiTransverseShiftPrimeDefectValueReflection

/-!
# Differential rank of the full real transverse Xi aperture

The integral-shift theorem does not cover the physical Hedenmalm aperture
`0 < a < 1/2`.  This file removes that restriction.  For every real shift
`a`, the complete prime source

`Lambda(n) * (1 - n^(-a))`

has a finite abscissa and an actual upper-end meromorphic realization.  Every
family of distinct nonzero real shifts is jointly differentially independent
over the genuine rational coordinate field.  Consequently the represented
differential matroid of an arbitrary real aperture family is exactly its
pointed collision matroid: zero is a loop, repetitions are parallel, and every
distinct nonzero aperture contributes one differential direction.

The same carrier is the actual completed-Xi logarithmic shift defect after
subtracting the exact archimedean shift defect.  Thus the theorem applies, in
particular, to arbitrary finite packets inside the physical interval
`(0, 1/2)`.
-/

namespace RHTower

open ArithmeticFunction Filter Set
open scoped Differential LSeries.notation UpperEndDifferentialInstances

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Finite-abscissa source of a real transverse Xi shift. -/
def xiRealTransverseShiftFiniteAbscissaSource (a : ℝ) :
    finiteAbscissaArithmeticSubalgebra :=
  vonMangoldtFiniteAbscissaSource -
    finiteAbscissaDirichletShift (a : ℂ) vonMangoldtFiniteAbscissaSource

/-- Arithmetic coefficient profile of a real transverse Xi shift. -/
def xiRealTransverseShiftArithmetic (a : ℝ) : ArithmeticFunction ℂ :=
  (xiRealTransverseShiftFiniteAbscissaSource a).1

@[simp]
theorem xiRealTransverseShiftArithmetic_apply (a : ℝ) (n : ℕ) :
    xiRealTransverseShiftArithmetic a n =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (1 - cpowWeight (a : ℂ) n) := by
  change (ArithmeticFunction.vonMangoldt n : ℂ) -
      cpowWeight (a : ℂ) n * (ArithmeticFunction.vonMangoldt n : ℂ) = _
  ring

@[simp]
theorem xiRealTransverseShiftFiniteAbscissaSource_zero :
    xiRealTransverseShiftFiniteAbscissaSource 0 = 0 := by
  apply Subtype.ext
  apply ArithmeticFunction.ext
  intro n
  change xiRealTransverseShiftArithmetic 0 n = 0
  rw [xiRealTransverseShiftArithmetic_apply]
  simp [cpowWeight]

/-- Actual upper-end meromorphic carrier of a real transverse Xi shift. -/
def xiRealTransverseShiftUpperEndCarrier (a : ℝ) : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero
    (xiRealTransverseShiftFiniteAbscissaSource a)

@[simp]
theorem xiRealTransverseShiftUpperEndCarrier_zero :
    xiRealTransverseShiftUpperEndCarrier 0 = 0 := by
  simp [xiRealTransverseShiftUpperEndCarrier]

theorem xiRealTransverseShiftArithmetic_apply_prime
    (a : ℝ) (p : Nat.Primes) :
    xiRealTransverseShiftArithmetic a p =
      (Real.log (p : ℕ) : ℂ) *
        (1 - primeShiftFactor (a : ℂ) p) := by
  rw [xiRealTransverseShiftArithmetic_apply,
    ArithmeticFunction.vonMangoldt_apply_prime p.2,
    cpowWeight_prime_eq_primeShiftFactor]

/-- Every real transverse shift defect is carried on positive prime powers. -/
theorem xiRealTransverseShiftArithmetic_supportedOnPositivePrimePowers
    (a : ℝ) :
    PrimeProfileSupportedOnPositivePrimePowers
      (xiRealTransverseShiftArithmetic a) := by
  intro n hn
  have hLambda : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro hzero
    apply hn
    simp [xiRealTransverseShiftArithmetic_apply, hzero]
  have hpow : IsPrimePow n :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLambda
  let x : PrimePowerClockIndex :=
    Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩
  refine ⟨x.1, x.2, ?_⟩
  have hx := congrArg Subtype.val
    (Nat.Primes.prodNatEquiv.apply_symm_apply ⟨n, hpow⟩)
  change n = (x.1 : ℕ) ^ (x.2 + 1)
  rw [← Nat.Primes.coe_prodNatEquiv_apply]
  exact hx.symm

/-- Distinct nonzero real shifts give a tail-independent family of all
finite logarithmic jets already on the prime layer. -/
theorem xiRealTransverseShift_primeJets_tailIndependent
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℝ) (hne : ∀ a, shift a ≠ 0)
    (hinj : Function.Injective shift) (m : ℕ) :
    TailCoefficientIndependent
      (fun ak : A × Fin (m + 1) => fun p : Nat.Primes =>
        primeProfileJetSource
          (fun a => xiRealTransverseShiftArithmetic (shift a)) m ak p) := by
  classical
  let alpha : Option A → ℂ
    | none => 0
    | some a => (shift a : ℂ)
  have halpha : Function.Injective (fun a => (alpha a).re) := by
    rintro (_ | a) (_ | b) h
    · rfl
    · exfalso
      apply hne b
      simpa [alpha] using h.symm
    · exfalso
      apply hne a
      simpa [alpha] using h
    · congr 1
      apply hinj
      simpa [alpha] using h
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
            (fun a => xiRealTransverseShiftArithmetic (shift a)) m ak p) =
        primeLogClock p *
          ∑ ok : Option A × Fin (m + 1),
            d ok * primeShiftFactor (alpha ok.1) p *
              primeLogClock p ^ (ok.2 : ℕ) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [primeProfileJetSource, primeProfileRotatedLogJet_apply,
      xiRealTransverseShiftArithmetic_apply_prime, d, alpha]
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
              (1 - Complex.exp
                (-(shift a : ℂ) * (Real.log (p : ℕ) : ℂ)))))) =
          (Real.log (p : ℕ) : ℂ) *
            ∑ a, c (a, k) * Complex.I ^ (k : ℕ) *
              (Real.log (p : ℕ) : ℂ) ^ (k : ℕ) *
                (1 - Complex.exp
                  (-(shift a : ℂ) * (Real.log (p : ℕ) : ℂ))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = (Real.log (p : ℕ) : ℂ) *
          (((∑ a, c (a, k) * Complex.I ^ (k : ℕ)) *
              (Real.log (p : ℕ) : ℂ) ^ (k : ℕ)) +
            ∑ a, -(c (a, k) * Complex.I ^ (k : ℕ)) *
              Complex.exp
                (-(shift a : ℂ) * (Real.log (p : ℕ) : ℂ)) *
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

/-- The complete prime-power profiles of distinct nonzero real shifts have
no finite-prime clock-jet relation. -/
theorem xiRealTransverseShiftArithmetic_clockTailIndependent
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℝ) (hne : ∀ a, shift a ≠ 0)
    (hinj : Function.Injective shift) (m : ℕ) :
    PrimeProfileTailIndependent
      (primeProfileJetSource
        (fun a => xiRealTransverseShiftArithmetic (shift a)) m) := by
  classical
  intro c hlocal
  apply xiRealTransverseShift_primeJets_tailIndependent
    shift hne hinj m c
  have hrays := (primePowerClockLocal_coordinateProfile_iff
    (∑ ak, c ak • primeProfileJetSource
      (fun a => xiRealTransverseShiftArithmetic (shift a)) m ak)).mp hlocal
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
    (fun a => xiRealTransverseShiftArithmetic (shift a)) m ak) ≠ 0
  rw [map_sum]
  simpa only [ev, ArithmeticFunction.smul_map, smul_eq_mul] using! hp

/-- Formal arithmetic differential independence of distinct nonzero real
transverse shifts. -/
theorem xiRealTransverseShiftArithmetic_differentialIndependent
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℝ) (hne : ∀ a, shift a ≠ 0)
    (hinj : Function.Injective shift) :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun a => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
          (xiRealTransverseShiftArithmetic (shift a))) := by
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
              (xiRealTransverseShiftArithmetic (shift a))) := by
        apply
          (differentialIndependent_fractionPrimeProfiles_iff_clockTailIndependent
            (fun a => xiRealTransverseShiftArithmetic (shift a))
            (fun a =>
              xiRealTransverseShiftArithmetic_supportedOnPositivePrimePowers
                (shift a))).2
        exact xiRealTransverseShiftArithmetic_clockTailIndependent
          shift hne hinj
      unfold GaloisForLFunctions.DifferentialIndependent at hlarge ⊢
      exact AlgebraicIndependent.restrictScalars
        (FaithfulSMul.algebraMap_injective ℂ finitePrimeCoefficientField) hlarge

/-- Finite packets of distinct nonzero real aperture carriers are jointly
differentially independent over the rational upper-end coordinate field. -/
theorem xiRealTransverseShiftUpperEndCarrier_differentialIndependent
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℝ) (hne : ∀ a, shift a ≠ 0)
    (hinj : Function.Injective shift) :
    GaloisForLFunctions.DifferentialIndependent
      upperEndRationalCoordinateField
      (fun a => xiRealTransverseShiftUpperEndCarrier (shift a)) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hEmpty =>
      letI : IsEmpty A := hEmpty
      exact algebraicIndependent_empty_type
  | inr hNonempty =>
      letI : Nonempty A := hNonempty
      apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
      simpa [xiRealTransverseShiftArithmetic,
        xiRealTransverseShiftUpperEndCarrier] using
          xiRealTransverseShiftArithmetic_differentialIndependent
            shift hne hinj

/-- Injective nonzero real shift families are differentially independent,
without a finiteness assumption on the index type. -/
theorem
    xiRealTransverseShiftUpperEndCarrier_differentialIndependent_of_injective_ne_zero
    {A : Type*} (shift : A → ℝ) (hinj : Function.Injective shift)
    (hne : ∀ a, shift a ≠ 0) :
    GaloisForLFunctions.DifferentialIndependent
      upperEndRationalCoordinateField
      (fun a => xiRealTransverseShiftUpperEndCarrier (shift a)) := by
  classical
  apply differentialIndependent_of_forall_finite_subfamily
  intro I hIfinite
  by_cases hIempty : I = ∅
  · subst I
    exact algebraicIndependent_empty_type
  letI : Fintype I := hIfinite.fintype
  letI : Nonempty I :=
    Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr hIempty)
  apply xiRealTransverseShiftUpperEndCarrier_differentialIndependent
    (fun i : I => shift i)
  · intro i
    exact hne i
  · intro i j hij
    exact Subtype.ext (hinj hij)

/-- Every finite packet of distinct physical apertures has full differential
rank. -/
theorem xiPhysicalApertureUpperEndCarrier_differentialIndependent
    {A : Type*} [Fintype A] [DecidableEq A]
    (aperture : A → ℝ) (hpos : ∀ a, 0 < aperture a)
    (_hhalf : ∀ a, aperture a < 1 / 2)
    (hinj : Function.Injective aperture) :
    GaloisForLFunctions.DifferentialIndependent
      upperEndRationalCoordinateField
      (fun a => xiRealTransverseShiftUpperEndCarrier (aperture a)) :=
  xiRealTransverseShiftUpperEndCarrier_differentialIndependent
    aperture (fun a => (hpos a).ne') hinj

/-- **Continuum aperture collision law.** For an arbitrary real shift family,
zero shifts are loops, repeated shifts are parallel, and distinct nonzero
shifts are the only differential directions. -/
theorem
    xiRealTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision
    {A : Type*} (shift : A → ℝ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun a => xiRealTransverseShiftUpperEndCarrier (shift a)) =
      affinePointedCollisionMatroid shift 0 := by
  apply differentialFamilyMatroid_eq_affinePointedCollisionMatroid_of_parallel
  · intro I hIinj hInonzero
    apply
      xiRealTransverseShiftUpperEndCarrier_differentialIndependent_of_injective_ne_zero
        (fun i : I => shift i)
    · intro i j hij
      exact Subtype.ext (hIinj i.2 j.2 hij)
    · intro i
      exact hInonzero i i.2
  · intro i hi
    rw [hi, xiRealTransverseShiftUpperEndCarrier_zero]
    exact differentialAlgebraicOver_algebraMap 0
  · intro i j _ hij
    rw [hij, sub_self]
    exact differentialAlgebraicOver_algebraMap 0

/-- A selected real-aperture packet is differentially independent exactly
when its labels are injective and nonzero on that packet. -/
theorem
    xiRealTransverseShiftUpperEndCarrier_differentialIndependent_iff
    {A : Type*} (shift : A → ℝ) (I : Set A) :
    GaloisForLFunctions.DifferentialIndependent
        upperEndRationalCoordinateField
        (fun i : I => xiRealTransverseShiftUpperEndCarrier (shift i)) ↔
      Set.InjOn shift I ∧ ∀ i ∈ I, shift i ≠ 0 := by
  let x := fun a => xiRealTransverseShiftUpperEndCarrier (shift a)
  constructor
  · intro hI
    have hmatroid :
        (differentialFamilyMatroid
          (F := upperEndRationalCoordinateField) x).Indep I :=
      (differentialFamilyMatroid_indep_iff x I).mpr hI
    rw [
      xiRealTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision,
      affinePointedCollisionMatroid_indep_iff] at hmatroid
    exact hmatroid
  · intro hI
    apply (differentialFamilyMatroid_indep_iff x I).mp
    rw [
      xiRealTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision,
      affinePointedCollisionMatroid_indep_iff]
    exact hI

/-- Exact differential rank of any real transverse-shift packet. -/
theorem xiRealTransverseShiftUpperEndCarrier_differentialMatroid_eRk
    {A : Type*} (shift : A → ℝ) (I : Set A) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun a => xiRealTransverseShiftUpperEndCarrier (shift a))).eRk I =
      ((shift '' I) ∩ {a | a ≠ 0}).encard := by
  rw [
    xiRealTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_eRk]

/-! ## Actual completed-Xi value reflection -/

/-- The real-shift source L-series is the difference of the von Mangoldt
L-series at `s` and `s+a`. -/
theorem LSeries_xiRealTransverseShiftArithmetic
    (a : ℝ) {s : ℂ} (hs : 1 < s.re)
    (hsa : 1 < (s + (a : ℂ)).re) :
    LSeries (fun n => xiRealTransverseShiftArithmetic a n) s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (s + (a : ℂ)) := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let g : ℕ → ℂ := fun n =>
    dirichletShift (a : ℂ) vonMangoldtArithmetic n
  have hf : LSeriesSummable f s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hshift : LSeriesSummable g s := by
    rw [show g =
        fun n => dirichletShift (a : ℂ) vonMangoldtArithmetic n by rfl,
      dirichletShift_LSeriesSummable_iff]
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt hsa
  have hsub := LSeries_sub hf hshift
  rw [show LSeries g s = LSeries f (s + (a : ℂ)) by
    exact LSeries_dirichletShift (a : ℂ) s vonMangoldtArithmetic] at hsub
  simpa [f, g, xiRealTransverseShiftArithmetic,
    xiRealTransverseShiftFiniteAbscissaSource,
    vonMangoldtFiniteAbscissaSource, vonMangoldtArithmetic] using! hsub

/-- Exact archimedean logarithmic-derivative correction at a real shift. -/
def xiRealTransverseShiftArchimedeanCorrection
    (a : ℝ) (s : ℂ) : ℂ :=
  logDeriv archFactor (s + (a : ℂ)) - logDeriv archFactor s

/-- Raw real-shift defect of the actual completed logarithmic derivative. -/
def xiRealTransverseShiftRawLogDerivDefect
    (a : ℝ) (s : ℂ) : ℂ :=
  logDeriv xi (s + (a : ℂ)) - logDeriv xi s

/-- Prime-corrected real-shift defect of the actual completed logarithmic
derivative. -/
def xiRealTransverseShiftPrimeDefect (a : ℝ) (s : ℂ) : ℂ :=
  xiRealTransverseShiftRawLogDerivDefect a s -
    xiRealTransverseShiftArchimedeanCorrection a s

/-- On their common Euler half-plane, actual completed-Xi shift defects at
arbitrary real apertures equal the complete transverse prime-source L-series. -/
theorem xiRealTransverseShiftPrimeDefect_eq_lSeries
    (a : ℝ) {s : ℂ} (hs : 1 < s.re)
    (hsa : 1 < (s + (a : ℂ)).re) :
    xiRealTransverseShiftPrimeDefect a s =
      LSeries (fun n => xiRealTransverseShiftArithmetic a n) s := by
  have hsplit :=
    seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hs
  have hsplitA :=
    seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hsa
  rw [seamFluxCochain] at hsplit hsplitA
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries hs] at hsplit
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries hsa] at hsplitA
  have hsource := LSeries_xiRealTransverseShiftArithmetic a hs hsa
  unfold xiRealTransverseShiftPrimeDefect
    xiRealTransverseShiftRawLogDerivDefect
    xiRealTransverseShiftArchimedeanCorrection
  linear_combination hsplit - hsplitA - hsource

/-- Upper-end germ of the actual corrected completed-Xi real-shift defect. -/
def xiRealTransverseShiftPrimeDefectUpperEndGerm
    (a : ℝ) : Germ upperEndFilter ℂ :=
  ((fun z : ℂ =>
    xiRealTransverseShiftPrimeDefect a (-Complex.I * z)) :
      Germ upperEndFilter ℂ)

/-- **Physical-aperture completed-Xi reflection.** The analytic carrier at
every real aperture is exactly the corrected shift defect of the actual
completed logarithmic derivative. -/
theorem
    xiRealTransverseShiftUpperEndGerm_eq_xiRealTransverseShiftPrimeDefect
    (a : ℝ) :
    finiteAbscissaLSeriesToUpperEndGerm
        (xiRealTransverseShiftFiniteAbscissaSource a) =
      xiRealTransverseShiftPrimeDefectUpperEndGerm a := by
  apply Germ.coe_eq.mpr
  have hupper :
      ∀ᶠ z in upperEndFilter, max 1 (1 - a) < z.im := by
    rw [upperEndFilter_basis.eventually_iff]
    exact ⟨max 1 (1 - a), trivial, fun _ hz => hz⟩
  filter_upwards [hupper] with z hz
  have hs : 1 < (-Complex.I * z).re := by
    rw [show (-Complex.I * z).re = z.im by
      simp [Complex.mul_re]]
    exact lt_of_le_of_lt (le_max_left _ _) hz
  have hsa : 1 < (-Complex.I * z + (a : ℂ)).re := by
    rw [show (-Complex.I * z + (a : ℂ)).re = z.im + a by
      simp [Complex.mul_re]]
    have hza : 1 - a < z.im :=
      lt_of_le_of_lt (le_max_right _ _) hz
    linarith
  have h := xiRealTransverseShiftPrimeDefect_eq_lSeries a hs hsa
  simpa [xiRealTransverseShiftPrimeDefectUpperEndGerm,
    finiteAbscissaLSeriesToUpperEndGerm,
    xiRealTransverseShiftArithmetic] using h.symm

end

end RHTower
