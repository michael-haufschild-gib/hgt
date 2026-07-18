import GaloisForLFunctions.RHTower.XiShiftPrimeHypertranscendence
import GaloisForLFunctions.HTGeometry.PrimeExpLogFiberRigidity

/-!
# Differential rank of transverse Xi prime-source shift defects

For every positive integer `a`, the coefficient stream

`Lambda(n) * (1 - n^(-a))`

is the prime source exposed by translating the zeta logarithmic derivative by `a`. This module
proves that every finite family of distinct positive shifts is jointly differentially independent,
first as a formal arithmetic family and then as actual upper-end meromorphic carriers over the
genuine rational coordinate field.

The proof does not truncate the prime-power tails. It reads a proposed relation on the prime layer,
where the jets are exponential-polynomial columns

`(log p)^(k+1) * (1 - exp(-a * log p))`.

Adding the zero shift turns these differences into a subfamily of the complete prime exp/log
palette. The existing fibre-rigidity theorem kills the relation on every cofinite prime set, and
the exact prime-profile packet theorem promotes that prime-layer detection to differential
independence of the full profiles.

No declaration in this file constrains Xi zeros or proves RH. The theorem shows that a finite
package of safe shifted-Xi reporters cannot differentially compress the transverse prime-source
flow.
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

local instance xiTransverseUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

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
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun a => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
          (xiTransverseShiftArithmetic (shift a))) := by
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
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) :
    GaloisForLFunctions.DifferentialIndependent
      upperEndRationalCoordinateField
      (fun a => finiteAbscissaLSeriesToUpperEndMero
        (xiTransverseShiftFiniteAbscissaSource (shift a))) := by
  apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
  simpa [xiTransverseShiftArithmetic] using
    xiTransverseShiftArithmetic_differentialIndependent shift hpos hinj

end

end RHTower
