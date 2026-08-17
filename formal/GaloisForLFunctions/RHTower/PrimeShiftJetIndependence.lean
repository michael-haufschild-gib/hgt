import Mathlib
import GaloisForLFunctions.HTGeometry.CommonLayerPrimeJetIndependence
import GaloisForLFunctions.HTGeometry.PrimeValuationLeadingEchelonInfinite
import GaloisForLFunctions.RHTower.PrimeSourceCancellationBudget
import GaloisForLFunctions.RHTower.XiTranslationOrbitFreeness

/-!
# Complex-shift jet independence of a prime-power Dirichlet source

At a prime `p` the jet family `D^k F(s + h_j)` of an ordinary Dirichlet series has coefficient
vector `a_p (-log p)^k p^{-h_j}`.  A nonzero linear functional annihilating a cofinite prime tail
would make a nonzero exponential polynomial with polynomial coefficients vanish at all but
finitely many prime logarithms, which the finite-exponential-type zero count forbids.  Hence the
prime feature vectors are tail independent, and the common-layer jet law turns that into algebraic
independence of the whole rectangle of translates and derivative jets over `ℂ`.

The finite-abscissa transfer then gives the same statement for the actual upper-end meromorphic
carriers over the genuine rational coordinate field, and the exposed `+2` xi shift defect
satisfies every hypothesis.
-/

namespace GaloisForLFunctions.RHTower.PrimeShiftJet

open Finset GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.CExpPoly
open GaloisForLFunctions.RHTower.PrimeCancellation

/-- The polynomial block attached to one shift by a finite jet coefficient vector. -/
noncomputable def jetBlock {m : ℕ} (γ : Fin (m + 1) → ℂ) : Polynomial ℂ :=
  scaleComp Complex.I (finPoly γ)

theorem eval_jetBlock {m : ℕ} (γ : Fin (m + 1) → ℂ) (z : ℂ) :
    (jetBlock γ).eval z = ∑ k : Fin (m + 1), γ k * (Complex.I * z) ^ (k : ℕ) := by
  rw [jetBlock, eval_scaleComp, eval_finPoly]

theorem jetBlock_eq_zero {m : ℕ} {γ : Fin (m + 1) → ℂ} (h : jetBlock γ = 0) : γ = 0 := by
  by_contra hγ
  exact scaleComp_ne_zero Complex.I_ne_zero (finPoly_ne_zero hγ) h

theorem prime_cpow_neg {a : ℂ} (p : Nat.Primes) :
    ((p : ℕ) : ℂ) ^ (-a) = Complex.exp (-a * ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) := by
  rw [cpow_neg_eq_exp a p.2.pos, complex_log_prime]

/-- **Prime-feature tail-span law.**  If the source coefficient is nonzero at all but finitely
many primes, then the shift--jet feature vectors of arbitrary distinct complex shifts and
arbitrary jet orders are tail independent: no nonzero linear functional annihilates a cofinite
prime tail. -/
theorem primeShiftJet_tailCoefficientIndependent
    {q m : ℕ} (F : ArithmeticFunction ℂ)
    (hzeros : {p : Nat.Primes | F ((p : ℕ)) = 0}.Finite)
    (h : Fin q → ℂ) (hdistinct : Function.Injective h) :
    TailCoefficientIndependent
      (fun x : Fin q × Fin (m + 1) => fun p : Nat.Primes =>
        (dirichletShift (h x.1) F) ((p : ℕ)) * rotatedPrimeLogClock p ^ (x.2 : ℕ)) := by
  classical
  intro γ hfin
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    funext x
    exact absurd x.1.2 (by omega)
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  set c : Fin (q' + 1) → ℂ := fun j => -(h j) with hc
  have hcinj : Function.Injective c := fun i j hij => hdistinct (neg_injective hij)
  set P : Fin (q' + 1) → Polynomial ℂ := fun j => jetBlock (fun k => γ (j, k)) with hP
  have hpoint : ∀ p : Nat.Primes,
      (∑ x : Fin (q' + 1) × Fin (m + 1), γ x *
          ((dirichletShift (h x.1) F) ((p : ℕ)) * rotatedPrimeLogClock p ^ (x.2 : ℕ)))
        = F ((p : ℕ)) * cexpFn c P (((Real.log ((p : ℕ) : ℝ) : ℝ)) : ℂ) := by
    intro p
    rw [Fintype.sum_prod_type]
    unfold cexpFn
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [eval_jetBlock, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [dirichletShift_apply, cpowWeight, prime_cpow_neg, hc, rotatedPrimeLogClock, primeLogClock]
    ring
  have hEfin : {p : Nat.Primes |
      cexpFn c P (((Real.log ((p : ℕ) : ℝ) : ℝ)) : ℂ) ≠ 0}.Finite := by
    refine (hzeros.union hfin).subset ?_
    intro p hp
    by_cases hF : F ((p : ℕ)) = 0
    · exact Or.inl hF
    · refine Or.inr ?_
      simp only [Set.mem_setOf_eq, hpoint p]
      exact mul_ne_zero hF hp
  obtain ⟨C, A, hC, hA, hgrow⟩ := exists_exponentialType_bound c P
  set E : Finset ℕ := hEfin.toFinset.image (fun p : Nat.Primes => (p : ℕ)) with hE
  have hzeroFn : ∀ p : ℕ, p.Prime → p ∉ E →
      cexpFn c P ((Real.log (p : ℝ) : ℝ) : ℂ) = 0 := by
    intro p hp hpE
    by_contra hne
    exact hpE (by
      rw [hE]
      exact Finset.mem_image.mpr ⟨⟨p, hp⟩, by simpa using hne, rfl⟩)
  have hzeroAll := eq_zero_of_exponentialType_of_cofinite_primeLog_zeros
    (differentiable_cexpFn c P) hA hC hgrow E hzeroFn
  have hblocks := eq_zero_of_cexpFn_eq_zero q' c P hcinj (fun z => congrFun hzeroAll z)
  funext x
  have := jetBlock_eq_zero (hblocks x.1)
  have hx := congrFun this x.2
  simpa using hx

end GaloisForLFunctions.RHTower.PrimeShiftJet

namespace GaloisForLFunctions.RHTower.PrimeShiftJet

open Finset GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.CExpPoly
open GaloisForLFunctions.RHTower.PrimeCancellation

theorem dirichletShift_supportedOnPositivePrimePowers {F : ArithmeticFunction ℂ}
    (hF : SupportedOnPositivePrimePowers F) (a : ℂ) :
    SupportedOnPositivePrimePowers (dirichletShift a F) := by
  intro n hn
  refine hF (fun hzero => hn ?_)
  rw [dirichletShift_apply, hzero, mul_zero]

/-- **Complex-shift jet independence.**  Every finite family of arbitrary distinct complex
translates of a positive-prime-power source whose prime coefficients vanish only finitely often is
differentially algebraically independent over `ℂ`; equivalently, all their derivative jets are
algebraically independent. -/
theorem dirichletShiftFamily_differentialIndependent
    {q : ℕ} [Nonempty (Fin q)] (F : ArithmeticFunction ℂ)
    (hsupport : SupportedOnPositivePrimePowers F)
    (hzeros : {p : Nat.Primes | F ((p : ℕ)) = 0}.Finite)
    (h : Fin q → ℂ) (hdistinct : Function.Injective h) :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun j : Fin q => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (dirichletShift (h j) F)) := by
  classical
  unfold GaloisForLFunctions.DifferentialIndependent
  simp_rw [differentialJet_algebraMap_rotatedLogArithmeticJet]
  let x : Fin q → ℕ → arithmeticFunctionFractionField := fun j k =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (rotatedLogArithmeticJet k (dirichletShift (h j) F))
  apply algebraicIndependent_prod_nat_of_fin x
  intro m
  have hrect := commonLayerJetRectangle_algebraicIndependent
    (I := Fin q × Fin (m + 1))
    (fun i => dirichletShift (h i.1) F) (fun i => (i.2 : ℕ))
    (fun i => dirichletShift_supportedOnPositivePrimePowers hsupport (h i.1))
    (primeShiftJet_tailCoefficientIndependent F hzeros h hdistinct)
  have hmap := hrect.map'
    (f := IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
    (IsFractionRing.injective (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
  simpa only [Function.comp_apply, x] using! hmap

end GaloisForLFunctions.RHTower.PrimeShiftJet

namespace RHTower

open Complex Filter
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.PrimeShiftJet

local instance primeShiftJetUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance primeShiftJetUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance primeShiftJetUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- **Analytic complex-shift jet independence.**  The actual upper-end meromorphic carriers of the
complex translates of a positive-prime-power finite-abscissa source with cofinitely many nonzero
prime coefficients are differentially algebraically independent over the genuine rational
coordinate field. -/
theorem dirichletShiftFamily_upperEnd_differentialIndependent
    {q : ℕ} [Nonempty (Fin q)] (S : finiteAbscissaArithmeticSubalgebra)
    (hsupport : SupportedOnPositivePrimePowers S.1)
    (hzeros : {p : Nat.Primes | S.1 ((p : ℕ)) = 0}.Finite)
    (h : Fin q → ℂ) (hdistinct : Function.Injective h) :
    GaloisForLFunctions.DifferentialIndependent upperEndRationalCoordinateField
      (fun j : Fin q => upperEndTranslationMeroEquiv (Complex.I * h j)
        (finiteAbscissaLSeriesToUpperEndMero S)) := by
  classical
  have hcarrier : (fun j : Fin q => upperEndTranslationMeroEquiv (Complex.I * h j)
        (finiteAbscissaLSeriesToUpperEndMero S))
      = fun j : Fin q => finiteAbscissaLSeriesToUpperEndMero
        (finiteAbscissaDirichletShift (h j) S) := by
    funext j
    exact upperEndTranslationMeroEquiv_finiteAbscissaLSeries (h j) S
  rw [hcarrier]
  apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
  exact dirichletShiftFamily_differentialIndependent S.1 hsupport hzeros h hdistinct

/-- **Filtered xi source: complex translate independence.**  Every finite family of distinct
complex translates of the exposed `+2` xi shift defect is differentially algebraically independent
over the rational coordinate field. -/
theorem filteredVonMangoldt_translates_differentialIndependent
    {q : ℕ} [Nonempty (Fin q)] (h : Fin q → ℂ) (hdistinct : Function.Injective h) :
    GaloisForLFunctions.DifferentialIndependent upperEndRationalCoordinateField
      (fun j : Fin q => upperEndTranslationMeroEquiv (Complex.I * h j)
        filteredVonMangoldtUpperEndCarrier) := by
  refine dirichletShiftFamily_upperEnd_differentialIndependent
    filteredVonMangoldtFiniteAbscissaSource ?_ ?_ h hdistinct
  · exact filteredVonMangoldtArithmetic_supportedOnPositivePrimePowers
  · have hempty : {p : Nat.Primes | filteredVonMangoldtFiniteAbscissaSource.1 ((p : ℕ)) = 0}
        = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      simpa [filteredVonMangoldtFiniteAbscissaSource, filteredVonMangoldtArithmetic] using
        filteredVonMangoldtCoeff_prime_ne_zero p
    rw [hempty]
    exact Set.finite_empty

end

end RHTower
