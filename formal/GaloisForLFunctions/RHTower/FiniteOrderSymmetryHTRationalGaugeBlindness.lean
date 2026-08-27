import GaloisForLFunctions.RHTower.LiRemoteQuartetGaugedCarrier
import GaloisForLFunctions.RHTower.ImaginaryAxisPositiveRepair
import GaloisForLFunctions.RHTower.FiniteHermiteCRT
import GaloisForLFunctions.HTGeometry.FamilyInversionGauge
import GaloisForLFunctions.HTGeometry.PolynomialGaugeGrowth
import GaloisForLFunctions.HTGeometry.RationalFiniteAvoidance
import GaloisForLFunctions.HTGeometry.LocalPolynomialGauge

/-!
# Finite-order symmetry-caged hypertranscendental gauge blindness

An explicit real-even polynomial packet is translated to the critical-line centre and normalized
at a real point outside its finite root set.  The resulting nonzero polynomial gauge is flat to an
arbitrary prescribed finite order, obeys both scalar symmetries, and has an off-critical-line zero.
Multiplying the reflected-Gamma carrier by this gauge preserves exact order one,
hypertranscendence, and the literal all-translation/all-derivative field, while changing its divisor.
-/

open Complex Polynomial Set
open scoped Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Centred real-even packet carrying every requested local multiplicity.  Quartet closure makes
the construction work for an arbitrary finite set, hence in particular for every invariant one. -/
def finiteSymmetryFlatPacket (A : Finset ℂ) (nu : ℂ → ℕ) : Polynomial ℂ :=
  simultaneousFlatPolynomial (fun a : {z // z ∈ A} => nu a)
      (fun a : {z // z ∈ A} => a.1 - (1 / 2 : ℂ)) * X ^ 2

private theorem quartetFlatPolynomial_eval_neg (a z : ℂ) :
    (quartetFlatPolynomial a).eval (-z) = (quartetFlatPolynomial a).eval z := by
  simp [quartetFlatPolynomial]

private theorem quartetFlatPolynomial_eval_conj (a z : ℂ) :
    (quartetFlatPolynomial a).eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((quartetFlatPolynomial a).eval z) := by
  simp [quartetFlatPolynomial, map_mul, map_sub, map_pow]
  ring

private theorem simultaneousFlatPolynomial_eval_neg
    {iota : Type*} [Fintype iota] (M : iota → ℕ) (a : iota → ℂ) (z : ℂ) :
    (simultaneousFlatPolynomial M a).eval (-z) =
      (simultaneousFlatPolynomial M a).eval z := by
  simp only [simultaneousFlatPolynomial, Polynomial.eval_prod, Polynomial.eval_pow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [quartetFlatPolynomial_eval_neg]

private theorem simultaneousFlatPolynomial_eval_conj
    {iota : Type*} [Fintype iota] (M : iota → ℕ) (a : iota → ℂ) (z : ℂ) :
    (simultaneousFlatPolynomial M a).eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((simultaneousFlatPolynomial M a).eval z) := by
  simp only [simultaneousFlatPolynomial, Polynomial.eval_prod, Polynomial.eval_pow,
    map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [quartetFlatPolynomial_eval_conj]

theorem finiteSymmetryFlatPacket_monic (A : Finset ℂ) (nu : ℂ → ℕ) :
    (finiteSymmetryFlatPacket A nu).Monic := by
  exact (simultaneousFlatPolynomial_monic
    (fun a : {z // z ∈ A} => nu a)
    (fun a : {z // z ∈ A} => a.1 - (1 / 2 : ℂ))).mul (monic_X.pow 2)

theorem finiteSymmetryFlatPacket_eval_zero (A : Finset ℂ) (nu : ℂ → ℕ) :
    (finiteSymmetryFlatPacket A nu).eval 0 = 0 := by
  simp [finiteSymmetryFlatPacket]

theorem finiteSymmetryFlatPacket_eval_neg
    (A : Finset ℂ) (nu : ℂ → ℕ) (z : ℂ) :
    (finiteSymmetryFlatPacket A nu).eval (-z) =
      (finiteSymmetryFlatPacket A nu).eval z := by
  simp only [finiteSymmetryFlatPacket, eval_mul, eval_pow, eval_X]
  rw [simultaneousFlatPolynomial_eval_neg]
  ring

theorem finiteSymmetryFlatPacket_eval_conj
    (A : Finset ℂ) (nu : ℂ → ℕ) (z : ℂ) :
    (finiteSymmetryFlatPacket A nu).eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((finiteSymmetryFlatPacket A nu).eval z) := by
  simp only [finiteSymmetryFlatPacket, eval_mul, eval_pow, eval_X, map_mul, map_pow]
  rw [simultaneousFlatPolynomial_eval_conj]

private theorem X_sub_C_dvd_quartetFlatPolynomial (a : ℂ) :
    X - C a ∣ quartetFlatPolynomial a := by
  rw [Polynomial.dvd_iff_isRoot]
  simp [Polynomial.IsRoot, quartetFlatPolynomial]

theorem finiteSymmetryFlatPacket_local_dvd
    (A : Finset ℂ) (nu : ℂ → ℕ) {a : ℂ} (ha : a ∈ A) :
    (X - C (a - (1 / 2 : ℂ))) ^ nu a ∣ finiteSymmetryFlatPacket A nu := by
  let i : {z // z ∈ A} := ⟨a, ha⟩
  have hlinear : X - C (a - (1 / 2 : ℂ)) ∣
      quartetFlatPolynomial (a - (1 / 2 : ℂ)) :=
    X_sub_C_dvd_quartetFlatPolynomial _
  have hpacket := quartetFlatPolynomial_pow_dvd_simultaneousFlatPolynomial
    (fun b : {z // z ∈ A} => nu b)
    (fun b : {z // z ∈ A} => b.1 - (1 / 2 : ℂ)) i
  obtain ⟨Q, hQ⟩ := hpacket
  obtain ⟨R, hR⟩ := hlinear
  refine ⟨R ^ nu a * Q * X ^ 2, ?_⟩
  rw [finiteSymmetryFlatPacket, hQ, hR, mul_pow]
  ring

/-- A real normalization point can be chosen in `(1,2)` outside the packet's finite root set. -/
theorem exists_finiteSymmetryFlatPacket_real_nonzero
    (A : Finset ℂ) (nu : ℂ → ℕ) :
    ∃ x : ℝ, x ∈ Set.Ioo (1 : ℝ) 2 ∧
      (finiteSymmetryFlatPacket A nu).eval (x : ℂ) ≠ 0 := by
  let B := finiteSymmetryFlatPacket A nu
  obtain ⟨x, hx, hxavoid, q, hq⟩ :=
    exists_ratCast_mem_Ioo_not_mem_finset (by norm_num : (1 : ℝ) < 2)
      (B.roots.map Complex.re).toFinset
  refine ⟨x, hx, ?_⟩
  have hB : B ≠ 0 := (finiteSymmetryFlatPacket_monic A nu).ne_zero
  have hxroots : (x : ℂ) ∉ B.roots.toFinset := by
    intro hroot
    apply hxavoid
    rw [Multiset.mem_toFinset, Multiset.mem_map]
    exact ⟨(x : ℂ), Multiset.mem_toFinset.mp hroot, by simp⟩
  exact Bottcher.eval_ne_zero_of_notMem_roots hB hxroots

/-- Critical-line-centred normalized gauge associated with a non-root real displacement. -/
def finiteSymmetryGauge
    (A : Finset ℂ) (nu : ℂ → ℕ) (x : ℝ) : Polynomial ℂ :=
  1 - C (((finiteSymmetryFlatPacket A nu).eval (x : ℂ))⁻¹) *
    (finiteSymmetryFlatPacket A nu).comp (X - C (1 / 2 : ℂ))

def finiteSymmetryOffLinePoint (x : ℝ) : ℂ := (x : ℂ) + 1 / 2

theorem finiteSymmetryGauge_eval_half
    (A : Finset ℂ) (nu : ℂ → ℕ) (x : ℝ) :
    (finiteSymmetryGauge A nu x).eval (1 / 2 : ℂ) = 1 := by
  simp [finiteSymmetryGauge, finiteSymmetryFlatPacket_eval_zero]

theorem finiteSymmetryGauge_ne_zero
    (A : Finset ℂ) (nu : ℂ → ℕ) (x : ℝ) :
    finiteSymmetryGauge A nu x ≠ 0 := by
  intro hzero
  have h := finiteSymmetryGauge_eval_half A nu x
  rw [hzero] at h
  simp at h

theorem finiteSymmetryGauge_offLineZero
    (A : Finset ℂ) (nu : ℂ → ℕ) {x : ℝ}
    (hx : (finiteSymmetryFlatPacket A nu).eval (x : ℂ) ≠ 0) :
    (finiteSymmetryGauge A nu x).eval (finiteSymmetryOffLinePoint x) = 0 := by
  simp only [finiteSymmetryGauge, finiteSymmetryOffLinePoint, eval_sub, eval_one,
    eval_mul, eval_C, Polynomial.eval_comp, eval_X]
  rw [show (x : ℂ) + 1 / 2 - 1 / 2 = (x : ℂ) by ring]
  field_simp
  ring

theorem finiteSymmetryOffLinePoint_re_ne_half {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    (finiteSymmetryOffLinePoint x).re ≠ 1 / 2 := by
  simp only [finiteSymmetryOffLinePoint, Complex.add_re, ofReal_re]
  norm_num
  nlinarith [hx.1]

theorem finiteSymmetryFlatPacket_eval_real
    (A : Finset ℂ) (nu : ℂ → ℕ) (x : ℝ) :
    (starRingEnd ℂ) ((finiteSymmetryFlatPacket A nu).eval (x : ℂ)) =
      (finiteSymmetryFlatPacket A nu).eval (x : ℂ) := by
  rw [← finiteSymmetryFlatPacket_eval_conj]
  simp

theorem finiteSymmetryGauge_eval_one_sub
    (A : Finset ℂ) (nu : ℂ → ℕ) (x : ℝ) (s : ℂ) :
    (finiteSymmetryGauge A nu x).eval (1 - s) =
      (finiteSymmetryGauge A nu x).eval s := by
  simp only [finiteSymmetryGauge, eval_sub, eval_one, eval_mul, eval_C,
    Polynomial.eval_comp, eval_X]
  rw [show 1 - s - 1 / 2 = -(s - 1 / 2) by ring,
    finiteSymmetryFlatPacket_eval_neg]

theorem finiteSymmetryGauge_eval_conj
    (A : Finset ℂ) (nu : ℂ → ℕ) (x : ℝ) (s : ℂ) :
    (finiteSymmetryGauge A nu x).eval ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) ((finiteSymmetryGauge A nu x).eval s) := by
  simp only [finiteSymmetryGauge, eval_sub, eval_one, eval_mul, eval_C,
    Polynomial.eval_comp, eval_X, map_sub, map_one, map_mul, map_inv₀]
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    apply Complex.ext <;> norm_num
  rw [show (starRingEnd ℂ) s - 1 / 2 =
      (starRingEnd ℂ) (s - 1 / 2) by
        rw [map_sub, hhalf],
    finiteSymmetryFlatPacket_eval_conj,
    finiteSymmetryFlatPacket_eval_real]

theorem finiteSymmetryFlatPacket_iterateDerivative_eval_eq_zero
    (A : Finset ℂ) (nu : ℂ → ℕ) {a : ℂ} (ha : a ∈ A)
    {j : ℕ} (hj : j < nu a) :
    (derivative^[j] (finiteSymmetryFlatPacket A nu)).eval
        (a - (1 / 2 : ℂ)) = 0 := by
  have hdvd := finiteSymmetryFlatPacket_local_dvd A nu ha
  simpa using eval_iterate_derivative_eq_of_power_linear_dvd_sub
    (T := 0) (by simpa using hdvd) hj

theorem finiteSymmetryGauge_iterateDerivative_eval_eq_one
    (A : Finset ℂ) (nu : ℂ → ℕ) (x : ℝ)
    {a : ℂ} (ha : a ∈ A) {j : ℕ} (hj : j < nu a) :
    (derivative^[j] (finiteSymmetryGauge A nu x)).eval a =
      (derivative^[j] (1 : Polynomial ℂ)).eval a := by
  rw [finiteSymmetryGauge, iterate_derivative_sub, iterate_derivative_C_mul,
    iterate_derivative_comp_sub]
  simp only [eval_sub, eval_mul, eval_C, Polynomial.eval_comp, eval_X]
  rw [finiteSymmetryFlatPacket_iterateDerivative_eval_eq_zero A nu ha hj]
  simp

/-! ## The gauged reflected-Gamma carrier -/

def polynomialGaugedLiCarrier (alpha : ℝ) (P : Polynomial ℂ) (s : ℂ) : ℂ :=
  P.eval s * liReflectedGammaCarrier alpha s

theorem polynomialGaugedLiCarrier_analyticOnNhd (alpha : ℝ) (P : Polynomial ℂ) :
    AnalyticOnNhd ℂ (polynomialGaugedLiCarrier alpha P) Set.univ := by
  exact (P.differentiable.differentiableOn.analyticOnNhd isOpen_univ).mul
    (liReflectedGammaCarrier_analyticOnNhd alpha)

theorem polynomialGaugedLiCarrier_one_sub
    (alpha : ℝ) (P : Polynomial ℂ)
    (hP : ∀ s : ℂ, P.eval (1 - s) = P.eval s) (s : ℂ) :
    polynomialGaugedLiCarrier alpha P (1 - s) =
      polynomialGaugedLiCarrier alpha P s := by
  rw [polynomialGaugedLiCarrier, polynomialGaugedLiCarrier, hP,
    liReflectedGammaCarrier_one_sub]

theorem polynomialGaugedLiCarrier_conj
    (alpha : ℝ) (P : Polynomial ℂ)
    (hP : ∀ s : ℂ, P.eval ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (P.eval s)) (s : ℂ) :
    polynomialGaugedLiCarrier alpha P ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (polynomialGaugedLiCarrier alpha P s) := by
  rw [polynomialGaugedLiCarrier, polynomialGaugedLiCarrier, hP,
    liReflectedGammaCarrier_conj, map_mul]

theorem polynomialGaugedLiCarrier_hypertranscendental
    {alpha : ℝ} {P : Polynomial ℂ} (hP : P ≠ 0)
    (hsep : ∀ k : ℤ, (2 * alpha : ℂ) ≠ (k : ℂ)) :
    Hypertranscendental (polynomialGaugedLiCarrier alpha P) := by
  exact hypertranscendental_mul_polynomial
    (liReflectedGammaCarrier_analyticOnNhd alpha).contDiff hP
    (liReflectedGammaCarrier_hypertranscendental hsep)

theorem polynomialGaugedLiCarrier_hypertranscendental_of_two_mul_sub_one
    {alpha : ℝ} {P : Polynomial ℂ} (hP : P ≠ 0)
    (hsep : ∀ k : ℤ, (2 * alpha - 1 : ℂ) ≠ (k : ℂ)) :
    Hypertranscendental (polynomialGaugedLiCarrier alpha P) := by
  apply polynomialGaugedLiCarrier_hypertranscendental hP
  intro k hk
  apply hsep (k - 1)
  push_cast
  linear_combination hk

theorem polynomialGaugedLiCarrier_orderOneEnvelope
    (alpha : ℝ) (P : Polynomial ℂ) :
    OrderOneEnvelope (polynomialGaugedLiCarrier alpha P) := by
  exact (orderOneEnvelope_polyEval P).mul
    (liReflectedGammaCarrier_orderOneEnvelope alpha)

theorem polynomialGaugedLiCarrier_hasExactEntireOrderOne
    {alpha : ℝ} (halpha : 0 < alpha) {P : Polynomial ℂ}
    (hPhalf : P.eval (1 / 2 : ℂ) = 1) :
    HasExactEntireOrderOne (polynomialGaugedLiCarrier alpha P) := by
  refine ⟨Complex.analyticOnNhd_univ_iff_differentiable.mp
      (polynomialGaugedLiCarrier_analyticOnNhd alpha P),
    polynomialGaugedLiCarrier_orderOneEnvelope alpha P, ?_⟩
  intro hmin
  have hhalf : polynomialGaugedLiCarrier alpha P (1 / 2 : ℂ) ≠ 0 := by
    rw [polynomialGaugedLiCarrier, hPhalf, one_mul]
    exact liReflectedGammaCarrier_ne_zero_half halpha
  have hzeros : ∀ n : ℕ, polynomialGaugedLiCarrier alpha P
      ((1 / 2 : ℂ) + I * (alpha : ℂ) + n • I) = 0 := by
    intro n
    rw [polynomialGaugedLiCarrier,
      liReflectedGammaCarrier_zero_arithmeticProgression, mul_zero]
  exact hmin.no_arithmeticProgression_zeros hhalf I_ne_zero hzeros

theorem polynomialGaugedLiCarrier_iteratedDeriv_eq
    (alpha : ℝ) (P : Polynomial ℂ) {a : ℂ} {m : ℕ}
    (hP : ∀ j < m, (derivative^[j] P).eval a =
      (derivative^[j] (1 : Polynomial ℂ)).eval a) {j : ℕ} (hj : j < m) :
    iteratedDeriv j (polynomialGaugedLiCarrier alpha P) a =
      iteratedDeriv j (liReflectedGammaCarrier alpha) a := by
  change iteratedDeriv j
    (fun s => P.eval s * liReflectedGammaCarrier alpha s) a = _
  rw [iteratedDeriv_mul_polynomial_at
    (liReflectedGammaCarrier_analyticOnNhd alpha).contDiff.contDiffAt P j]
  calc
    ∑ i ∈ Finset.range (j + 1),
        ((j.choose i : ℕ) : ℂ) * (derivative^[i] P).eval a *
          iteratedDeriv (j - i) (liReflectedGammaCarrier alpha) a =
        ((j.choose 0 : ℕ) : ℂ) * (derivative^[0] P).eval a *
          iteratedDeriv (j - 0) (liReflectedGammaCarrier alpha) a := by
      apply Finset.sum_eq_single 0
      · intro i hi hi0
        have hi' : i < m := lt_of_le_of_lt
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hj
        rw [hP i hi']
        cases i with
        | zero => exact (hi0 rfl).elim
        | succ i => simp [Function.iterate_succ_apply]
      · simp
    _ = iteratedDeriv j (liReflectedGammaCarrier alpha) a := by
      rw [hP 0 (by omega)]
      simp

theorem finiteSymmetryGaugedLiCarrier_iteratedDeriv_eq
    (A : Finset ℂ) (nu : ℂ → ℕ) (alpha : ℝ) (x : ℝ)
    {a : ℂ} (ha : a ∈ A) {j : ℕ} (hj : j < nu a) :
    iteratedDeriv j
        (polynomialGaugedLiCarrier alpha (finiteSymmetryGauge A nu x)) a =
      iteratedDeriv j (liReflectedGammaCarrier alpha) a := by
  exact polynomialGaugedLiCarrier_iteratedDeriv_eq alpha _
    (fun k hk => finiteSymmetryGauge_iterateDerivative_eval_eq_one A nu x ha hk) hj

/-! ## Literal complete translated differential-field equality -/

open scoped UpperEndDifferentialInstances

def polynomialGaugeRatFunc (P : Polynomial ℂ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) P

theorem polynomialGaugeRatFunc_ne_zero {P : Polynomial ℂ} (hP : P ≠ 0) :
    polynomialGaugeRatFunc P ≠ 0 := by
  unfold polynomialGaugeRatFunc
  simpa only [map_zero] using (RatFunc.algebraMap_injective ℂ).ne hP

def polynomialGaugedLiCarrierUpperEndMero
    (alpha : ℝ) (P : Polynomial ℂ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact upperEndRatfuncToMero (polynomialGaugeRatFunc P) *
    liReflectedGammaCarrierUpperEndMero alpha

def polynomialGaugedLiCarrierAnalyticUpperEndMero
    (alpha : ℝ) (P : Polynomial ℂ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact analyticUpperEndMero (polynomialGaugedLiCarrier alpha P) 0
    ((polynomialGaugedLiCarrier_analyticOnNhd alpha P).mono (Set.subset_univ _))

theorem polynomialGaugedLiCarrierUpperEndMero_eq_analytic
    (alpha : ℝ) (P : Polynomial ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    polynomialGaugedLiCarrierUpperEndMero alpha P =
      polynomialGaugedLiCarrierAnalyticUpperEndMero alpha P := by
  letI := isDomain_upperEndAnalyticSubring
  rw [polynomialGaugedLiCarrierUpperEndMero, polynomialGaugeRatFunc,
    upperEndRatfuncToMero_algebraMap_polynomial,
    liReflectedGammaCarrierUpperEndMero,
    polynomialGaugedLiCarrierAnalyticUpperEndMero,
    upperEndPolyToMero, analyticUpperEndMero, analyticUpperEndMero]
  change algebraMap upperEndAnalyticSubring upperEndMeroField
      (upperEndPolyToAnalytic P) *
    algebraMap upperEndAnalyticSubring upperEndMeroField
      (analyticUpperEndElement (liReflectedGammaCarrier alpha) 0 _) =
    algebraMap upperEndAnalyticSubring upperEndMeroField
      (analyticUpperEndElement (polynomialGaugedLiCarrier alpha P) 0 _)
  rw [← map_mul]
  congr 1

def polynomialGaugedLiCarrierTranslateFamily
    (alpha : ℝ) (P : Polynomial ℂ) (h : ℂ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact upperEndRatfuncToMero
      (ratFuncTranslationEquiv h (polynomialGaugeRatFunc P)) *
    liReflectedGammaCarrierTranslateFamily alpha h

theorem polynomialGaugedLiCarrierTranslateFamily_eq_translation
    (alpha : ℝ) (P : Polynomial ℂ) (h : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    polynomialGaugedLiCarrierTranslateFamily alpha P h =
      upperEndTranslationMeroEquiv h
        (polynomialGaugedLiCarrierUpperEndMero alpha P) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [polynomialGaugedLiCarrierTranslateFamily,
    liReflectedGammaCarrierTranslateFamily,
    polynomialGaugedLiCarrierUpperEndMero,
    map_mul, upperEndTranslationMeroEquiv_ratfuncToMero]

theorem polynomialGaugedLiCarrierTranslateFamily_differentialAdjoin_eq
    (alpha : ℝ) {P : Polynomial ℂ} (hP : P ≠ 0) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    differentialAdjoin (RatFunc ℂ)
        (Set.range (polynomialGaugedLiCarrierTranslateFamily alpha P)) =
      differentialAdjoin (RatFunc ℂ)
        (Set.range (liReflectedGammaCarrierTranslateFamily alpha)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  apply differentialAdjoin_gauge_eq
    (liReflectedGammaCarrierTranslateFamily alpha)
    (fun h => ratFuncTranslationEquiv h (polynomialGaugeRatFunc P))
  intro h
  simpa only [map_zero] using (ratFuncTranslationEquiv h).injective.ne
    (polynomialGaugeRatFunc_ne_zero hP)

/-- Literal equality after adjoining every derivative of every complex translate. -/
theorem polynomialGaugedLiCarrierTranslateFamily_allJets_adjoin_eq
    (alpha : ℝ) {P : Polynomial ℂ} (hP : P ≠ 0) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    IntermediateField.adjoin (RatFunc ℂ)
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (polynomialGaugedLiCarrierTranslateFamily alpha P p.1)) =
      IntermediateField.adjoin (RatFunc ℂ)
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (liReflectedGammaCarrierTranslateFamily alpha p.1)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  rw [← differentialAdjoin_range_eq_adjoin_jetRange
      (RatFunc ℂ) (polynomialGaugedLiCarrierTranslateFamily alpha P),
    ← differentialAdjoin_range_eq_adjoin_jetRange
      (RatFunc ℂ) (liReflectedGammaCarrierTranslateFamily alpha)]
  exact polynomialGaugedLiCarrierTranslateFamily_differentialAdjoin_eq alpha hP

/-! ## Exact coarse growth and divisor cost -/

theorem polynomialGaugedLiCarrier_characteristicLogEquivalent
    {alpha : ℝ} (halpha : 0 < alpha) {P : Polynomial ℂ}
    (hPhalf : P.eval (1 / 2 : ℂ) = 1) :
    CharacteristicLogEquivalent (polynomialGaugedLiCarrier alpha P)
      (liReflectedGammaCarrier alpha) := by
  apply characteristicLogEquivalent_mul_polynomial
    (liReflectedGammaCarrier_analyticOnNhd alpha)
    ⟨1 / 2, liReflectedGammaCarrier_ne_zero_half halpha⟩ P
  exact ⟨1 / 2, by rw [hPhalf]; norm_num⟩

theorem polynomialGaugedLiCarrier_zeroCount_eq
    {alpha : ℝ} (halpha : 0 < alpha) {P : Polynomial ℂ}
    (hPhalf : P.eval (1 / 2 : ℂ) = 1) (c : ℂ) (R : ℝ) :
    zeroCount (polynomialGaugedLiCarrier alpha P) c R =
      zeroCount (liReflectedGammaCarrier alpha) c R +
        zeroCount (fun z => P.eval z) c R := by
  let p : ℂ → ℂ := fun z => P.eval z
  let f : ℂ → ℂ := liReflectedGammaCarrier alpha
  have hpAn : AnalyticOnNhd ℂ p Set.univ :=
    P.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hfAn : AnalyticOnNhd ℂ f Set.univ :=
    liReflectedGammaCarrier_analyticOnNhd alpha
  have hpDiff : Differentiable ℂ p := P.differentiable
  have hfDiff : Differentiable ℂ f :=
    Complex.analyticOnNhd_univ_iff_differentiable.mp hfAn
  have hpWitness : ∃ z, p z ≠ 0 := by
    refine ⟨1 / 2, ?_⟩
    change P.eval (1 / 2 : ℂ) ≠ 0
    rw [hPhalf]
    norm_num
  have hfWitness : ∃ z, f z ≠ 0 :=
    ⟨1 / 2, liReflectedGammaCarrier_ne_zero_half halpha⟩
  obtain ⟨zp, hzp⟩ := hpWitness
  obtain ⟨zf, hzf⟩ := hfWitness
  have hpOrder : ∀ z, meromorphicOrderAt p z ≠ ⊤ := by
    intro z
    rw [(hpAn z (Set.mem_univ z)).meromorphicOrderAt_eq]
    have hz := analyticOrderAt_ne_top_of_entire hpDiff hzp z
    simp [hz]
  have hfOrder : ∀ z, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    rw [(hfAn z (Set.mem_univ z)).meromorphicOrderAt_eq]
    have hz := analyticOrderAt_ne_top_of_entire hfDiff hzf z
    simp [hz]
  change zeroCount (p * f) c R = zeroCount f c R + zeroCount p c R
  rw [zeroCount_mul_eq_add hpAn hfAn hpOrder hfOrder c R]
  exact add_comm _ _

theorem polynomialGauge_zeroCount_le_natDegree
    {P : Polynomial ℂ} (hPhalf : P.eval (1 / 2 : ℂ) = 1)
    (c : ℂ) (R : ℝ) :
    zeroCount (fun z => P.eval z) c R ≤ P.natDegree := by
  exact zeroCount_polynomial_le_natDegree P
    (fun hP => by rw [hP] at hPhalf; simp at hPhalf) c R

/-! ## Dependency-closed card package -/

/-- Equality of the literal fields generated over `ℂ(s)` by all complex translates and all
derivatives of the carrier and its polynomial gauge. -/
def CompleteTranslatedJetFieldsEqual (alpha : ℝ) (P : Polynomial ℂ) : Prop :=
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI : Differential upperEndMeroField := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  IntermediateField.adjoin (RatFunc ℂ)
      (Set.range fun p : ℂ × ℕ => differentialJet p.2
        (polynomialGaugedLiCarrierTranslateFamily alpha P p.1)) =
    IntermediateField.adjoin (RatFunc ℂ)
      (Set.range fun p : ℂ × ℕ => differentialJet p.2
        (liReflectedGammaCarrierTranslateFamily alpha p.1))

theorem completeTranslatedJetFieldsEqual_of_ne_zero
    (alpha : ℝ) {P : Polynomial ℂ} (hP : P ≠ 0) :
    CompleteTranslatedJetFieldsEqual alpha P := by
  unfold CompleteTranslatedJetFieldsEqual
  exact polynomialGaugedLiCarrierTranslateFamily_allJets_adjoin_eq alpha hP

/-- Complete theorem payload: exact-order entire HT pair, both scalar symmetries, arbitrary finite
passport, opposite divisor locations, literal complete-field equality, logarithmic characteristic
equivalence, and a uniform exact zero-count correction bounded by polynomial degree. -/
structure FiniteOrderSymmetryHTRationalGaugePackage
    (A : Finset ℂ) (nu : ℂ → ℕ) (alpha : ℝ) where
  gauge : Polynomial ℂ
  offLinePoint : ℂ
  gauge_ne_zero : gauge ≠ 0
  gauge_half : gauge.eval (1 / 2 : ℂ) = 1
  gauge_one_sub : ∀ s : ℂ, gauge.eval (1 - s) = gauge.eval s
  gauge_conj : ∀ s : ℂ, gauge.eval ((starRingEnd ℂ) s) =
    (starRingEnd ℂ) (gauge.eval s)
  gauge_flat : ∀ a ∈ A, ∀ j < nu a,
    (derivative^[j] gauge).eval a =
      (derivative^[j] (1 : Polynomial ℂ)).eval a
  offLinePoint_not_critical : offLinePoint.re ≠ 1 / 2
  gauge_offLine_zero : gauge.eval offLinePoint = 0
  critical_exact_order_one : HasExactEntireOrderOne (liReflectedGammaCarrier alpha)
  off_exact_order_one : HasExactEntireOrderOne (polynomialGaugedLiCarrier alpha gauge)
  critical_hypertranscendental : Hypertranscendental (liReflectedGammaCarrier alpha)
  off_hypertranscendental : Hypertranscendental (polynomialGaugedLiCarrier alpha gauge)
  critical_one_sub : ∀ s : ℂ,
    liReflectedGammaCarrier alpha (1 - s) = liReflectedGammaCarrier alpha s
  off_one_sub : ∀ s : ℂ,
    polynomialGaugedLiCarrier alpha gauge (1 - s) =
      polynomialGaugedLiCarrier alpha gauge s
  critical_conj : ∀ s : ℂ,
    liReflectedGammaCarrier alpha ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (liReflectedGammaCarrier alpha s)
  off_conj : ∀ s : ℂ,
    polynomialGaugedLiCarrier alpha gauge ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (polynomialGaugedLiCarrier alpha gauge s)
  passport_agreement : ∀ a ∈ A, ∀ j < nu a,
    iteratedDeriv j (polynomialGaugedLiCarrier alpha gauge) a =
      iteratedDeriv j (liReflectedGammaCarrier alpha) a
  critical_zero_re : ∀ s : ℂ, liReflectedGammaCarrier alpha s = 0 →
    s.re = 1 / 2
  off_has_offLine_zero : polynomialGaugedLiCarrier alpha gauge offLinePoint = 0
  complete_translated_jet_fields_equal : CompleteTranslatedJetFieldsEqual alpha gauge
  characteristic_log_equivalent :
    CharacteristicLogEquivalent (polynomialGaugedLiCarrier alpha gauge)
      (liReflectedGammaCarrier alpha)
  zeroCount_exact : ∀ c : ℂ, ∀ R : ℝ,
    zeroCount (polynomialGaugedLiCarrier alpha gauge) c R =
      zeroCount (liReflectedGammaCarrier alpha) c R +
        zeroCount (fun z => gauge.eval z) c R
  zeroCount_excess_le : ∀ c : ℂ, ∀ R : ℝ,
    zeroCount (fun z => gauge.eval z) c R ≤ gauge.natDegree

theorem two_mul_ne_integer_of_two_mul_sub_one_ne_integer
    {alpha : ℝ}
    (hsep : ∀ k : ℤ, (2 * alpha - 1 : ℂ) ≠ (k : ℂ)) :
    ∀ k : ℤ, (2 * alpha : ℂ) ≠ (k : ℂ) := by
  intro k hk
  apply hsep (k - 1)
  push_cast
  linear_combination hk

/-- Parameter form matching the paper theorem.  No invariance hypothesis on the finite passport is
needed: the construction closes every requested point under both symmetries internally. -/
theorem exists_finiteOrderSymmetryHTRationalGaugePackage
    (A : Finset ℂ) (nu : ℂ → ℕ) (alpha : ℝ)
    (halpha : 0 < alpha)
    (hsep : ∀ k : ℤ, (2 * alpha - 1 : ℂ) ≠ (k : ℂ)) :
    Nonempty (FiniteOrderSymmetryHTRationalGaugePackage A nu alpha) := by
  obtain ⟨x, hx, hxB⟩ := exists_finiteSymmetryFlatPacket_real_nonzero A nu
  let P := finiteSymmetryGauge A nu x
  let rho := finiteSymmetryOffLinePoint x
  have hP : P ≠ 0 := finiteSymmetryGauge_ne_zero A nu x
  have hPhalf : P.eval (1 / 2 : ℂ) = 1 := finiteSymmetryGauge_eval_half A nu x
  have hsep' := two_mul_ne_integer_of_two_mul_sub_one_ne_integer hsep
  refine ⟨{
    gauge := P
    offLinePoint := rho
    gauge_ne_zero := hP
    gauge_half := hPhalf
    gauge_one_sub := finiteSymmetryGauge_eval_one_sub A nu x
    gauge_conj := finiteSymmetryGauge_eval_conj A nu x
    gauge_flat := ?_
    offLinePoint_not_critical := finiteSymmetryOffLinePoint_re_ne_half hx
    gauge_offLine_zero := finiteSymmetryGauge_offLineZero A nu hxB
    critical_exact_order_one := liReflectedGammaCarrier_hasExactEntireOrderOne halpha
    off_exact_order_one := polynomialGaugedLiCarrier_hasExactEntireOrderOne halpha hPhalf
    critical_hypertranscendental := liReflectedGammaCarrier_hypertranscendental hsep'
    off_hypertranscendental :=
      polynomialGaugedLiCarrier_hypertranscendental_of_two_mul_sub_one hP hsep
    critical_one_sub := liReflectedGammaCarrier_one_sub alpha
    off_one_sub := polynomialGaugedLiCarrier_one_sub alpha P
      (finiteSymmetryGauge_eval_one_sub A nu x)
    critical_conj := liReflectedGammaCarrier_conj alpha
    off_conj := polynomialGaugedLiCarrier_conj alpha P
      (finiteSymmetryGauge_eval_conj A nu x)
    passport_agreement := ?_
    critical_zero_re := fun s hs => liReflectedGammaCarrier_zero_re_eq_half hs
    off_has_offLine_zero := ?_
    complete_translated_jet_fields_equal :=
      completeTranslatedJetFieldsEqual_of_ne_zero alpha hP
    characteristic_log_equivalent :=
      polynomialGaugedLiCarrier_characteristicLogEquivalent halpha hPhalf
    zeroCount_exact := polynomialGaugedLiCarrier_zeroCount_eq halpha hPhalf
    zeroCount_excess_le := polynomialGauge_zeroCount_le_natDegree hPhalf
  }⟩
  · intro a ha j hj
    exact finiteSymmetryGauge_iterateDerivative_eval_eq_one A nu x ha hj
  · intro a ha j hj
    exact finiteSymmetryGaugedLiCarrier_iteratedDeriv_eq A nu alpha x ha hj
  · rw [polynomialGaugedLiCarrier, finiteSymmetryGauge_offLineZero A nu hxB,
      zero_mul]

/-- Closed unconditional capstone.  `alpha = 1/4` is positive and nonresonant, so every arbitrary
finite complex passport has a witness pair satisfying the complete card, with no hypotheses. -/
theorem finiteOrderSymmetryHTRationalGaugeBlindness_unconditional :
    ∀ (A : Finset ℂ) (nu : ℂ → ℕ),
      Nonempty (FiniteOrderSymmetryHTRationalGaugePackage A nu (1 / 4 : ℝ)) := by
  intro A nu
  apply exists_finiteOrderSymmetryHTRationalGaugePackage A nu (1 / 4 : ℝ)
  · norm_num
  · intro k hk
    have hcomplex : (-1 : ℂ) = 2 * (k : ℂ) := by
      norm_num at hk ⊢
      linear_combination 2 * hk
    have hinteger : (-1 : ℤ) = 2 * k := by
      exact_mod_cast hcomplex
    omega

end

end RHTower
