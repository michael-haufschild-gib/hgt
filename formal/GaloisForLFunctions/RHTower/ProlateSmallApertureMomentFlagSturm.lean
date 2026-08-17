import GaloisForLFunctions.RHTower.ProlateSmallApertureEvenFullIndex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory intervalIntegral Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open _root_.RHTower

def complexProlateSLAction (c : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (((1 - x ^ 2 : ℝ) : ℂ) * deriv (deriv f) x) -
    (((2 * x : ℝ) : ℂ) * deriv f x) -
      (((c ^ 2 * x ^ 2 : ℝ) : ℂ) * f x)

theorem hasDerivAt_complexBandFlux {f : ℝ → ℂ} {t : ℝ}
    (hf2 : DifferentiableAt ℝ (deriv f) t) :
    HasDerivAt (fun y => ((1 - y ^ 2 : ℝ) : ℂ) * deriv f y)
      (((-(2 * t) : ℝ) : ℂ) * deriv f t +
        (((1 - t ^ 2 : ℝ) : ℂ) * deriv (deriv f) t)) t := by
  have hpoly : HasDerivAt (fun y : ℝ => ((1 - y ^ 2 : ℝ) : ℂ))
      (((-(2 * t) : ℝ) : ℂ)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_sub 1).ofReal_comp
  exact hpoly.mul hf2.hasDerivAt

theorem complex_band_flux_integral_by_parts {f g : ℝ → ℂ}
    (hf2 : Differentiable ℝ (deriv f)) (hf2c : Continuous (deriv (deriv f)))
    (hg1 : Differentiable ℝ g) (hg'c : Continuous (deriv g)) :
    ∫ y in (-1 : ℝ)..1, g y *
        ((((-(2 * y) : ℝ) : ℂ) * deriv f y) +
          (((1 - y ^ 2 : ℝ) : ℂ) * deriv (deriv f) y))
      = -∫ y in (-1 : ℝ)..1,
          deriv g y * (((1 - y ^ 2 : ℝ) : ℂ) * deriv f y) := by
  have hu : ∀ y ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g (deriv g y) y :=
    fun y _ => (hg1 y).hasDerivAt
  have hv : ∀ y ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun t => ((1 - t ^ 2 : ℝ) : ℂ) * deriv f t)
        ((((-(2 * y) : ℝ) : ℂ) * deriv f y) +
          (((1 - y ^ 2 : ℝ) : ℂ) * deriv (deriv f) y)) y :=
    fun y _ => hasDerivAt_complexBandFlux (hf2 y)
  have hu' : IntervalIntegrable (deriv g) volume (-1) 1 := hg'c.intervalIntegrable _ _
  have hv' : IntervalIntegrable
      (fun y => (((-(2 * y) : ℝ) : ℂ) * deriv f y) +
        (((1 - y ^ 2 : ℝ) : ℂ) * deriv (deriv f) y)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    have hcoef1 : Continuous (fun y : ℝ => (((-(2 * y) : ℝ) : ℂ))) := by fun_prop
    have hcoef2 : Continuous (fun y : ℝ => (((1 - y ^ 2 : ℝ) : ℂ))) := by fun_prop
    exact (hcoef1.mul hf2.continuous).add (hcoef2.mul hf2c)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [h]
  norm_num

theorem complexProlateSLAction_band_bilinear_symmetric {f g : ℝ → ℂ}
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hf2c : Continuous (deriv (deriv f)))
    (hg1 : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (hg2c : Continuous (deriv (deriv g))) (c : ℝ) :
    ∫ y in (-1 : ℝ)..1, g y * complexProlateSLAction c f y
      = ∫ y in (-1 : ℝ)..1, f y * complexProlateSLAction c g y := by
  have hfc : Continuous f := hf1.continuous
  have hgc : Continuous g := hg1.continuous
  have hf'c : Continuous (deriv f) := hf2.continuous
  have hg'c : Continuous (deriv g) := hg2.continuous
  have hAf : IntervalIntegrable
      (fun y => g y * ((((-(2 * y) : ℝ) : ℂ) * deriv f y) +
        (((1 - y ^ 2 : ℝ) : ℂ) * deriv (deriv f) y))) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hBf : IntervalIntegrable
      (fun y => g y * (((c ^ 2 * y ^ 2 : ℝ) : ℂ) * f y)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hAg : IntervalIntegrable
      (fun y => f y * ((((-(2 * y) : ℝ) : ℂ) * deriv g y) +
        (((1 - y ^ 2 : ℝ) : ℂ) * deriv (deriv g) y))) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hBg : IntervalIntegrable
      (fun y => f y * (((c ^ 2 * y ^ 2 : ℝ) : ℂ) * g y)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsplitf : ∫ y in (-1 : ℝ)..1, g y * complexProlateSLAction c f y =
      (∫ y in (-1 : ℝ)..1, g y * ((((-(2 * y) : ℝ) : ℂ) * deriv f y) +
        (((1 - y ^ 2 : ℝ) : ℂ) * deriv (deriv f) y))) -
      ∫ y in (-1 : ℝ)..1, g y * (((c ^ 2 * y ^ 2 : ℝ) : ℂ) * f y) := by
    rw [← intervalIntegral.integral_sub hAf hBf]
    exact intervalIntegral.integral_congr fun y _ => by
      simp only [complexProlateSLAction]
      push_cast
      ring
  have hsplitg : ∫ y in (-1 : ℝ)..1, f y * complexProlateSLAction c g y =
      (∫ y in (-1 : ℝ)..1, f y * ((((-(2 * y) : ℝ) : ℂ) * deriv g y) +
        (((1 - y ^ 2 : ℝ) : ℂ) * deriv (deriv g) y))) -
      ∫ y in (-1 : ℝ)..1, f y * (((c ^ 2 * y ^ 2 : ℝ) : ℂ) * g y) := by
    rw [← intervalIntegral.integral_sub hAg hBg]
    exact intervalIntegral.integral_congr fun y _ => by
      simp only [complexProlateSLAction]
      push_cast
      ring
  have hibpf := complex_band_flux_integral_by_parts hf2 hf2c hg1 hg'c
  have hibpg := complex_band_flux_integral_by_parts hg2 hg2c hf1 hf'c
  have hcross : ∫ y in (-1 : ℝ)..1,
      deriv g y * (((1 - y ^ 2 : ℝ) : ℂ) * deriv f y) =
      ∫ y in (-1 : ℝ)..1,
      deriv f y * (((1 - y ^ 2 : ℝ) : ℂ) * deriv g y) :=
    intervalIntegral.integral_congr fun y _ => by ring
  have hmul : ∫ y in (-1 : ℝ)..1,
      g y * (((c ^ 2 * y ^ 2 : ℝ) : ℂ) * f y) =
      ∫ y in (-1 : ℝ)..1,
      f y * (((c ^ 2 * y ^ 2 : ℝ) : ℂ) * g y) :=
    intervalIntegral.integral_congr fun y _ => by ring
  rw [hsplitf, hibpf, hcross, hmul, ← hibpg, ← hsplitg]

def zeroBandPolynomialAction (p : Polynomial ℂ) : Polynomial ℂ :=
  (1 - Polynomial.X ^ 2) * p.derivative.derivative -
    2 * Polynomial.X * p.derivative

theorem zeroBandPolynomialAction_eval (p : Polynomial ℂ) (x : ℝ) :
    Polynomial.eval (x : ℂ) (zeroBandPolynomialAction p) =
      complexProlateSLAction 0 (fun y : ℝ => Polynomial.eval (y : ℂ) p) x := by
  have h1 := (p.hasDerivAt (x : ℂ)).comp_ofReal
  have h2 := (p.derivative.hasDerivAt (x : ℂ)).comp_ofReal
  have hd1 : deriv (fun y : ℝ => Polynomial.eval (y : ℂ) p) x =
      Polynomial.eval (x : ℂ) p.derivative := h1.deriv
  have hd2 : deriv (deriv (fun y : ℝ => Polynomial.eval (y : ℂ) p)) x =
      Polynomial.eval (x : ℂ) p.derivative.derivative := by
    have hfun : deriv (fun y : ℝ => Polynomial.eval (y : ℂ) p) =
        fun y : ℝ => Polynomial.eval (y : ℂ) p.derivative := by
      funext y
      exact ((p.hasDerivAt (y : ℂ)).comp_ofReal).deriv
    rw [hfun]
    exact h2.deriv
  rw [zeroBandPolynomialAction, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  rw [complexProlateSLAction, hd1, hd2]
  simp

theorem zeroBandPolynomialAction_X_pow_add_two (n : ℕ) :
    zeroBandPolynomialAction (Polynomial.X ^ (n + 2) : Polynomial ℂ) =
      (((n + 2) * (n + 1) : ℕ) : ℂ) • Polynomial.X ^ n -
        (((n + 2) * (n + 3) : ℕ) : ℂ) • Polynomial.X ^ (n + 2) := by
  apply Polynomial.funext
  intro z
  simp [zeroBandPolynomialAction, Algebra.smul_def]
  ring

theorem zeroBandPolynomialAction_X_pow (n : ℕ) :
    zeroBandPolynomialAction (Polynomial.X ^ n : Polynomial ℂ) =
      ((n * (n - 1) : ℕ) : ℂ) • Polynomial.X ^ (n - 2) -
        ((n * (n + 1) : ℕ) : ℂ) • Polynomial.X ^ n := by
  cases n with
  | zero => simp [zeroBandPolynomialAction]
  | succ n =>
      cases n with
      | zero =>
          ext j
          simp [zeroBandPolynomialAction, Algebra.smul_def]
      | succ n =>
          rw [show n + 2 - 1 = n + 1 by omega]
          rw [show n + 2 + 1 = n + 3 by omega]
          simpa only [Nat.succ_eq_add_one, add_assoc, one_add_one_eq_two,
            Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
            using zeroBandPolynomialAction_X_pow_add_two n

theorem zeroBandPolynomialAction_add (p q : Polynomial ℂ) :
    zeroBandPolynomialAction (p + q) =
      zeroBandPolynomialAction p + zeroBandPolynomialAction q := by
  simp only [zeroBandPolynomialAction, Polynomial.derivative_add, mul_add]
  module

theorem zeroBandPolynomialAction_smul (z : ℂ) (p : Polynomial ℂ) :
    zeroBandPolynomialAction (z • p) = z • zeroBandPolynomialAction p := by
  simp [zeroBandPolynomialAction, Algebra.smul_def]
  ring

theorem zeroBandPolynomialAction_zero :
    zeroBandPolynomialAction (0 : Polynomial ℂ) = 0 := by
  simp [zeroBandPolynomialAction]

/-- Complex polynomials of degree strictly below `k`, presented without a
degree side condition so that quotient induction is exact. -/
def polynomialMomentSpan (k : ℕ) : Submodule ℂ (Polynomial ℂ) :=
  Submodule.span ℂ
    (Set.range fun i : Fin k => (Polynomial.X : Polynomial ℂ) ^ (i : ℕ))

theorem polynomial_X_pow_mem_momentSpan {j k : ℕ} (hjk : j < k) :
    (Polynomial.X : Polynomial ℂ) ^ j ∈ polynomialMomentSpan k := by
  apply Submodule.subset_span
  exact ⟨⟨j, hjk⟩, rfl⟩

theorem zeroBandPolynomialAction_mem_polynomialMomentSpan {k : ℕ}
    {p : Polynomial ℂ} (hp : p ∈ polynomialMomentSpan k) :
    zeroBandPolynomialAction p ∈ polynomialMomentSpan k := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      rw [zeroBandPolynomialAction_X_pow]
      exact Submodule.sub_mem _
        (Submodule.smul_mem _ _
          (polynomial_X_pow_mem_momentSpan (by omega)))
        (Submodule.smul_mem _ _
          (polynomial_X_pow_mem_momentSpan i.isLt))
  | zero => exact zeroBandPolynomialAction_zero.symm ▸ Submodule.zero_mem _
  | add p q _ _ hp hq =>
      rw [zeroBandPolynomialAction_add]
      exact Submodule.add_mem _ hp hq
  | smul z p _ hp =>
      rw [zeroBandPolynomialAction_smul]
      exact Submodule.smul_mem _ _ hp

/-- On the degree-`k` quotient, zero-band Sturm action is exactly the scalar
`-k(k+1)`.  This is the algebraic triangular half of the all-rung anchor. -/
theorem zeroBandPolynomialAction_add_eigenvalue_mem_lower {k : ℕ}
    {p : Polynomial ℂ} (hp : p ∈ polynomialMomentSpan (k + 1)) :
    zeroBandPolynomialAction p + ((k * (k + 1) : ℕ) : ℂ) • p ∈
      polynomialMomentSpan k := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      change zeroBandPolynomialAction
          ((Polynomial.X : Polynomial ℂ) ^ (i : ℕ)) +
        ((k * (k + 1) : ℕ) : ℂ) • Polynomial.X ^ (i : ℕ) ∈
          polynomialMomentSpan k
      by_cases hik : (i : ℕ) < k
      · exact Submodule.add_mem _
          (zeroBandPolynomialAction_mem_polynomialMomentSpan
            (polynomial_X_pow_mem_momentSpan hik))
          (Submodule.smul_mem _ _ (polynomial_X_pow_mem_momentSpan hik))
      · have hieq : (i : ℕ) = k := by omega
        rw [show (Polynomial.X : Polynomial ℂ) ^ (i : ℕ) =
          Polynomial.X ^ k by rw [hieq]]
        rw [zeroBandPolynomialAction_X_pow]
        cases k with
        | zero => simp [polynomialMomentSpan]
        | succ k =>
            cases k with
            | zero => simp [polynomialMomentSpan]
            | succ k =>
                have hlow : (Polynomial.X : Polynomial ℂ) ^ (k + 2 - 2) ∈
                    polynomialMomentSpan (k + 2) :=
                  polynomial_X_pow_mem_momentSpan (by omega)
                convert Submodule.smul_mem _
                  (((k + 2) * (k + 2 - 1) : ℕ) : ℂ) hlow using 1
                all_goals module
  | zero => simp [zeroBandPolynomialAction_zero]
  | add p q _ _ hp hq =>
      have heq : zeroBandPolynomialAction (p + q) +
          ((k * (k + 1) : ℕ) : ℂ) • (p + q) =
          (zeroBandPolynomialAction p + ((k * (k + 1) : ℕ) : ℂ) • p) +
            (zeroBandPolynomialAction q + ((k * (k + 1) : ℕ) : ℂ) • q) := by
        rw [zeroBandPolynomialAction_add]
        module
      rw [heq]
      exact Submodule.add_mem _ hp hq
  | smul z p _ hp =>
      have heq : zeroBandPolynomialAction (z • p) +
          ((k * (k + 1) : ℕ) : ℂ) • (z • p) =
          z • (zeroBandPolynomialAction p +
            ((k * (k + 1) : ℕ) : ℂ) • p) := by
        rw [zeroBandPolynomialAction_smul]
        module
      rw [heq]
      exact Submodule.smul_mem _ z hp

theorem apertureCpolyToL2_mem_apertureMomentSpan {k : ℕ}
    {p : Polynomial ℂ} (hp : p ∈ polynomialMomentSpan k) :
    apertureCpolyToL2 1 p ∈ apertureMomentSpan k := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      rw [apertureCpolyToL2_X_pow]
      exact apertureComplexMonomial_mem_momentSpan i.isLt
  | zero => simp
  | add p q _ _ hp hq =>
      rw [map_add]
      exact Submodule.add_mem _ hp hq
  | smul z p _ hp =>
      rw [map_smul]
      exact Submodule.smul_mem _ _ hp

theorem exists_polynomialMomentSpan_of_mem_apertureMomentSpan {k : ℕ}
    {v : UnitApertureL2} (hv : v ∈ apertureMomentSpan k) :
    ∃ p : Polynomial ℂ,
      p ∈ polynomialMomentSpan k ∧ apertureCpolyToL2 1 p = v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      exact ⟨Polynomial.X ^ (i : ℕ),
        polynomial_X_pow_mem_momentSpan i.isLt,
        apertureCpolyToL2_X_pow 1 (i : ℕ)⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add v w _ _ hv hw =>
      obtain ⟨p, hp, rfl⟩ := hv
      obtain ⟨q, hq, rfl⟩ := hw
      exact ⟨p + q, Submodule.add_mem _ hp hq, map_add _ p q⟩
  | smul z v _ hv =>
      obtain ⟨p, hp, rfl⟩ := hv
      exact ⟨z • p, Submodule.smul_mem _ _ hp, map_smul _ z p⟩

theorem inner_apertureMomentFlagVector_eq_zero_of_mem {k : ℕ}
    {v : UnitApertureL2} (hv : v ∈ apertureMomentSpan k) :
    inner ℂ (apertureMomentFlagVector k) v = 0 := by
  have horth : inner ℂ
      (apertureMomentResidual k (apertureComplexMonomialL2 1 k)) v = 0 :=
    (apertureMomentSpan k).starProjection_inner_eq_zero _ _ hv
  rw [apertureMomentFlagVector, fourierGroundVector, inner_smul_left,
    horth, mul_zero]

/-- Coefficientwise complex conjugation, used to pass from the bilinear
integration-by-parts identity to the Hermitian `L²` pairing. -/
def coefficientConjugatePolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  p.map (starRingEnd ℂ)

theorem coefficientConjugatePolynomial_eval_real (p : Polynomial ℂ) (x : ℝ) :
    Polynomial.eval (x : ℂ) (coefficientConjugatePolynomial p) =
      (starRingEnd ℂ) (Polynomial.eval (x : ℂ) p) := by
  rw [coefficientConjugatePolynomial]
  convert Polynomial.eval_map_apply
    (f := starRingEnd ℂ) (p := p) (x := (x : ℂ)) using 1
  all_goals simp

theorem coefficientConjugatePolynomial_zeroBandPolynomialAction
    (p : Polynomial ℂ) :
    coefficientConjugatePolynomial (zeroBandPolynomialAction p) =
      zeroBandPolynomialAction (coefficientConjugatePolynomial p) := by
  simp [coefficientConjugatePolynomial, zeroBandPolynomialAction,
    Polynomial.derivative_map]

theorem deriv_polynomial_eval_ofReal (p : Polynomial ℂ) (x : ℝ) :
    deriv (fun y : ℝ => Polynomial.eval (y : ℂ) p) x =
      Polynomial.eval (x : ℂ) p.derivative :=
  ((p.hasDerivAt (x : ℂ)).comp_ofReal).deriv

theorem differentiable_polynomial_eval_ofReal (p : Polynomial ℂ) :
    Differentiable ℝ (fun y : ℝ => Polynomial.eval (y : ℂ) p) :=
  fun x => ((p.hasDerivAt (x : ℂ)).comp_ofReal).differentiableAt

theorem differentiable_deriv_polynomial_eval_ofReal (p : Polynomial ℂ) :
    Differentiable ℝ
      (deriv (fun y : ℝ => Polynomial.eval (y : ℂ) p)) := by
  have hfun : deriv (fun y : ℝ => Polynomial.eval (y : ℂ) p) =
      fun y : ℝ => Polynomial.eval (y : ℂ) p.derivative := by
    funext y
    exact deriv_polynomial_eval_ofReal p y
  rw [hfun]
  exact differentiable_polynomial_eval_ofReal p.derivative

theorem continuous_deriv_deriv_polynomial_eval_ofReal (p : Polynomial ℂ) :
    Continuous
      (deriv (deriv (fun y : ℝ => Polynomial.eval (y : ℂ) p))) := by
  have hfun1 : deriv (fun y : ℝ => Polynomial.eval (y : ℂ) p) =
      fun y : ℝ => Polynomial.eval (y : ℂ) p.derivative := by
    funext y
    exact deriv_polynomial_eval_ofReal p y
  rw [hfun1]
  have hfun2 : deriv (fun y : ℝ => Polynomial.eval (y : ℂ) p.derivative) =
      fun y : ℝ => Polynomial.eval (y : ℂ) p.derivative.derivative := by
    funext y
    exact deriv_polynomial_eval_ofReal p.derivative y
  rw [hfun2]
  exact continuous_cpoly p.derivative.derivative

theorem inner_apertureCpolyToL2_eq_intervalIntegral (p q : Polynomial ℂ) :
    inner ℂ (apertureCpolyToL2 1 p) (apertureCpolyToL2 1 q) =
      ∫ x in (-1 : ℝ)..1,
        (starRingEnd ℂ) (Polynomial.eval (x : ℂ) p) *
          Polynomial.eval (x : ℂ) q := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : ℝ, inner ℂ
        ((apertureCpolyToL2 1 p : UnitApertureL2) x)
        ((apertureCpolyToL2 1 q : UnitApertureL2) x) ∂apertureMeasure 1) =
        ∫ x : ℝ,
          (starRingEnd ℂ) (Polynomial.eval (x : ℂ) p) *
            Polynomial.eval (x : ℂ) q ∂apertureMeasure 1 := by
      refine integral_congr_ae ?_
      filter_upwards [(memLp_apertureCpoly 1 p).coeFn_toLp,
        (memLp_apertureCpoly 1 q).coeFn_toLp] with x hpx hqx
      change inner ℂ
        (((memLp_apertureCpoly 1 p).toLp _ : UnitApertureL2) x)
        (((memLp_apertureCpoly 1 q).toLp _ : UnitApertureL2) x) = _
      rw [hpx, hqx, RCLike.inner_apply]
      ring
    _ = _ := by
      rw [apertureMeasure, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num)]

/-- Zero-band Sturm action is Hermitian-symmetric on the polynomial aperture
core.  Endpoint flux vanishes because its coefficient is `1-x²`. -/
theorem inner_apertureCpolyToL2_zeroBandPolynomialAction_symmetric
    (p q : Polynomial ℂ) :
    inner ℂ (apertureCpolyToL2 1 p)
        (apertureCpolyToL2 1 (zeroBandPolynomialAction q)) =
      inner ℂ (apertureCpolyToL2 1 (zeroBandPolynomialAction p))
        (apertureCpolyToL2 1 q) := by
  rw [inner_apertureCpolyToL2_eq_intervalIntegral,
    inner_apertureCpolyToL2_eq_intervalIntegral]
  have hbil := complexProlateSLAction_band_bilinear_symmetric
    (f := fun x : ℝ => Polynomial.eval (x : ℂ) q)
    (g := fun x : ℝ => Polynomial.eval (x : ℂ)
      (coefficientConjugatePolynomial p))
    (differentiable_polynomial_eval_ofReal q)
    (differentiable_deriv_polynomial_eval_ofReal q)
    (continuous_deriv_deriv_polynomial_eval_ofReal q)
    (differentiable_polynomial_eval_ofReal (coefficientConjugatePolynomial p))
    (differentiable_deriv_polynomial_eval_ofReal
      (coefficientConjugatePolynomial p))
    (continuous_deriv_deriv_polynomial_eval_ofReal
      (coefficientConjugatePolynomial p)) 0
  simp_rw [← zeroBandPolynomialAction_eval] at hbil
  calc
    (∫ x in (-1 : ℝ)..1,
        (starRingEnd ℂ) (Polynomial.eval (x : ℂ) p) *
          Polynomial.eval (x : ℂ) (zeroBandPolynomialAction q)) =
        ∫ x in (-1 : ℝ)..1,
          Polynomial.eval (x : ℂ) (coefficientConjugatePolynomial p) *
            Polynomial.eval (x : ℂ) (zeroBandPolynomialAction q) := by
      apply intervalIntegral.integral_congr
      intro x _
      change (starRingEnd ℂ) (Polynomial.eval (x : ℂ) p) *
          Polynomial.eval (x : ℂ) (zeroBandPolynomialAction q) =
        Polynomial.eval (x : ℂ) (coefficientConjugatePolynomial p) *
          Polynomial.eval (x : ℂ) (zeroBandPolynomialAction q)
      rw [coefficientConjugatePolynomial_eval_real]
    _ = ∫ x in (-1 : ℝ)..1,
          Polynomial.eval (x : ℂ) q *
            Polynomial.eval (x : ℂ)
              (zeroBandPolynomialAction (coefficientConjugatePolynomial p)) := hbil
    _ = ∫ x in (-1 : ℝ)..1,
        (starRingEnd ℂ)
            (Polynomial.eval (x : ℂ) (zeroBandPolynomialAction p)) *
          Polynomial.eval (x : ℂ) q := by
      apply intervalIntegral.integral_congr
      intro x _
      change Polynomial.eval (x : ℂ) q *
          Polynomial.eval (x : ℂ)
            (zeroBandPolynomialAction (coefficientConjugatePolynomial p)) =
        (starRingEnd ℂ)
            (Polynomial.eval (x : ℂ) (zeroBandPolynomialAction p)) *
          Polynomial.eval (x : ℂ) q
      rw [← coefficientConjugatePolynomial_zeroBandPolynomialAction,
        coefficientConjugatePolynomial_eval_real]
      ring

/-- Every orthogonal moment rung is intrinsically the zero-band Sturm
eigenline with eigenvalue `-k(k+1)`.  No special-function formula or spectral
labelling is assumed: triangular quotient action plus Hermitian symmetry force
the result. -/
theorem exists_apertureMomentFlagPolynomial_zeroBand_eigen (k : ℕ) :
    ∃ p : Polynomial ℂ,
      p ∈ polynomialMomentSpan (k + 1) ∧
      apertureCpolyToL2 1 p = apertureMomentFlagVector k ∧
      p ≠ 0 ∧
      zeroBandPolynomialAction p =
        -((k * (k + 1) : ℕ) : ℂ) • p := by
  obtain ⟨p, hp, hpflag⟩ :=
    exists_polynomialMomentSpan_of_mem_apertureMomentSpan
      (apertureMomentFlagVector_mem_span_succ k)
  let K : ℂ := ((k * (k + 1) : ℕ) : ℂ)
  let d : Polynomial ℂ := zeroBandPolynomialAction p + K • p
  have hdmem : d ∈ polynomialMomentSpan k := by
    dsimp only [d, K]
    exact zeroBandPolynomialAction_add_eigenvalue_mem_lower hp
  have hAdmem : apertureCpolyToL2 1 d ∈ apertureMomentSpan k :=
    apertureCpolyToL2_mem_apertureMomentSpan hdmem
  have hLdmem : zeroBandPolynomialAction d ∈ polynomialMomentSpan k :=
    zeroBandPolynomialAction_mem_polynomialMomentSpan hdmem
  have hALdmem : apertureCpolyToL2 1 (zeroBandPolynomialAction d) ∈
      apertureMomentSpan k :=
    apertureCpolyToL2_mem_apertureMomentSpan hLdmem
  have hflag_d : inner ℂ (apertureCpolyToL2 1 p)
      (apertureCpolyToL2 1 d) = 0 := by
    rw [hpflag]
    exact inner_apertureMomentFlagVector_eq_zero_of_mem hAdmem
  have hflag_Ld : inner ℂ (apertureCpolyToL2 1 p)
      (apertureCpolyToL2 1 (zeroBandPolynomialAction d)) = 0 := by
    rw [hpflag]
    exact inner_apertureMomentFlagVector_eq_zero_of_mem hALdmem
  have hLp_d : inner ℂ
      (apertureCpolyToL2 1 (zeroBandPolynomialAction p))
      (apertureCpolyToL2 1 d) = 0 := by
    rw [← inner_apertureCpolyToL2_zeroBandPolynomialAction_symmetric]
    exact hflag_Ld
  have hAd_decomp : apertureCpolyToL2 1 d =
      apertureCpolyToL2 1 (zeroBandPolynomialAction p) +
        K • apertureCpolyToL2 1 p := by
    dsimp only [d]
    rw [map_add, map_smul]
  have hself : inner ℂ (apertureCpolyToL2 1 d)
      (apertureCpolyToL2 1 d) = 0 := by
    calc
      inner ℂ (apertureCpolyToL2 1 d) (apertureCpolyToL2 1 d) =
          inner ℂ
            (apertureCpolyToL2 1 (zeroBandPolynomialAction p) +
              K • apertureCpolyToL2 1 p)
            (apertureCpolyToL2 1 d) :=
        congrArg (fun v : UnitApertureL2 =>
          inner ℂ v (apertureCpolyToL2 1 d)) hAd_decomp
      _ = 0 := by
        rw [inner_add_left, hLp_d, inner_smul_left,
          hflag_d, mul_zero, add_zero]
  have hAdzero : apertureCpolyToL2 1 d = 0 := inner_self_eq_zero.mp hself
  have hdzero : d = 0 := by
    apply apertureCpolyToL2_injective one_pos
    simpa using hAdzero
  have hpeig : zeroBandPolynomialAction p = -K • p := by
    dsimp only [d] at hdzero
    simpa using eq_neg_of_add_eq_zero_left hdzero
  have hpne : p ≠ 0 := by
    intro hpzero
    apply apertureMomentFlagVector_ne_zero k
    rw [← hpflag, hpzero, map_zero]
  exact ⟨p, hp, hpflag, hpne, by simpa only [K] using hpeig⟩

end GaloisForLFunctions.RHTower
