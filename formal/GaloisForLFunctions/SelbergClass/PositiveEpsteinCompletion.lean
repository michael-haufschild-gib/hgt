import GaloisForLFunctions.SelbergClass.PositiveEpsteinCoefficients
import GaloisForLFunctions.SelbergClass.PositiveEpsteinGrowth
import GaloisForLFunctions.LatticeSectionTheory.DefiniteCountsHaveOffLineZeros
import GaloisForLFunctions.RHTower.ReciprocalGammaExactOrderOne
import GaloisForLFunctions.RHTower.SelbergClass.FullConjugate
import GaloisForLFunctions.HTGeometry.OrderOneEnvelopeRootDivision
import GaloisForLFunctions.HTGeometry.OrderOneEntireQuotient
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# A positive Epstein series and its scalar completion

The form `m² + 64n²` has determinant `64`. Scaling its completed Epstein
function by `8ˢ/2` balances the dual lattice and normalizes the first ordinary
Dirichlet coefficient to one. Clearing the two poles gives an entire numerator.
-/

noncomputable section

open Complex Filter Topology Set
open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.PositiveEpstein

/-- The normalized rectangular representation counts as an arithmetic function. -/
def arithmeticCoeffs : ArithmeticFunction ℂ :=
  ⟨fun n => (coeff n : ℂ), by simp⟩

@[simp] theorem arithmeticCoeffs_apply (n : ℕ) : arithmeticCoeffs n = (coeff n : ℂ) := rfl

theorem qNorm_eq_rectForm (p : LatticePoint) :
    (qNorm p : ℝ) = rectForm 8 p.1 := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (qNorm_cast p)
  push_cast at h
  simpa only [rectForm, show (8 : ℝ) ^ 2 = 64 by norm_num] using h

private def epsteinTerm (y : ℝ) (s : ℂ) (p : ℤ × ℤ) : ℂ :=
  Complex.Gamma s * (if p = 0 then 0 else 1) /
    ((Real.pi * rectForm y p : ℝ) : ℂ) ^ s

/-- Grouping representations identifies the lattice completion with the ordinary series. -/
theorem epsteinLambda_eight_eq_lSeries {s : ℂ} (hs : 1 < s.re) :
    epsteinLambda 8 (by norm_num) s =
      2 * Complex.Gamma s / (Real.pi : ℂ) ^ s * LSeries (fun n => (coeff n : ℂ)) s := by
  have hsupp : Function.support (epsteinTerm 8 s) ⊆ {p : ℤ × ℤ | p ≠ (0, 0)} := by
    intro p hp hp0
    apply hp
    simp [epsteinTerm, hp0]
  have hsub : HasSum (fun p : LatticePoint => epsteinTerm 8 s p.1)
      (epsteinLambda 8 (by norm_num) s) :=
    (hasSum_subtype_iff_of_support_subset hsupp).mpr
      (hasSum_epsteinLambda (by norm_num : (0 : ℝ) < 8) hs)
  have hsub' : HasSum (fun p : LatticePoint =>
      Complex.Gamma s / (Real.pi : ℂ) ^ s * latticeTerm s p)
      (epsteinLambda 8 (by norm_num) s) := by
    refine hsub.congr_fun fun p => ?_
    have hp0 : p.1 ≠ (0 : ℤ × ℤ) := p.2
    rw [epsteinTerm, if_neg hp0, mul_one, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (rectForm_nonneg 8 p.1),
      ← qNorm_eq_rectForm p]
    push_cast
    rw [latticeTerm, cpow_neg]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [(lSeriesSummable_and_eq hs).2]
  calc epsteinLambda 8 (by norm_num) s =
      Complex.Gamma s / (Real.pi : ℂ) ^ s * ∑' p, latticeTerm s p :=
        hsub'.unique ((summable_latticeTerm hs).hasSum.mul_left _)
    _ = 2 * Complex.Gamma s / (Real.pi : ℂ) ^ s * ((∑' p, latticeTerm s p) / 2) := by ring

/-- Coordinate interchange identifies the dual rectangular lattice after scaling by sixty-four. -/
theorem epsteinLambda_dual_eight {s : ℂ} (hs : 1 < s.re) :
    epsteinLambda (1 / 8) (by norm_num) s =
      (64 : ℂ) ^ s * epsteinLambda 8 (by norm_num) s := by
  have hQ (p : ℤ × ℤ) : rectForm 8 p.swap = 64 * rectForm (1 / 8) p := by
    unfold rectForm
    dsimp only [Prod.swap]
    ring
  have hterm (p : ℤ × ℤ) : epsteinTerm (1 / 8) s p =
      (64 : ℂ) ^ s * epsteinTerm 8 s p.swap := by
    by_cases hp : p = 0
    · simp [epsteinTerm, hp]
    have hswap : p.swap ≠ (0 : ℤ × ℤ) := by
      intro h
      apply hp
      simpa using congrArg Prod.swap h
    have hq : 0 < Real.pi * rectForm (1 / 8) p :=
      mul_pos Real.pi_pos (rectForm_pos (by norm_num) hp)
    have hpow : (((Real.pi * rectForm (1 / 8) p : ℝ) : ℂ) ^ s) ≠ 0 :=
      cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hq.ne'))
    have h64 : (64 : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
    have hbase : Real.pi * rectForm 8 p.swap = 64 * (Real.pi * rectForm (1 / 8) p) := by
      rw [hQ]
      ring
    have hfactor : (((Real.pi * rectForm 8 p.swap : ℝ) : ℂ) ^ s) =
        (64 : ℂ) ^ s * (((Real.pi * rectForm (1 / 8) p : ℝ) : ℂ) ^ s) := by
      rw [hbase, Complex.ofReal_mul]
      simpa only [Complex.ofReal_ofNat] using
        Complex.mul_cpow_ofReal_nonneg (a := 64) (by norm_num) hq.le s
    rw [epsteinTerm, epsteinTerm, if_neg hp, if_neg hswap, mul_one, hfactor]
    field_simp [h64, hpow]
  have hswapSum : (∑' p : ℤ × ℤ, epsteinTerm 8 s p.swap) =
      epsteinLambda 8 (by norm_num) s :=
    ((Equiv.prodComm ℤ ℤ).tsum_eq (epsteinTerm 8 s)).trans
      (hasSum_epsteinLambda (by norm_num : (0 : ℝ) < 8) hs).tsum_eq
  calc epsteinLambda (1 / 8) (by norm_num) s =
      ∑' p : ℤ × ℤ, epsteinTerm (1 / 8) s p :=
        (hasSum_epsteinLambda (by norm_num : (0 : ℝ) < 1 / 8) hs).tsum_eq.symm
    _ = ∑' p : ℤ × ℤ, (64 : ℂ) ^ s * epsteinTerm 8 s p.swap := tsum_congr hterm
    _ = (64 : ℂ) ^ s * ∑' p : ℤ × ℤ, epsteinTerm 8 s p.swap := tsum_mul_left
    _ = (64 : ℂ) ^ s * epsteinLambda 8 (by norm_num) s := by rw [hswapSum]


/-- The normalized completion of the positive rectangular Epstein series. -/
def completed (s : ℂ) : ℂ :=
  (8 : ℂ) ^ s / 2 * epsteinLambda 8 (by norm_num) s

/-- The entire numerator obtained by clearing the completion's poles at zero and one. -/
def numerator (s : ℂ) : ℂ :=
  (8 : ℂ) ^ s / 2 *
    (s * (s - 1) * (rectFEPair 8 (by norm_num)).Λ₀ s - (s - 1) + s / 8)

theorem analytic_numerator : AnalyticOnNhd ℂ numerator univ := by
  apply Complex.analyticOnNhd_univ_iff_differentiable.mpr
  have hpow : Differentiable ℂ (fun s : ℂ => (8 : ℂ) ^ s) :=
    differentiable_id.const_cpow (.inl (by norm_num))
  have hΛ := (rectFEPair 8 (by norm_num)).differentiable_Λ₀
  unfold numerator
  fun_prop

private theorem epstein_eight_eq (s : ℂ) :
    epsteinLambda 8 (by norm_num) s =
      (rectFEPair 8 (by norm_num)).Λ₀ s - 1 / s - (1 / 8) / (1 - s) := by
  unfold epsteinLambda WeakFEPair.Λ
  simp only [rectFEPair, smul_eq_mul, mul_one, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]

theorem numerator_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    numerator s = s * (s - 1) * completed s := by
  rw [numerator, completed, epstein_eight_eq]
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, h1s]
  ring

@[simp] theorem numerator_zero : numerator 0 = 1 / 2 := by
  norm_num [numerator]

@[simp] theorem numerator_one : numerator 1 = 1 / 2 := by
  norm_num [numerator]

theorem orderOneEnvelope_numerator : OrderOneEnvelope numerator := by
  have hpow : OrderOneEnvelope (fun s : ℂ => (8 : ℂ) ^ s) := by
    refine ((orderOneEnvelope_natCast_cpow_neg (n := 8) (by norm_num)).comp_affine
      (-1) 0).congr fun s => ?_
    norm_num only [neg_mul, one_mul, add_zero, neg_neg, Nat.cast_ofNat]
  have hpoly : OrderOneEnvelope (fun s : ℂ => s * (s - 1)) := by
    refine (orderOneEnvelope_polynomial
      (Polynomial.X * (Polynomial.X - 1) : Polynomial ℂ)).congr fun z => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
  have hcorrection : OrderOneEnvelope (fun s : ℂ => -(s - 1) + s / 8) := by
    refine (orderOneEnvelope_polynomial (-(Polynomial.X - 1) + Polynomial.X *
      Polynomial.C (8⁻¹ : ℂ))).congr fun z => ?_
    simp only [Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      div_eq_mul_inv]
  refine ((hpow.const_mul (1 / 2)).mul
    ((hpoly.mul (orderOneEnvelope_epsteinLambda_zero (by norm_num : (0 : ℝ) < 8))).add
      hcorrection)).congr fun s => ?_
  unfold numerator
  ring

/-- Entire regularization of the ordinary Dirichlet series at its possible pole. -/
def regularized (s : ℂ) : ℂ :=
  ((Real.pi / 8 : ℝ) : ℂ) ^ s * reciprocalGammaEntire (s + 1) * numerator s

/-- The completion uses the ordinary gamma presentation `Q=8/π`, `Γ(s)`. -/
theorem completed_eq_gamma_lSeries {s : ℂ} (hs : 1 < s.re) :
    completed s = ((8 / Real.pi : ℝ) : ℂ) ^ s * Complex.Gamma s *
      LSeries (fun n => (coeff n : ℂ)) s := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hπpow : (Real.pi : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hπ)
  have hbase : ((8 / Real.pi : ℝ) : ℂ) * (Real.pi : ℂ) = 8 := by
    push_cast
    field_simp [hπ]
  have hscale : ((8 / Real.pi : ℝ) : ℂ) ^ s * (Real.pi : ℂ) ^ s = (8 : ℂ) ^ s := by
    rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) Real.pi_pos.le, hbase]
  rw [completed, epsteinLambda_eight_eq_lSeries hs, ← hscale]
  field_simp [hπpow]

private theorem reciprocal_scales (s : ℂ) :
    ((Real.pi / 8 : ℝ) : ℂ) ^ s * ((8 / Real.pi : ℝ) : ℂ) ^ s = 1 := by
  rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), ← Complex.ofReal_mul]
  have heq : Real.pi / 8 * (8 / Real.pi) = 1 := by field_simp [Real.pi_ne_zero]
  rw [heq, Complex.ofReal_one, one_cpow]

/-- The entire regularization agrees with `(s−1)` times the ordinary Dirichlet series. -/
theorem regularized_eq_mul_lSeries {s : ℂ} (hs : 1 < s.re) :
    regularized s = (s - 1) * LSeries (fun n => (coeff n : ℂ)) s := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
  have hΓ : Complex.Gamma (s + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith only [hs])
  have hcancel : s * Complex.Gamma s * (Complex.Gamma (s + 1))⁻¹ = 1 := by
    rw [← Complex.Gamma_add_one s hs0, mul_inv_cancel₀ hΓ]
  rw [regularized, numerator_eq s hs0 hs1, completed_eq_gamma_lSeries hs,
    reciprocalGammaEntire]
  calc ((Real.pi / 8 : ℝ) : ℂ) ^ s * (Complex.Gamma (s + 1))⁻¹ *
      (s * (s - 1) * (((8 / Real.pi : ℝ) : ℂ) ^ s * Complex.Gamma s *
        LSeries (fun n => (coeff n : ℂ)) s)) =
      (((Real.pi / 8 : ℝ) : ℂ) ^ s * ((8 / Real.pi : ℝ) : ℂ) ^ s) *
        (s * Complex.Gamma s * (Complex.Gamma (s + 1))⁻¹) *
          ((s - 1) * LSeries (fun n => (coeff n : ℂ)) s) := by ring
    _ = (s - 1) * LSeries (fun n => (coeff n : ℂ)) s := by
      rw [reciprocal_scales, hcancel, one_mul, one_mul]

theorem analytic_regularized : AnalyticOnNhd ℂ regularized univ := by
  apply Complex.analyticOnNhd_univ_iff_differentiable.mpr
  have hbase : ((Real.pi / 8 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 8)).ne'
  have hpow : Differentiable ℂ (fun s : ℂ => ((Real.pi / 8 : ℝ) : ℂ) ^ s) :=
    differentiable_id.const_cpow (.inl hbase)
  have hΓ : Differentiable ℂ reciprocalGammaEntire := Complex.differentiable_one_div_Gamma
  have hR := Complex.analyticOnNhd_univ_iff_differentiable.mp analytic_numerator
  unfold regularized
  fun_prop

@[simp] theorem regularized_one : regularized 1 = (Real.pi : ℂ) / 16 := by
  have hΓ : Complex.Gamma (1 + 1 : ℂ) = 1 := by
    rw [Complex.Gamma_add_one 1 (by norm_num), Complex.Gamma_one, mul_one]
  rw [regularized, cpow_one, numerator_one, reciprocalGammaEntire, hΓ, inv_one, mul_one]
  push_cast
  ring

theorem orderOneEnvelope_regularized : OrderOneEnvelope regularized := by
  have hbase : ((Real.pi / 8 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 8)).ne'
  have hpow : OrderOneEnvelope (fun s : ℂ => ((Real.pi / 8 : ℝ) : ℂ) ^ s) :=
    (orderOneEnvelope_exp_mul (Complex.log ((Real.pi / 8 : ℝ) : ℂ))).congr
      fun s => (Complex.cpow_def_of_ne_zero hbase _).symm
  exact (hpow.mul (RHTower.orderOneEnvelope_reciprocalGammaEntire.comp_affine 1 1 |>.congr
    fun s => by simp only [one_mul])).mul orderOneEnvelope_numerator

/-- Finite-order entire regularization of the positive ordinary Epstein series. -/
def entireRegularization : RHTower.EntireFiniteOrder where
  toFun := regularized
  analytic := analytic_regularized
  growth := by
    obtain ⟨C, hC, hbound⟩ := orderOneEnvelope_regularized
    refine ⟨Real.exp (2 * C), 2 * C, 2, Real.exp_pos _, by positivity, by norm_num, ?_⟩
    intro z
    have hr : 0 ≤ ‖z‖ := norm_nonneg z
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 + ‖z‖)
    have hmul := mul_le_mul_of_nonneg_left hlog
      (mul_nonneg hC.le (by positivity : (0 : ℝ) ≤ 1 + ‖z‖))
    have hexp : orderOneWeight C z ≤ 2 * C + 2 * C * ‖z‖ ^ 2 := by
      unfold orderOneWeight
      nlinarith only [hmul, mul_nonneg hC.le (sq_nonneg (1 - ‖z‖))]
    rw [Real.rpow_two]
    calc ‖regularized z‖ ≤ Real.exp (orderOneWeight C z) := hbound z
      _ ≤ Real.exp (2 * C + 2 * C * ‖z‖ ^ 2) := Real.exp_le_exp.mpr hexp
      _ = Real.exp (2 * C) * Real.exp (2 * C * ‖z‖ ^ 2) := Real.exp_add _ _

def continuation : RHTower.SelbergAnalyticContinuation where
  poleOrder := 1
  regularized := entireRegularization

@[simp] theorem continuation_value (s : ℂ) : continuation.value s = regularized s / (s - 1) := by
  simp only [continuation, RHTower.SelbergAnalyticContinuation.value,
    entireRegularization, pow_one]

theorem lSeries_eq_continuation {s : ℂ} (hs : 1 < s.re) :
    LSeries arithmeticCoeffs s = continuation.value s := by
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    subst s
    norm_num at hs
  rw [continuation_value, regularized_eq_mul_lSeries hs]
  change LSeries (fun n => (coeff n : ℂ)) s = _
  field_simp [hs1]

theorem regularized_conjugate (s : ℂ) : star (regularized (star s)) = regularized s := by
  have hcoeff : RHTower.selbergArithmeticFunctionConjugate arithmeticCoeffs = arithmeticCoeffs := by
    ext n
    simp only [RHTower.selbergArithmeticFunctionConjugate_apply, arithmeticCoeffs_apply,
      Complex.star_def, Complex.conj_ofReal]
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
  have htwo : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have hlocal : (fun z : ℂ => star (regularized (star z))) =ᶠ[𝓝 (2 : ℂ)] regularized := by
    filter_upwards [hopen.mem_nhds htwo] with z hz
    have hzstar : 1 < (star z).re := by simpa using hz
    rw [regularized_eq_mul_lSeries hzstar, regularized_eq_mul_lSeries hz]
    change (starRingEnd ℂ) ((star z - 1) * LSeries arithmeticCoeffs (star z)) =
      (z - 1) * LSeries arithmeticCoeffs z
    have hL : star (LSeries arithmeticCoeffs (star z)) = LSeries arithmeticCoeffs z := by
      rw [← RHTower.lSeries_conjugate, hcoeff]
    rw [map_mul, map_sub, map_one]
    change (star (star z) - 1) * star (LSeries arithmeticCoeffs (star z)) = _
    rw [star_star, hL]
  exact congrFun (entireRegularization.conjugate.analytic.eq_of_eventuallyEq
    analytic_regularized hlocal) s

theorem continuation_conjugate (s : ℂ) :
    star (continuation.value (star s)) = continuation.value s := by
  rw [← RHTower.SelbergAnalyticContinuation.conjugate_value]
  change star (regularized (star s)) / (s - 1) ^ 1 = continuation.value s
  rw [pow_one, regularized_conjugate, continuation_value]

/-- A degree-two gamma presentation with root number one. -/
def gammaData : RHTower.SelbergGammaData where
  Q := 8 / Real.pi
  Q_pos := div_pos (by norm_num) Real.pi_pos
  rank := 1
  lambda := fun _ => 1
  lambda_pos := fun _ => zero_lt_one
  mu := fun _ => 0
  mu_re_nonneg := fun _ => le_refl 0
  rootNumber := 1
  rootNumber_norm := by norm_num

@[simp] theorem gammaFactor_eq (s : ℂ) :
    gammaData.gammaFactor s = ((8 / Real.pi : ℝ) : ℂ) ^ s * Complex.Gamma s := by
  simp [gammaData, RHTower.SelbergGammaData.gammaFactor]

private theorem gammaFactor_conjugate (s : ℂ) :
    star (gammaData.gammaFactor (star s)) = gammaData.gammaFactor s := by
  have hself : gammaData.conjugate = gammaData := by
    simp [gammaData, RHTower.SelbergGammaData.conjugate]
  rw [← RHTower.SelbergGammaData.conjugate_gammaFactor, hself]

private theorem representedCompleted_conjugate (s : ℂ) :
    star (RHTower.selbergCompletedValue gammaData continuation (star s)) =
      RHTower.selbergCompletedValue gammaData continuation s := by
  change (starRingEnd ℂ) (gammaData.gammaFactor (star s) * continuation.value (star s)) =
    gammaData.gammaFactor s * continuation.value s
  rw [map_mul]
  change star (gammaData.gammaFactor (star s)) * star (continuation.value (star s)) = _
  rw [gammaFactor_conjugate, continuation_conjugate]

private theorem representedCompleted_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓ : Complex.Gamma s ≠ 0) :
    RHTower.selbergCompletedValue gammaData continuation s = completed s := by
  have hΓ1 : Complex.Gamma (s + 1) ≠ 0 := by
    rw [Complex.Gamma_add_one s hs0]
    exact mul_ne_zero hs0 hΓ
  have hcancel : s * Complex.Gamma s * (Complex.Gamma (s + 1))⁻¹ = 1 := by
    rw [← Complex.Gamma_add_one s hs0, mul_inv_cancel₀ hΓ1]
  have hscale := reciprocal_scales s
  have hscale' : ((8 / Real.pi : ℝ) : ℂ) ^ s * ((Real.pi / 8 : ℝ) : ℂ) ^ s = 1 := by
    rw [mul_comm]
    exact hscale
  rw [RHTower.selbergCompletedValue, gammaFactor_eq, continuation_value, regularized,
    reciprocalGammaEntire, numerator_eq s hs0 hs1]
  calc ((8 / Real.pi : ℝ) : ℂ) ^ s * Complex.Gamma s *
      (((Real.pi / 8 : ℝ) : ℂ) ^ s * (Complex.Gamma (s + 1))⁻¹ *
        (s * (s - 1) * completed s) / (s - 1)) =
      (((8 / Real.pi : ℝ) : ℂ) ^ s * ((Real.pi / 8 : ℝ) : ℂ) ^ s) *
        (s * Complex.Gamma s * (Complex.Gamma (s + 1))⁻¹) * completed s := by
          field_simp [sub_ne_zero.mpr hs1, hΓ1]
    _ = completed s := by rw [hscale', hcancel, one_mul, one_mul]

private theorem completed_one_sub_rightHalfPlane {s : ℂ} (hs : 1 < s.re) :
    completed (1 - s) = completed s := by
  rw [completed, completed, epsteinLambda_one_sub (by norm_num : (0 : ℝ) < 8) s,
    epsteinLambda_dual_eight hs]
  have h64 : (64 : ℂ) ^ s = (8 : ℂ) ^ s * (8 : ℂ) ^ s := by
    simpa only [Complex.ofReal_ofNat, show (8 : ℂ) * 8 = 64 by norm_num] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 8)
        (by norm_num : (0 : ℝ) ≤ 8) s
  have h8 : (8 : ℂ) ^ (1 - s) * (8 : ℂ) ^ s = 8 := by
    rw [← cpow_add _ _ (by norm_num : (8 : ℂ) ≠ 0)]
    simp only [sub_add_cancel, cpow_one]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [h64]
  calc (8 : ℂ) ^ (1 - s) / 2 * (1 / 8 *
      (8 ^ s * 8 ^ s * epsteinLambda 8 (by norm_num) s)) =
      (8 ^ (1 - s) * 8 ^ s) / 8 *
        (8 ^ s / 2 * epsteinLambda 8 (by norm_num) s) := by ring
    _ = 8 ^ s / 2 * epsteinLambda 8 (by norm_num) s := by rw [h8]; norm_num

/-- Balancing the rectangular lattice makes the pole-cleared numerator reflection-even. -/
theorem numerator_one_sub (s : ℂ) : numerator (1 - s) = numerator s := by
  have hR := Complex.analyticOnNhd_univ_iff_differentiable.mp analytic_numerator
  have hreflect : AnalyticOnNhd ℂ (fun z : ℂ => numerator (1 - z)) univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (hR.comp ((differentiable_const (1 : ℂ)).sub differentiable_id))
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
  have htwo : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have hlocal : (fun z : ℂ => numerator (1 - z)) =ᶠ[𝓝 (2 : ℂ)] numerator := by
    filter_upwards [hopen.mem_nhds htwo] with z hz
    have hz0 : z ≠ 0 := by intro h; subst z; norm_num at hz
    have hz1 : z ≠ 1 := by intro h; subst z; norm_num at hz
    have h1z0 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
    have h1z1 : 1 - z ≠ 1 := by
      intro h
      apply hz0
      simpa using congrArg (fun w : ℂ => 1 - w) h
    rw [numerator_eq (1 - z) h1z0 h1z1, numerator_eq z hz0 hz1,
      completed_one_sub_rightHalfPlane hz]
    ring
  exact congrFun (hreflect.eq_of_eventuallyEq analytic_numerator hlocal) s

/-- The normalized completion satisfies its scalar functional equation away from its poles. -/
theorem completed_one_sub (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completed (1 - s) = completed s := by
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have h1s1 : 1 - s ≠ 1 := by
    intro h
    apply hs0
    simpa using congrArg (fun w : ℂ => 1 - w) h
  have h := numerator_one_sub s
  rw [numerator_eq (1 - s) h1s0 h1s1, numerator_eq s hs0 hs1] at h
  have heq : (1 - s) * (1 - s - 1) = s * (s - 1) := by ring
  rw [heq] at h
  exact mul_left_cancel₀ (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) h

/-- The scalar functional equation holds for the pole-safe Selberg presentation. -/
theorem functionalEquation :
    RHTower.selbergCompletedValue gammaData continuation =ᶠ[codiscrete ℂ]
      fun s => gammaData.rootNumber * RHTower.selbergConjugateReflection
        (RHTower.selbergCompletedValue gammaData continuation) s := by
  let g : ℂ → ℂ := fun s => reciprocalGammaEntire s * reciprocalGammaEntire (1 - s)
  have hd : Differentiable ℂ reciprocalGammaEntire := Complex.differentiable_one_div_Gamma
  have hg : AnalyticOnNhd ℂ g univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (hd.mul (hd.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)))
  have hgzero : ¬ Set.EqOn g 0 univ := by
    intro h
    have hΓ : Complex.Gamma (1 / 2 : ℂ) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by norm_num)
    have hpoint : g (1 / 2) ≠ 0 := by
      dsimp only [g, reciprocalGammaEntire]
      rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring]
      exact mul_ne_zero (inv_ne_zero hΓ) (inv_ne_zero hΓ)
    exact hpoint (h (mem_univ _))
  have hgood : ∀ᶠ s in codiscrete ℂ, g s ≠ 0 :=
    (hg.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left hgzero
  have hzero : (singleton (0 : ℂ))ᶜ ∈ codiscrete ℂ :=
    compl_mem_codiscrete_iff.mpr ⟨isClosed_singleton, subsingleton_singleton.isDiscrete⟩
  have hone : (singleton (1 : ℂ))ᶜ ∈ codiscrete ℂ :=
    compl_mem_codiscrete_iff.mpr ⟨isClosed_singleton, subsingleton_singleton.isDiscrete⟩
  filter_upwards [hgood, hzero, hone] with s hgs hs0 hs1
  have hs0' : s ≠ 0 := by simpa using hs0
  have hs1' : s ≠ 1 := by simpa using hs1
  have hΓs : Complex.Gamma s ≠ 0 := by
    intro h
    apply hgs
    simp only [g, reciprocalGammaEntire, h, inv_zero, zero_mul]
  have hΓ1s : Complex.Gamma (1 - s) ≠ 0 := by
    intro h
    apply hgs
    simp only [g, reciprocalGammaEntire, h, inv_zero, mul_zero]
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1'.symm
  have h1s1 : 1 - s ≠ 1 := by
    intro h
    apply hs0'
    simpa using congrArg (fun w : ℂ => 1 - w) h
  have hroot : gammaData.rootNumber = 1 := rfl
  rw [hroot, one_mul, RHTower.selbergConjugateReflection,
    show 1 - star s = star (1 - s) by simp, representedCompleted_conjugate,
    representedCompleted_eq s hs0' hs1' hΓs,
    representedCompleted_eq (1 - s) h1s0 h1s1 hΓ1s, completed_one_sub s hs0' hs1']

/-- A normalized positive member of the extended Selberg class without multiplicative coefficients. -/
def extendedClass : RHTower.ExtendedSelbergClass where
  coeff := arithmeticCoeffs
  coeff_ne_zero := by
    intro h
    have h1 := congrArg (fun f : ArithmeticFunction ℂ => f 1) h
    simp at h1
  lSeriesSummable := fun _ hs => (lSeriesSummable_and_eq hs).1
  continuation := continuation
  lSeries_eq_value := fun _ hs => lSeries_eq_continuation hs
  gammaData := gammaData
  functionalEquation := functionalEquation

theorem extendedClass_degree : extendedClass.presentationDegree = 2 := by
  change 2 * ∑ _j : Fin 1, (1 : ℝ) = 2
  norm_num

theorem extendedClass_conductor : extendedClass.presentationConductor = 256 := by
  change gammaData.conductor = 256
  have hdegree : gammaData.degree = 2 := by
    change 2 * ∑ _j : Fin 1, (1 : ℝ) = 2
    norm_num
  rw [RHTower.SelbergGammaData.conductor, hdegree]
  change (2 * Real.pi) ^ (2 : ℝ) * (8 / Real.pi) ^ 2 *
    (∏ _j : Fin 1, (1 : ℝ) ^ (2 * (1 : ℝ))) = 256
  norm_num [Real.rpow_two]
  field_simp [Real.pi_ne_zero]
  ring

/-- The completion has a real zero strictly between the critical line and its pole. -/
theorem completed_has_offLine_zero :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ completed σ = 0 := by
  obtain ⟨σ, hσ, hσ1, hz⟩ := epsteinLambda_eight_has_offLine_zero
  exact ⟨σ, hσ, hσ1, by rw [completed, hz, mul_zero]⟩

/-- The positive ordinary series has a zero strictly inside the right half of the critical strip. -/
theorem extendedClass_has_offLine_zero :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ extendedClass (σ : ℂ) = 0 := by
  obtain ⟨σ, hσ, hσ1, hz⟩ := completed_has_offLine_zero
  have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith only [hσ])
  have hσone : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1.ne
  have hR : numerator σ = 0 := by rw [numerator_eq _ hσ0 hσone, hz, mul_zero]
  have hH : regularized σ = 0 := by rw [regularized, hR, mul_zero]
  refine ⟨σ, hσ, hσ1, ?_⟩
  change continuation.value (σ : ℂ) = 0
  rw [continuation_value, hH, zero_div]

/-- Positivity, normalization, Ramanujan bounds and the full extended-Selberg analytic axioms
do not force the critical-line condition. The positive coefficients fail multiplicativity. -/
theorem exists_positive_ramanujan_counterexample :
    ∃ F : RHTower.ExtendedSelbergClass,
      F.presentationDegree = 2 ∧ F.coeff 1 = 1 ∧
      (∀ n : ℕ, 0 ≤ (F.coeff n).re ∧ (F.coeff n).im = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, 0 < n → ‖F.coeff n‖ ≤ C * (n : ℝ) ^ ε) ∧
      (∃ m n : ℕ, Nat.Coprime m n ∧ F.coeff (m * n) ≠ F.coeff m * F.coeff n) ∧
      ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ F (σ : ℂ) = 0 := by
  refine ⟨extendedClass, extendedClass_degree, ?_, ?_, ?_, ?_, extendedClass_has_offLine_zero⟩
  · change (coeff 1 : ℂ) = 1
    simp only [coeff_one, Complex.ofReal_one]
  · intro n
    exact ⟨coeff_nonneg n, rfl⟩
  · exact ramanujan_bound
  · refine ⟨5, 13, coeff_not_multiplicative.1, ?_⟩
    change (coeff (5 * 13) : ℂ) ≠ (coeff 5 : ℂ) * (coeff 13 : ℂ)
    intro h
    apply coeff_not_multiplicative.2
    exact_mod_cast h

end GaloisForLFunctions.SelbergClass.PositiveEpstein
