import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerCoefficients
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.ReciprocalGammaExactOrderOne
import GaloisForLFunctions.RHTower.ZetaPoleSplit
import GaloisForLFunctions.RHTower.SelbergClass.FullConjugate
import GaloisForLFunctions.HTGeometry.OrderOneEnvelopeRootDivision

/-!
# Degree-one positive multiplicative twins

The series `ζ(s)(1 + A p⁻ˢ + p p⁻²ˢ)` has a finite-order entire
regularization and a reflection-even completion. Its gamma presentation
has degree one, conductor `p²` and root number one.
-/

noncomputable section
open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.SelbergClass.PositiveFiniteEuler

/-- Entire continuation of `(s-1)ζ(s)`, expressed through Xi and reciprocal Gamma. -/
private def zetaRegularization (s : ℂ) : ℂ :=
  RHTower.riemannXi s * (Real.pi : ℂ) ^ (s / 2) *
    GaloisForLFunctions.reciprocalGammaEntire (s / 2 + 1)

private theorem differentiable_zetaRegularization : Differentiable ℂ zetaRegularization := by
  have hpow : Differentiable ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (s / 2)) :=
    (differentiable_id.div_const 2).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hrec : Differentiable ℂ (fun s : ℂ =>
      GaloisForLFunctions.reciprocalGammaEntire (s / 2 + 1)) :=
    Complex.differentiable_one_div_Gamma.comp ((differentiable_id.div_const 2).add_const 1)
  exact (RHTower.differentiable_riemannXi.mul hpow).mul hrec

private theorem zetaRegularization_eq {s : ℂ} (hs : s ≠ 1) :
    zetaRegularization s = (s - 1) * riemannZeta s := by
  have hnum : (s - 1) * (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) =
      2 * RHTower.riemannXi s := by
    rw [RHTower.riemannXi]
    field_simp [sub_ne_zero.mpr hs.symm]
    ring
  have hpi : (Real.pi : ℂ) ^ (-s / 2) = ((Real.pi : ℂ) ^ (s / 2))⁻¹ := by
    rw [neg_div, Complex.cpow_neg]
  rw [riemannZeta_eq_mul_completedRiemannZeta₀, ← mul_div_assoc, hnum, hpi,
    zetaRegularization, GaloisForLFunctions.reciprocalGammaEntire]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

private theorem zetaRegularization_eq_poleUnit : zetaRegularization = RHTower.zetaPoleUnit := by
  have hZ := Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_zetaRegularization
  have hP := Complex.analyticOnNhd_univ_iff_differentiable.mpr RHTower.differentiable_zetaPoleUnit
  apply hZ.eq_of_eventuallyEq hP (x := (2 : ℂ))
  filter_upwards [isOpen_compl_singleton.mem_nhds (by norm_num : (2 : ℂ) ≠ 1)] with s hs
  exact (zetaRegularization_eq hs).trans (RHTower.zetaPoleUnit_of_ne hs).symm

private theorem orderOneEnvelope_zetaRegularization : OrderOneEnvelope zetaRegularization := by
  have hpow : OrderOneEnvelope (fun s : ℂ => (Real.pi : ℂ) ^ (s / 2)) := by
    refine (orderOneEnvelope_exp_mul (Complex.log (Real.pi : ℂ) / 2)).congr fun s => ?_
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    congr 1
    ring
  have hrec : OrderOneEnvelope (fun s : ℂ => GaloisForLFunctions.reciprocalGammaEntire (s / 2 + 1)) :=
    (RHTower.orderOneEnvelope_reciprocalGammaEntire.comp_affine (1 / 2) 1).congr
      fun s => by rw [one_div_mul_eq_div]
  exact (RHTower.orderOneEnvelope_riemannXi.mul hpow).mul hrec

/-- Pole-cleared continuation of the positive finite-factor series. -/
def regularized (p : ℕ) (A : ℝ) (s : ℂ) : ℂ :=
  zetaRegularization s * localFactor p A s

theorem differentiable_localFactor {p : ℕ} (hp : p ≠ 0) (A : ℝ) :
    Differentiable ℂ (localFactor p A) := by
  have he : Differentiable ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (.inl (by exact_mod_cast hp))
  exact ((he.const_mul (A : ℂ)).const_add 1).add ((he.pow 2).const_mul (p : ℂ))

theorem differentiable_regularized {p : ℕ} (hp : p ≠ 0) (A : ℝ) :
    Differentiable ℂ (regularized p A) :=
  differentiable_zetaRegularization.mul (differentiable_localFactor hp A)

theorem regularized_eq {p : ℕ} (A : ℝ) {s : ℂ} (hs : s ≠ 1) :
    regularized p A s = (s - 1) * (localFactor p A s * riemannZeta s) := by
  rw [regularized, zetaRegularization_eq hs]
  ring

/-- The pole is simple: its residue is the positive finite Euler factor at one. -/
theorem regularized_one (p : ℕ) (A : ℝ) : regularized p A 1 = localFactor p A 1 := by
  rw [regularized, zetaRegularization_eq_poleUnit, RHTower.zetaPoleUnit_one, one_mul]

theorem orderOneEnvelope_regularized {p : ℕ} (hp : p ≠ 0) (A : ℝ) :
    OrderOneEnvelope (regularized p A) := by
  have he := orderOneEnvelope_natCast_cpow_neg hp
  have hlocal : OrderOneEnvelope (localFactor p A) :=
    ((orderOneEnvelope_const 1).add (he.const_mul (A : ℂ))).add
      ((he.mul he).const_mul (p : ℂ)) |>.congr fun s => by rw [localFactor, pow_two]
  exact orderOneEnvelope_zetaRegularization.mul hlocal

/-- Finite-order entire regularization for the ordinary Dirichlet series. -/
def entireRegularization {p : ℕ} (hp : p ≠ 0) (A : ℝ) : RHTower.EntireFiniteOrder where
  toFun := regularized p A
  analytic := Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_regularized hp A)
  growth := by
    obtain ⟨C, hC, hbound⟩ := orderOneEnvelope_regularized hp A
    refine ⟨Real.exp (2 * C), 2 * C, 2, Real.exp_pos _, by positivity, by norm_num, ?_⟩
    intro z
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 + ‖z‖)
    have hmul := mul_le_mul_of_nonneg_left hlog
      (mul_nonneg hC.le (by positivity : (0 : ℝ) ≤ 1 + ‖z‖))
    have hexp : orderOneWeight C z ≤ 2 * C + 2 * C * ‖z‖ ^ 2 := by
      unfold orderOneWeight
      nlinarith only [hmul, mul_nonneg hC.le (sq_nonneg (1 - ‖z‖))]
    rw [Real.rpow_two]
    calc ‖regularized p A z‖ ≤ Real.exp (orderOneWeight C z) := hbound z
      _ ≤ Real.exp (2 * C + 2 * C * ‖z‖ ^ 2) := Real.exp_le_exp.mpr hexp
      _ = Real.exp (2 * C) * Real.exp (2 * C * ‖z‖ ^ 2) := Real.exp_add _ _

def continuation {p : ℕ} (hp : p ≠ 0) (A : ℝ) : RHTower.SelbergAnalyticContinuation where
  poleOrder := 1
  regularized := entireRegularization hp A

@[simp] theorem continuation_value {p : ℕ} (hp : p ≠ 0) (A : ℝ) (s : ℂ) :
    (continuation hp A).value s = regularized p A s / (s - 1) := by
  simp only [continuation, RHTower.SelbergAnalyticContinuation.value,
    entireRegularization, pow_one]

theorem continuation_eq {p : ℕ} (hp : p ≠ 0) (A : ℝ) {s : ℂ} (hs : s ≠ 1) :
    (continuation hp A).value s = localFactor p A s * riemannZeta s := by
  rw [continuation_value, regularized_eq A hs]
  exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs)

/-- Reflection balances the two endpoints of the finite factor. -/
def completedFactor (p : ℕ) (A : ℝ) (s : ℂ) : ℂ :=
  (p : ℂ) ^ s + A + (p : ℂ) ^ (1 - s)

theorem completedFactor_one_sub (p : ℕ) (A : ℝ) (s : ℂ) :
    completedFactor p A (1 - s) = completedFactor p A s := by
  simp only [completedFactor, sub_sub_cancel]
  ring

theorem cpow_mul_localFactor {p : ℕ} (hp : p ≠ 0) (A : ℝ) (s : ℂ) :
    (p : ℂ) ^ s * localFactor p A s = completedFactor p A s := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have ht : (p : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (.inl hpC)
  rw [localFactor, completedFactor, cpow_sub hpC, cpow_one, cpow_neg]
  field_simp [ht]
  ring

/-- The zeta completion with its balanced reciprocal factor. -/
def completed (p : ℕ) (A : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta s * completedFactor p A s

theorem completed_one_sub (p : ℕ) (A : ℝ) (s : ℂ) :
    completed p A (1 - s) = completed p A s := by
  rw [completed, completed, completedRiemannZeta_one_sub, completedFactor_one_sub]

/-- Gamma data of degree one and conductor `p²`. -/
def gammaData {p : ℕ} (hp : 0 < p) : RHTower.SelbergGammaData where
  Q := (p : ℝ) * Real.exp (-(Real.log Real.pi) / 2)
  Q_pos := mul_pos (by exact_mod_cast hp) (Real.exp_pos _)
  rank := 1
  lambda := fun _ => 1 / 2
  lambda_pos := fun _ => by norm_num
  mu := fun _ => 0
  mu_re_nonneg := fun _ => le_refl 0
  rootNumber := 1
  rootNumber_norm := by norm_num

theorem gammaFactor_eq {p : ℕ} (hp : 0 < p) (s : ℂ) :
    (gammaData hp).gammaFactor s = (p : ℂ) ^ s * Gammaℝ s := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hlog : Complex.log (((p : ℝ) * Real.exp (-(Real.log Real.pi) / 2) : ℝ) : ℂ) =
      (Real.log p : ℂ) - (Real.log Real.pi : ℂ) / 2 := by
    rw [← Complex.ofReal_log (mul_pos hpR (Real.exp_pos _)).le,
      Real.log_mul hpR.ne' (Real.exp_ne_zero _), Real.log_exp]
    push_cast
    ring
  simp only [RHTower.SelbergGammaData.gammaFactor, gammaData, Pi.mul_apply,
    Finset.prod_apply, Fin.prod_univ_one, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, one_div_mul_eq_div, zero_add, add_zero]
  rw [Gammaℝ, cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (mul_pos hpR (Real.exp_pos _)).ne'), hlog,
    cpow_def_of_ne_zero hpC, cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    ← Complex.natCast_log, ← Complex.ofReal_log Real.pi_pos.le, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

theorem gammaData_degree {p : ℕ} (hp : 0 < p) : (gammaData hp).degree = 1 := by
  norm_num [RHTower.SelbergGammaData.degree, gammaData]

theorem gammaData_conductor {p : ℕ} (hp : 0 < p) : (gammaData hp).conductor = (p : ℝ) ^ 2 := by
  have he : Real.exp (-Real.log Real.pi / 2) ^ 2 = Real.pi⁻¹ := by
    rw [pow_two, ← Real.exp_add]
    rw [show -Real.log Real.pi / 2 + -Real.log Real.pi / 2 = -Real.log Real.pi by ring,
      Real.exp_neg, Real.exp_log Real.pi_pos]
  rw [RHTower.SelbergGammaData.conductor, gammaData_degree]
  simp only [gammaData, Real.rpow_one, Fin.prod_univ_one]
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
  rw [mul_pow, he]
  field_simp [Real.pi_ne_zero]

theorem regularized_eq_mul_lSeries {p : ℕ} (hp : p.Prime) (A : ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    regularized p A s = (s - 1) * LSeries (arithmeticCoeffs p A) s := by
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
  rw [regularized_eq A hs1, (lSeriesHasSum hp A hs).LSeries_eq]

private theorem regularized_conjugate {p : ℕ} (hp : p.Prime) (A : ℝ) (s : ℂ) :
    star (regularized p A (star s)) = regularized p A s := by
  have hcoeff : RHTower.selbergArithmeticFunctionConjugate (arithmeticCoeffs p A) =
      arithmeticCoeffs p A := by
    ext n
    simp only [RHTower.selbergArithmeticFunctionConjugate_apply, arithmeticCoeffs_apply,
      Complex.star_def, Complex.conj_ofReal]
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
  have hlocal : (fun z : ℂ => star (regularized p A (star z))) =ᶠ[𝓝 (2 : ℂ)]
      regularized p A := by
    filter_upwards [hopen.mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hzstar : 1 < (star z).re := by simpa using hz
    rw [regularized_eq_mul_lSeries hp A hzstar, regularized_eq_mul_lSeries hp A hz]
    change (starRingEnd ℂ) ((star z - 1) * LSeries (arithmeticCoeffs p A) (star z)) = _
    have hL : star (LSeries (arithmeticCoeffs p A) (star z)) =
        LSeries (arithmeticCoeffs p A) z := by
      rw [← RHTower.lSeries_conjugate, hcoeff]
    rw [map_mul, map_sub, map_one]
    change (star (star z) - 1) * star (LSeries (arithmeticCoeffs p A) (star z)) = _
    rw [star_star, hL]
  exact congrFun ((entireRegularization hp.ne_zero A).conjugate.analytic.eq_of_eventuallyEq
    (entireRegularization hp.ne_zero A).analytic hlocal) s

private theorem representedCompleted_conjugate {p : ℕ} (hp : p.Prime) (A : ℝ) (s : ℂ) :
    star (RHTower.selbergCompletedValue (gammaData hp.pos) (continuation hp.ne_zero A) (star s)) =
      RHTower.selbergCompletedValue (gammaData hp.pos) (continuation hp.ne_zero A) s := by
  have hgself : (gammaData hp.pos).conjugate = gammaData hp.pos := by
    simp [gammaData, RHTower.SelbergGammaData.conjugate]
  have hg : star ((gammaData hp.pos).gammaFactor (star s)) =
      (gammaData hp.pos).gammaFactor s := by
    rw [← RHTower.SelbergGammaData.conjugate_gammaFactor, hgself]
  have hc : star ((continuation hp.ne_zero A).value (star s)) =
      (continuation hp.ne_zero A).value s := by
    rw [continuation_value, continuation_value]
    change (starRingEnd ℂ) (regularized p A (star s) / (star s - 1)) = _
    rw [map_div₀, map_sub, map_one]
    change star (regularized p A (star s)) / (star (star s) - 1) = _
    rw [regularized_conjugate hp, star_star]
  change (starRingEnd ℂ) ((gammaData hp.pos).gammaFactor (star s) *
    (continuation hp.ne_zero A).value (star s)) = _
  rw [map_mul]
  exact congrArg₂ (· * ·) hg hc

private theorem representedCompleted_eq {p : ℕ} (hp : p.Prime) (A : ℝ)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΓ : Gammaℝ s ≠ 0) :
    RHTower.selbergCompletedValue (gammaData hp.pos) (continuation hp.ne_zero A) s =
      completed p A s := by
  rw [RHTower.selbergCompletedValue, gammaFactor_eq, continuation_eq hp.ne_zero A hs1,
    riemannZeta_def_of_ne_zero hs0, completed]
  calc (p : ℂ) ^ s * Gammaℝ s *
      (localFactor p A s * (completedRiemannZeta s / Gammaℝ s)) =
      completedRiemannZeta s * ((p : ℂ) ^ s * localFactor p A s) := by field_simp
    _ = completedRiemannZeta s * completedFactor p A s := by rw [cpow_mul_localFactor hp.ne_zero]

/-- The scalar functional equation holds for the pole-safe continuation. -/
theorem functionalEquation {p : ℕ} (hp : p.Prime) (A : ℝ) :
    RHTower.selbergCompletedValue (gammaData hp.pos) (continuation hp.ne_zero A) =ᶠ[codiscrete ℂ]
      fun s => (gammaData hp.pos).rootNumber * RHTower.selbergConjugateReflection
        (RHTower.selbergCompletedValue (gammaData hp.pos) (continuation hp.ne_zero A)) s := by
  let g : ℂ → ℂ := fun s => reciprocalGammaEntire (s / 2) *
    reciprocalGammaEntire ((1 - s) / 2)
  have hd : Differentiable ℂ reciprocalGammaEntire := Complex.differentiable_one_div_Gamma
  have hg : AnalyticOnNhd ℂ g univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((hd.comp (differentiable_id.div_const 2)).mul
        (hd.comp (((differentiable_const (1 : ℂ)).sub differentiable_id).div_const 2)))
  have hgzero : ¬ Set.EqOn g 0 univ := by
    intro h
    have hΓ : Complex.Gamma (1 / 4 : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
    have hpoint : g (1 / 2) ≠ 0 := by
      dsimp only [g, reciprocalGammaEntire]
      norm_num only [show (1 / 2 : ℂ) / 2 = 1 / 4 by ring,
        show ((1 : ℂ) - 1 / 2) / 2 = 1 / 4 by ring]
      exact mul_ne_zero (inv_ne_zero hΓ) (inv_ne_zero hΓ)
    exact hpoint (h (mem_univ _))
  have hgood : ∀ᶠ s in codiscrete ℂ, g s ≠ 0 :=
    (hg.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left hgzero
  have hzero : (singleton (0 : ℂ))ᶜ ∈ codiscrete ℂ :=
    compl_mem_codiscrete_iff.mpr ⟨isClosed_singleton, subsingleton_singleton.isDiscrete⟩
  have hone : (singleton (1 : ℂ))ᶜ ∈ codiscrete ℂ :=
    compl_mem_codiscrete_iff.mpr ⟨isClosed_singleton, subsingleton_singleton.isDiscrete⟩
  have gamma_nonzero {z : ℂ} (hz : reciprocalGammaEntire (z / 2) ≠ 0) : Gammaℝ z ≠ 0 := by
    rw [Gammaℝ]
    exact mul_ne_zero (cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (fun h => hz (by simp only [reciprocalGammaEntire, h, inv_zero]))
  filter_upwards [hgood, hzero, hone] with s hgs hs0 hs1
  have hs0' : s ≠ 0 := hs0
  have hs1' : s ≠ 1 := hs1
  have hΓs : Gammaℝ s ≠ 0 := gamma_nonzero (ne_zero_of_mul_ne_zero_left hgs)
  have hΓ1s : Gammaℝ (1 - s) ≠ 0 := gamma_nonzero (ne_zero_of_mul_ne_zero_right hgs)
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1'.symm
  have h1s1 : 1 - s ≠ 1 := by
    intro h
    apply hs0'
    simpa using congrArg (fun w : ℂ => 1 - w) h
  change _ = 1 * _
  rw [one_mul, RHTower.selbergConjugateReflection,
    show 1 - star s = star (1 - s) by simp, representedCompleted_conjugate hp,
    representedCompleted_eq hp A hs0' hs1' hΓs,
    representedCompleted_eq hp A h1s0 h1s1 hΓ1s, completed_one_sub]

/-- Positive finite Euler modifications are genuine degree-one members of the extended class. -/
def extendedClass {p : ℕ} (hp : p.Prime) (A : ℝ) : RHTower.ExtendedSelbergClass where
  coeff := arithmeticCoeffs p A
  coeff_ne_zero := by
    intro h
    have h1 := congrArg (fun f : ArithmeticFunction ℂ => f 1) h
    simpa only [arithmeticCoeffs_apply, coeff_one hp, Complex.ofReal_one,
      ArithmeticFunction.zero_apply, one_ne_zero] using h1
  lSeriesSummable := fun _ hs => (lSeriesHasSum hp A hs).LSeriesSummable
  continuation := continuation hp.ne_zero A
  lSeries_eq_value := by
    intro s hs
    rw [(lSeriesHasSum hp A hs).LSeries_eq,
      continuation_eq hp.ne_zero A (by intro h; subst s; norm_num at hs)]
  gammaData := gammaData hp.pos
  functionalEquation := functionalEquation hp A

theorem extendedClass_degree {p : ℕ} (hp : p.Prime) (A : ℝ) :
    (extendedClass hp A).presentationDegree = 1 := gammaData_degree hp.pos

theorem extendedClass_conductor {p : ℕ} (hp : p.Prime) (A : ℝ) :
    (extendedClass hp A).presentationConductor = (p : ℝ) ^ 2 := gammaData_conductor hp.pos

end GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
