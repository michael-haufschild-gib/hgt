import GaloisForLFunctions.RHTower.XiMassRadialRiemannLebesgue
import GaloisForLFunctions.RHTower.XiMassPrimeSquareBoundaryResidue

/-!
# Exact asymptotic carrier of the Xi prime-square layer

The critical prime-square coefficients have nonsummable absolute envelope `log p / p`, so
atomwise Riemann--Lebesgue decay cannot be passed through their series.  The obstruction is exactly
the pole of the prime logarithmic Dirichlet series at `s = 1`.  A one-sided contour shift keeps the
regular zeta factor entirely in `Re s ≥ 1`, isolates the pole carrier, and puts the regular boundary
term on the real mass shell where radial Riemann--Lebesgue applies.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Regular zeta logarithmic derivative on the prime-square boundary `Re s = 1`. -/
def xiMassPrimeSquareRegularBoundary (x : ℝ) : ℂ :=
  RHTower.Sieve.zetaLogDerivReg ((1 : ℂ) + 2 * (x : ℂ) * I)

/-- Centered regular part of the prime-square packet. -/
def xiMassPrimeSquareRegularCenteredIntegral (a : ℝ) (tau : ℂ) : ℂ :=
  ∫ x : ℝ, xiMassAnalyticTest a tau (x : ℂ) *
    xiMassPrimeSquareRegularBoundary x

theorem continuous_xiMassPrimeSquareRegularBoundary :
    Continuous xiMassPrimeSquareRegularBoundary := by
  rw [continuous_iff_continuousAt]
  intro x
  let s : ℂ := (1 : ℂ) + 2 * (x : ℂ) * I
  let path : ℝ → ℂ := fun y => (1 : ℂ) + 2 * (y : ℂ) * I
  have hpath : ContinuousAt (fun y : ℝ =>
      (1 : ℂ) + 2 * (y : ℂ) * I) x := by
    fun_prop
  by_cases hx : x = 0
  · subst x
    have hs : s = 1 := by simp [s]
    have hcomp := ContinuousAt.comp_of_eq
      (f := path) (g := RHTower.Sieve.zetaLogDerivReg)
      RHTower.Sieve.differentiableAt_zetaLogDerivReg_one.continuousAt
      hpath (by simp [path])
    change ContinuousAt (RHTower.Sieve.zetaLogDerivReg ∘ path) 0
    exact hcomp
  · have hs1 : s ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      simp [s] at him
      exact hx (by linarith)
    have hz : riemannZeta s ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simp [s, Complex.mul_re]
    have hG := (RHTower.Sieve.zetaResidueUnit_ne_zero_iff hs1).2 hz
    have hcomp := ContinuousAt.comp_of_eq
      (f := path) (g := RHTower.Sieve.zetaLogDerivReg)
      (RHTower.Sieve.differentiableAt_zetaLogDerivReg hG).continuousAt
      hpath (by rfl)
    change ContinuousAt (RHTower.Sieve.zetaLogDerivReg ∘ path) x
    exact hcomp

theorem integrable_xiMassPrimeSquareRegularCenteredIntegrand
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    Integrable (fun x : ℝ =>
      xiMassAnalyticTest a (sigma : ℂ) (x : ℂ) *
        xiMassPrimeSquareRegularBoundary x) := by
  obtain ⟨K, hK, hreg⟩ :=
    exists_norm_zetaLogDerivReg_right_envelope 1 le_rfl
  have hmajor :=
    (integrable_one_add_two_abs_pow_nine_mul_exp_neg hsigma).const_mul K
  apply Integrable.mono' hmajor
  · exact ((continuous_xiMassAnalyticTest_real ha (sigma : ℂ)).mul
      continuous_xiMassPrimeSquareRegularBoundary).aestronglyMeasurable
  · filter_upwards with x
    have htest : ‖xiMassAnalyticTest a (sigma : ℂ) (x : ℂ)‖ ≤
        Real.exp (-(sigma * |x|)) := by
      have hnorm := norm_xiMassAnalyticTest_ofReal_eq
        (a := a) (σ := sigma) (u := 0) (x := x) ha
      rw [show ‖xiMassAnalyticTest a (sigma : ℂ) (x : ℂ)‖ =
          Real.exp (-sigma * xiMassRadialFrequency a x) by
        simpa [xiMassRadialFrequency] using hnorm]
      apply Real.exp_le_exp.mpr
      have hx := abs_le_xiMassRadialFrequency (a := a) x
      nlinarith
    have hregx : ‖xiMassPrimeSquareRegularBoundary x‖ ≤
        K * (1 + 2 * |x|) ^ 9 := by
      have h := hreg 1 le_rfl le_rfl (2 * x)
      simpa [xiMassPrimeSquareRegularBoundary, abs_mul] using h
    rw [norm_mul]
    calc
      ‖xiMassAnalyticTest a (sigma : ℂ) (x : ℂ)‖ *
          ‖xiMassPrimeSquareRegularBoundary x‖ ≤
        Real.exp (-(sigma * |x|)) * (K * (1 + 2 * |x|) ^ 9) :=
          mul_le_mul htest hregx (norm_nonneg _) (Real.exp_nonneg _)
      _ = K * ((1 + 2 * |x|) ^ 9 * Real.exp (-(sigma * |x|))) := by ring
      _ = K * ((1 + 2 * |x|) ^ 9 * Real.exp (-sigma * |x|)) := by ring

/-- Regular boundary packet disperses; it carries no persistent vertical mode. -/
theorem tendsto_xiMassPrimeSquareRegularCenteredIntegral_vertical_atTop_zero
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    Tendsto (fun u : ℝ =>
      xiMassPrimeSquareRegularCenteredIntegral a ((sigma : ℂ) + u * I))
      atTop (𝓝 0) := by
  let f : ℝ → ℂ := fun x =>
    xiMassAnalyticTest a (sigma : ℂ) (x : ℂ) *
      xiMassPrimeSquareRegularBoundary x
  have hf : Integrable f :=
    integrable_xiMassPrimeSquareRegularCenteredIntegrand ha hsigma
  have hradial := tendsto_integral_exp_radialFrequency_mul_atTop_zero ha hf
  refine hradial.congr fun u => ?_
  unfold xiMassPrimeSquareRegularCenteredIntegral
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [f]
  have hzero := xiMassAnalyticTest_ofReal_eq_radial_time ha sigma 0 x
  have hu := xiMassAnalyticTest_ofReal_eq_radial_time ha sigma u x
  have hzero' : xiMassAnalyticTest a (sigma : ℂ) (x : ℂ) =
      Complex.exp (-(sigma * xiMassRadialFrequency a x : ℝ)) := by
    simpa only [ofReal_zero, zero_mul, mul_zero, neg_zero, exp_zero, mul_one,
      add_zero] using hzero
  rw [hzero', hu]
  ring

/-- The regular Euler packet shifts to the centered zero-free boundary without residue. -/
theorem integral_xiMassBottomTest_mul_zetaLogDerivReg_eq_centered
    {a d : ℝ} (hd : 0 ≤ d) (hda : d < a)
    {tau : ℂ} (htau : 0 < tau.re) :
    (∫ x : ℝ, xiMassBottomTest a d tau x *
      RHTower.Sieve.zetaLogDerivReg
        (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)) =
      xiMassPrimeSquareRegularCenteredIntegral a tau := by
  have ha : 0 < a := lt_of_le_of_lt hd hda
  obtain ⟨K, hK, hreg⟩ :=
    exists_norm_zetaLogDerivReg_right_envelope (1 + 2 * d) (by linarith)
  let F : ℂ → ℂ := fun z =>
    xiMassAnalyticTest a tau z *
      RHTower.Sieve.zetaLogDerivReg ((1 : ℂ) + 2 * I * z)
  have hdiff : ∀ z : ℂ, -d ≤ z.im → z.im ≤ 0 → DifferentiableAt ℂ F z := by
    intro z hzlow hzhigh
    have hmem : z ∈ xiMassStrip a := by
      change |z.im| < a
      rw [abs_of_nonpos hzhigh]
      linarith
    have htest := (hasDerivAt_xiMassAnalyticTest ha tau hmem).differentiableAt
    let s : ℂ := (1 : ℂ) + 2 * I * z
    have hsre : s.re = 1 - 2 * z.im := by
      simp [s, Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
    have hsre1 : 1 ≤ s.re := by rw [hsre]; linarith
    have hregdiff : DifferentiableAt ℂ RHTower.Sieve.zetaLogDerivReg s := by
      rcases eq_or_ne s 1 with hs | hs1
      · rw [hs]
        exact RHTower.Sieve.differentiableAt_zetaLogDerivReg_one
      · exact RHTower.Sieve.differentiableAt_zetaLogDerivReg
          ((RHTower.Sieve.zetaResidueUnit_ne_zero_iff hs1).2
            (riemannZeta_ne_zero_of_one_le_re hsre1))
    have hregcomp : DifferentiableAt ℂ
        (fun w : ℂ => RHTower.Sieve.zetaLogDerivReg
          ((1 : ℂ) + 2 * I * w)) z := by
      have hcomp := hregdiff.comp z
        (show DifferentiableAt ℂ (fun w : ℂ => (1 : ℂ) + 2 * I * w) z by
          fun_prop)
      change DifferentiableAt ℂ
        (RHTower.Sieve.zetaLogDerivReg ∘
          fun w : ℂ => (1 : ℂ) + 2 * I * w) z
      simpa only [s] using hcomp
    dsimp only [F]
    apply htest.mul
    exact hregcomp
  have hbound : ∀ z : ℂ, -d ≤ z.im → z.im ≤ 0 →
      ‖F z‖ ≤
        (Real.exp (|tau.im| * d) * K * (2 ^ 9 : ℝ) *
          xiMassShiftedMomentConstant tau.re (1 / 2) 9) *
            Real.exp (-(tau.re / 2 * |z.re|)) := by
    intro z hzlow hzhigh
    have hmem : z ∈ xiMassStrip a := by
      change |z.im| < a
      rw [abs_of_nonpos hzhigh]
      linarith
    have htest0 := norm_xiMassAnalyticTest_le ha htau.le hmem
    have htest : ‖xiMassAnalyticTest a tau z‖ ≤
        Real.exp (|tau.im| * d) * Real.exp (-(tau.re * |z.re|)) := by
      calc
        ‖xiMassAnalyticTest a tau z‖ ≤
            Real.exp (-tau.re * |z.re| + |tau.im| * |z.im|) := htest0
        _ ≤ Real.exp (-tau.re * |z.re| + |tau.im| * d) := by
          apply Real.exp_le_exp.mpr
          have hzabs : |z.im| ≤ d := by rw [abs_of_nonpos hzhigh]; linarith
          nlinarith [mul_le_mul_of_nonneg_left hzabs (abs_nonneg tau.im)]
        _ = Real.exp (|tau.im| * d) * Real.exp (-(tau.re * |z.re|)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    let s : ℂ := (1 : ℂ) + 2 * I * z
    have hsre : s.re = 1 - 2 * z.im := by
      simp [s, Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
    have hsim : s.im = 2 * z.re := by
      simp [s, Complex.mul_re, Complex.mul_im]
    have hslo : 1 ≤ s.re := by rw [hsre]; linarith
    have hshi : s.re ≤ 1 + 2 * d := by rw [hsre]; linarith
    have hregz : ‖RHTower.Sieve.zetaLogDerivReg s‖ ≤
        K * (1 + 2 * |z.re|) ^ 9 := by
      have h := hreg s.re hslo hshi s.im
      have hsform : ((s.re : ℂ) + s.im * I) = s := by
        apply Complex.ext <;> simp
      rw [hsform, hsim] at h
      simpa [abs_mul] using h
    have habsorb := shifted_moment_absorption htau (by norm_num : (0 : ℝ) ≤ 1 / 2)
      9 z.re
    have hpoly : (1 + 2 * |z.re|) ^ 9 * Real.exp (-(tau.re * |z.re|)) ≤
        (2 ^ 9 : ℝ) * xiMassShiftedMomentConstant tau.re (1 / 2) 9 *
          Real.exp (-(tau.re / 2 * |z.re|)) := by
      calc
        (1 + 2 * |z.re|) ^ 9 * Real.exp (-(tau.re * |z.re|)) =
            (2 ^ 9 : ℝ) *
              ((|z.re| + 1 / 2) ^ 9 * Real.exp (-(tau.re * |z.re|))) := by ring
        _ ≤ (2 ^ 9 : ℝ) *
              (xiMassShiftedMomentConstant tau.re (1 / 2) 9 *
                Real.exp (-(tau.re / 2 * |z.re|))) :=
          mul_le_mul_of_nonneg_left habsorb (by positivity)
        _ = _ := by ring
    dsimp only [F]
    rw [norm_mul]
    calc
      ‖xiMassAnalyticTest a tau z‖ *
          ‖RHTower.Sieve.zetaLogDerivReg ((1 : ℂ) + 2 * I * z)‖ ≤
        (Real.exp (|tau.im| * d) * Real.exp (-(tau.re * |z.re|))) *
          (K * (1 + 2 * |z.re|) ^ 9) :=
            mul_le_mul htest hregz (norm_nonneg _)
              (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ = (Real.exp (|tau.im| * d) * K) *
          ((1 + 2 * |z.re|) ^ 9 * Real.exp (-(tau.re * |z.re|))) := by ring
      _ ≤ (Real.exp (|tau.im| * d) * K) *
          ((2 ^ 9 : ℝ) * xiMassShiftedMomentConstant tau.re (1 / 2) 9 *
            Real.exp (-(tau.re / 2 * |z.re|))) :=
        mul_le_mul_of_nonneg_left hpoly (mul_nonneg (Real.exp_nonneg _) hK)
      _ = _ := by ring
  have hshift := integral_horizontal_shift_neg_of_lower_decay hd
    (half_pos htau) hdiff hbound
  have hbottom : (∫ x : ℝ, F ((x : ℂ) - (d : ℂ) * I)) =
      ∫ x : ℝ, xiMassBottomTest a d tau x *
        RHTower.Sieve.zetaLogDerivReg
          (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [F, xiMassBottomTest]
    congr 2
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcenter : (∫ x : ℝ, F (x : ℂ)) =
      xiMassPrimeSquareRegularCenteredIntegral a tau := by
    unfold xiMassPrimeSquareRegularCenteredIntegral
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [F, xiMassPrimeSquareRegularBoundary]
    congr 2
    ring
  rw [hbottom, hcenter] at hshift
  exact hshift

/-- Even prime-power frequency represented by the higher-valuation correction to the square
channel. -/
def xiMassPrimeSquareHigherExponent (pk : Nat.Primes × ℕ) : ℕ :=
  (pk.1 : ℕ) ^ (2 * (pk.2 + 2))

/-- Centered absolutely summable correction accompanying the prime-square pole. -/
def xiMassPrimeSquareHigherCenteredTail (a : ℝ) (tau : ℂ) : ℂ :=
  ∑' pk : Nat.Primes × ℕ,
    xiMassCenteredPrimeAtom a tau (xiMassPrimeSquareHigherExponent pk)

/-- Doubling the Euler exponent on `p^(k+2)` is exactly the centered exponent on
`p^(2(k+2))`; von Mangoldt coefficients agree on both prime powers. -/
theorem xiPrimeLogHigherValuation_term_eq_evenPrimePower
    (s : ℂ) (p : Nat.Primes) (k : ℕ) :
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (2 * s) ((p : ℕ) ^ (k + 2)) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        s ((p : ℕ) ^ (2 * (k + 2))) := by
  let m : ℕ := (p : ℕ) ^ (k + 2)
  have hm0 : m ≠ 0 := (pow_pos p.prop.pos _).ne'
  have hn0 : (p : ℕ) ^ (2 * (k + 2)) ≠ 0 :=
    (pow_pos p.prop.pos _).ne'
  have hpowNat : (p : ℕ) ^ (2 * (k + 2)) = m ^ 2 := by
    dsimp only [m]
    rw [← pow_mul]
    congr 1
    omega
  have harg : ((m : ℂ)).arg = 0 := by
    exact Complex.arg_ofReal_of_nonneg (show 0 ≤ (m : ℝ) by positivity)
  have hpow : ((((p : ℕ) ^ (2 * (k + 2)) : ℕ) : ℂ) ^ s) =
      ((m : ℂ) ^ (2 * s)) := by
    rw [hpowNat, Nat.cast_pow]
    rw [← Complex.cpow_nat_mul'
      (x := (m : ℂ)) (n := 2)
      (by simpa [harg] using Real.pi_pos)
      (by simpa [harg] using Real.pi_pos.le) s]
    congr 1
  rw [LSeries.term_of_ne_zero hm0, LSeries.term_of_ne_zero hn0]
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_pow (by omega)]
  rw [hpow]

theorem summable_xiMassPrimeSquareHigherCriticalWeight :
    Summable (fun pk : Nat.Primes × ℕ =>
      xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 3)) := by
  have h := summable_primeLog_mul_inv_rpow_add 2 (by norm_num)
  apply h.congr
  rintro ⟨p, k⟩
  rw [xiMassPrimePowerCriticalWeight_eq]
  rw [Real.inv_rpow (Nat.cast_nonneg _),
    Real.rpow_neg (Nat.cast_nonneg _)]
  congr 2
  push_cast
  ring

theorem norm_xiMassPrimeSquareHigherCenteredAtom_le
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (u : ℝ) (pk : Nat.Primes × ℕ) :
    ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I)
        (xiMassPrimeSquareHigherExponent pk)‖ ≤
      xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 3) *
        (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  rcases pk with ⟨p, k⟩
  have h := norm_xiMassCenteredPrimeAtom_primePower_le
    ha hsigma u p (2 * k + 3)
  have hexp : 2 * k + 3 + 1 = 2 * (k + 2) := by omega
  simpa only [xiMassPrimeSquareHigherExponent, Prod.fst, Prod.snd, hexp] using h

theorem summable_xiMassPrimeSquareHigherCenteredAtom
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ) :
    Summable (fun pk : Nat.Primes × ℕ =>
      xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I)
        (xiMassPrimeSquareHigherExponent pk)) := by
  apply summable_norm_iff.mp
  exact (summable_xiMassPrimeSquareHigherCriticalWeight.mul_right
      (∫ x : ℝ, Real.exp (-(sigma * |x|)))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (norm_xiMassPrimeSquareHigherCenteredAtom_le ha hsigma u)

/-- Higher-valuation correction has a common summable envelope and therefore disperses. -/
theorem tendsto_xiMassPrimeSquareHigherCenteredTail_vertical_atTop_zero
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    Tendsto (fun u : ℝ =>
      xiMassPrimeSquareHigherCenteredTail a ((sigma : ℂ) + u * I))
      atTop (𝓝 0) := by
  unfold xiMassPrimeSquareHigherCenteredTail
  have hpoint : ∀ pk : Nat.Primes × ℕ,
      Tendsto (fun u : ℝ =>
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I)
          (xiMassPrimeSquareHigherExponent pk)) atTop (𝓝 (0 : ℂ)) := by
    intro pk
    exact tendsto_xiMassCenteredPrimeAtom_vertical_atTop_zero
      ha hsigma (xiMassPrimeSquareHigherExponent pk)
  have hdom : ∀ᶠ u : ℝ in atTop, ∀ pk : Nat.Primes × ℕ,
      ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I)
        (xiMassPrimeSquareHigherExponent pk)‖ ≤
        xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 3) *
          (∫ x : ℝ, Real.exp (-(sigma * |x|))) :=
    Filter.Eventually.of_forall fun u pk =>
      norm_xiMassPrimeSquareHigherCenteredAtom_le ha hsigma u pk
  simpa using tendsto_tsum_of_dominated_convergence
    (summable_xiMassPrimeSquareHigherCriticalWeight.mul_right
      (∫ x : ℝ, Real.exp (-(sigma * |x|)))) hpoint hdom

/-- Bottom-line higher-valuation correction. -/
def xiMassPrimeSquareHigherBottomIntegral
    (a d : ℝ) (tau : ℂ) : ℂ :=
  ∫ x : ℝ, xiMassBottomTest a d tau x *
    xiPrimeLogHigherValuation
      (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)

theorem continuous_xiMassPrimeSquareHigherBottomAtom
    {a d : ℝ} (hd : 0 ≤ d) (hda : d < a) (tau : ℂ)
    (pk : Nat.Primes × ℕ) :
    Continuous (xiMassBottomPrimeAtomIntegrand a d tau
      (xiMassPrimeSquareHigherExponent pk)) := by
  let n : ℕ := xiMassPrimeSquareHigherExponent pk
  have hn : n ≠ 0 := by
    dsimp only [n, xiMassPrimeSquareHigherExponent]
    exact (pow_pos pk.1.prop.pos _).ne'
  have hpoint : xiMassBottomPrimeAtomIntegrand a d tau n =
      fun x =>
        LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
            (1 / 2 : ℂ) n *
          (xiMassBottomTest a d tau x *
            Complex.exp (-(I * (Real.log n : ℂ) *
              ((x : ℂ) - (d : ℂ) * I)))) := by
    funext x
    rw [xiMassBottomPrimeAtomIntegrand,
      xiMassBottomLSeriesTerm_eq_centered_mul_fourierPhase hn]
    ring
  change Continuous (xiMassBottomPrimeAtomIntegrand a d tau n)
  rw [hpoint]
  exact continuous_const.mul
    ((continuous_xiMassBottomTest_of_nonneg hd hda tau).mul
      (Complex.continuous_exp.comp (by fun_prop)))

theorem norm_xiMassPrimeSquareHigherBottomAtom_le
    {a d : ℝ} (hd : 0 ≤ d) (hda : d < a)
    {tau : ℂ} (htau : 0 ≤ tau.re) (pk : Nat.Primes × ℕ) (x : ℝ) :
    ‖xiMassBottomPrimeAtomIntegrand a d tau
        (xiMassPrimeSquareHigherExponent pk) x‖ ≤
      (Real.exp (|tau.im| * d) *
        xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 3)) *
          Real.exp (-(tau.re * |x|)) := by
  let n : ℕ := xiMassPrimeSquareHigherExponent pk
  have hterm :
      ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (xiMassBottomEulerPoint d x) n‖ ≤
        xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 3) := by
    calc
      ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (xiMassBottomEulerPoint d x) n‖ ≤
        ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (1 / 2 : ℂ) n‖ :=
            LSeries.norm_term_le_of_re_le_re _ (by
              simp [xiMassBottomEulerPoint, Complex.mul_re]
              linarith) _
      _ = xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 3) := by
        have hexp : 2 * pk.2 + 3 + 1 = 2 * (pk.2 + 2) := by omega
        rw [xiMassPrimePowerCriticalWeight]
        dsimp only [n, xiMassPrimeSquareHigherExponent]
        rw [hexp]
  rw [xiMassBottomPrimeAtomIntegrand, norm_mul]
  calc
    ‖xiMassBottomTest a d tau x‖ *
        ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (xiMassBottomEulerPoint d x) n‖ ≤
      (Real.exp (|tau.im| * d) * Real.exp (-(tau.re * |x|))) *
        xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 3) :=
          mul_le_mul (norm_xiMassBottomTest_le_of_nonneg hd hda htau)
            hterm (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem integrable_xiMassPrimeSquareHigherBottomAtom
    {a d : ℝ} (hd : 0 ≤ d) (hda : d < a)
    {tau : ℂ} (htau : 0 < tau.re) (pk : Nat.Primes × ℕ) :
    Integrable (xiMassBottomPrimeAtomIntegrand a d tau
      (xiMassPrimeSquareHigherExponent pk)) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic htau).const_mul
      (Real.exp (|tau.im| * d) *
        xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 3)))
    (continuous_xiMassPrimeSquareHigherBottomAtom hd hda tau pk).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x =>
      norm_xiMassPrimeSquareHigherBottomAtom_le hd hda htau.le pk x)

theorem summable_integral_norm_xiMassPrimeSquareHigherBottomAtom
    {a d : ℝ} (hd : 0 ≤ d) (hda : d < a)
    {tau : ℂ} (htau : 0 < tau.re) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ∫ x : ℝ, ‖xiMassBottomPrimeAtomIntegrand a d tau
        (xiMassPrimeSquareHigherExponent pk) x‖) := by
  let E : ℝ := Real.exp (|tau.im| * d)
  let J : ℝ := ∫ x : ℝ, Real.exp (-(tau.re * |x|))
  apply (summable_xiMassPrimeSquareHigherCriticalWeight.mul_left (E * J)).of_nonneg_of_le
    (fun pk => integral_nonneg fun _ => norm_nonneg _)
  intro pk
  have hmajor : Integrable (fun x : ℝ =>
      (E * xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 3)) *
        Real.exp (-(tau.re * |x|))) :=
    (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic htau).const_mul _
  calc
    (∫ x : ℝ, ‖xiMassBottomPrimeAtomIntegrand a d tau
        (xiMassPrimeSquareHigherExponent pk) x‖) ≤
      ∫ x : ℝ,
        (E * xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 3)) *
          Real.exp (-(tau.re * |x|)) :=
      integral_mono
        (integrable_xiMassPrimeSquareHigherBottomAtom hd hda htau pk).norm
        hmajor
        (fun x => by
          simpa only [E] using
            norm_xiMassPrimeSquareHigherBottomAtom_le hd hda htau.le pk x)
    _ = (E * J) * xiMassPrimePowerCriticalWeight pk.1 (2 * pk.2 + 3) := by
      rw [MeasureTheory.integral_const_mul]
      dsimp only [J]
      ring

theorem xiMassPrimeSquareHigherBottomIntegrand_eq_tsum
    (a d : ℝ) (tau : ℂ) (x : ℝ) :
    xiMassBottomTest a d tau x *
        xiPrimeLogHigherValuation
          (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) =
      ∑' pk : Nat.Primes × ℕ,
        xiMassBottomPrimeAtomIntegrand a d tau
          (xiMassPrimeSquareHigherExponent pk) x := by
  unfold xiPrimeLogHigherValuation
  rw [← tsum_mul_left]
  apply tsum_congr
  rintro ⟨p, k⟩
  rw [xiMassBottomPrimeAtomIntegrand, xiMassBottomTest]
  congr 1
  have hs : (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) =
      2 * xiMassBottomEulerPoint d x := by
    unfold xiMassBottomEulerPoint
    push_cast
    ring
  rw [hs, xiPrimeLogHigherValuation_term_eq_evenPrimePower]
  rfl

/-- Higher correction on the Euler line is exactly its centered absolutely summable atom tail. -/
theorem xiMassPrimeSquareHigherBottomIntegral_eq_centeredTail
    {a d : ℝ} (hd : 0 ≤ d) (hda : d < a)
    {tau : ℂ} (htau : 0 < tau.re) :
    xiMassPrimeSquareHigherBottomIntegral a d tau =
      xiMassPrimeSquareHigherCenteredTail a tau := by
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun pk => integrable_xiMassPrimeSquareHigherBottomAtom hd hda htau pk)
    (summable_integral_norm_xiMassPrimeSquareHigherBottomAtom hd hda htau)
  unfold xiMassPrimeSquareHigherBottomIntegral
  rw [show (∫ x : ℝ, xiMassBottomTest a d tau x *
      xiPrimeLogHigherValuation
        (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)) =
      ∫ x : ℝ, ∑' pk : Nat.Primes × ℕ,
        xiMassBottomPrimeAtomIntegrand a d tau
          (xiMassPrimeSquareHigherExponent pk) x by
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      xiMassPrimeSquareHigherBottomIntegrand_eq_tsum a d tau x)]
  rw [hswap.symm]
  unfold xiMassPrimeSquareHigherCenteredTail
  exact tsum_congr fun pk =>
    integral_xiMassBottomPrimeAtom_eq_centered_of_nonneg hd hda htau _

theorem integrable_xiMassBottomTest_mul_zetaLogDerivReg
    {a d : ℝ} (hd : 0 < d) (hda : d < a)
    {tau : ℂ} (htau : 0 < tau.re) :
    Integrable (fun x : ℝ => xiMassBottomTest a d tau x *
      RHTower.Sieve.zetaLogDerivReg
        (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)) := by
  obtain ⟨K, hK, hreg⟩ :=
    exists_norm_zetaLogDerivReg_right_envelope (1 + 2 * d) (by linarith)
  let C : ℝ := Real.exp (|tau.im| * d) * K
  have hmajor :=
    (integrable_one_add_two_abs_pow_nine_mul_exp_neg htau).const_mul C
  apply Integrable.mono' hmajor
  · exact (continuous_xiMassBottomTest_of_nonneg hd.le hda tau).aestronglyMeasurable.mul
      (continuous_zetaLogDerivReg_right_line (by linarith)).aestronglyMeasurable
  · filter_upwards with x
    have htest := norm_xiMassBottomTest_le_of_nonneg
      (x := x) hd.le hda htau.le
    have hregx := hreg (1 + 2 * d) (by linarith) le_rfl (2 * x)
    rw [norm_mul]
    calc
      ‖xiMassBottomTest a d tau x‖ *
          ‖RHTower.Sieve.zetaLogDerivReg
            (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)‖ ≤
        (Real.exp (|tau.im| * d) * Real.exp (-(tau.re * |x|))) *
          (K * (1 + 2 * |x|) ^ 9) := by
            apply mul_le_mul htest
            · simpa [abs_mul] using hregx
            · exact norm_nonneg _
            · positivity
      _ = C * ((1 + 2 * |x|) ^ 9 * Real.exp (-(tau.re * |x|))) := by
        dsimp only [C]
        ring
      _ = C * ((1 + 2 * |x|) ^ 9 * Real.exp (-tau.re * |x|)) := by ring

theorem integrable_xiMassPrimeSquareHigherBottomIntegrand
    {a d : ℝ} (hd : 0 ≤ d) (hda : d < a)
    {tau : ℂ} (htau : 0 < tau.re) :
    Integrable (fun x : ℝ => xiMassBottomTest a d tau x *
      xiPrimeLogHigherValuation
        (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)) := by
  let T : ℝ := ∑' pk : Nat.Primes × ℕ, xiPrimeLogHigherValuationWeight pk
  let C : ℝ := Real.exp (|tau.im| * d) * T
  have hmajor := (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic htau).const_mul C
  apply Integrable.mono' hmajor
  · exact (continuous_xiMassBottomTest_of_nonneg hd hda tau).aestronglyMeasurable.mul
      (aestronglyMeasurable_xiPrimeLogHigherValuation_line (1 + 2 * d))
  · filter_upwards with x
    have htest := norm_xiMassBottomTest_le_of_nonneg
      (x := x) hd hda htau.le
    have hline : 1 ≤ ((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)).re := by
      simp
      linarith
    have hhigh := norm_xiPrimeLogHigherValuation_le hline
    rw [norm_mul]
    calc
      ‖xiMassBottomTest a d tau x‖ *
          ‖xiPrimeLogHigherValuation
            (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)‖ ≤
        (Real.exp (|tau.im| * d) * Real.exp (-(tau.re * |x|))) * T :=
          mul_le_mul htest (by simpa only [T] using hhigh)
            (norm_nonneg _) (by positivity)
      _ = C * Real.exp (-(tau.re * |x|)) := by
        dsimp only [C]
        ring

/-- **Exact pole/regular/tail decomposition of the critical prime-square layer.** -/
theorem xiMassPrimeSquareLayer_eq_pole_add_regular_sub_higher
    {a : ℝ} (ha : 0 < a) {tau : ℂ} (htau : 0 < tau.re) :
    xiMassPrimeSquareLayer a tau =
      (Real.pi / 2 : ℂ) * xiMassAnalyticTest a tau 0 +
        xiMassPrimeSquareRegularCenteredIntegral a tau -
          xiMassPrimeSquareHigherCenteredTail a tau := by
  let d : ℝ := a / 2
  have hd : 0 < d := by dsimp only [d]; positivity
  have hda : d < a := by dsimp only [d]; linarith
  let pole : ℝ → ℂ := fun x => xiMassBottomTest a d tau x *
    (((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1)⁻¹)
  let reg : ℝ → ℂ := fun x => xiMassBottomTest a d tau x *
    RHTower.Sieve.zetaLogDerivReg
      (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)
  let high : ℝ → ℂ := fun x => xiMassBottomTest a d tau x *
    xiPrimeLogHigherValuation
      (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)
  have htauForm : ((tau.re : ℂ) + tau.im * I) = tau := by
    apply Complex.ext <;> simp
  have hpoleInt : Integrable pole := by
    simpa only [pole, htauForm] using
      integrable_xiMassBottomTest_mul_naturalPole htau hd hda tau.im
  have hregInt : Integrable reg :=
    integrable_xiMassBottomTest_mul_zetaLogDerivReg hd hda htau
  have hhighInt : Integrable high :=
    integrable_xiMassPrimeSquareHigherBottomIntegrand hd.le hda htau
  have hpoint (x : ℝ) :
      xiMassBottomTest a d tau x *
          xiPrimeLogDirichlet
            (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) =
        pole x + reg x - high x := by
    have hQ := xiPrimeLogDirichlet_eq_pole_add_regular_sub_higherValuation
      (s := (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)) (by simp; linarith)
    simp only [pole, reg, high]
    rw [hQ]
    ring
  have hintegral :
      (∫ x : ℝ, xiMassBottomTest a d tau x *
          xiPrimeLogDirichlet
            (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)) =
        (∫ x : ℝ, pole x) + (∫ x : ℝ, reg x) - (∫ x : ℝ, high x) := by
    rw [show (∫ x : ℝ, xiMassBottomTest a d tau x *
        xiPrimeLogDirichlet
          (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)) =
      ∫ x : ℝ, pole x + reg x - high x by
        exact integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    calc
      (∫ x : ℝ, pole x + reg x - high x) =
          (∫ x : ℝ, pole x + reg x) - ∫ x : ℝ, high x := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          integral_sub (hpoleInt.add hregInt) hhighInt
      _ = (∫ x : ℝ, pole x) + (∫ x : ℝ, reg x) -
          (∫ x : ℝ, high x) := by
        rw [integral_add hpoleInt hregInt]
  have hpole : (∫ x : ℝ, pole x) =
      (Real.pi / 2 : ℂ) * xiMassAnalyticTest a tau 0 := by
    simpa only [pole, htauForm] using
      integral_xiMassBottomTest_mul_naturalPole ha htau hd hda tau.im
  have hreg : (∫ x : ℝ, reg x) =
      xiMassPrimeSquareRegularCenteredIntegral a tau := by
    simpa only [reg] using
      integral_xiMassBottomTest_mul_zetaLogDerivReg_eq_centered hd.le hda htau
  have hhigh : (∫ x : ℝ, high x) =
      xiMassPrimeSquareHigherCenteredTail a tau := by
    simpa only [high, xiMassPrimeSquareHigherBottomIntegral] using
      xiMassPrimeSquareHigherBottomIntegral_eq_centeredTail hd.le hda htau
  have hlayer := integral_test_mul_xiPrimeLogDirichlet_eq_primeSquareLayer
    (a := a) hd hda htau
  rw [hintegral, hpole, hreg, hhigh] at hlayer
  exact hlayer.symm

/-- Prime-square layer has exactly one persistent vertical mode: its `s=1` pole carrier. -/
theorem tendsto_xiMassPrimeSquareLayer_sub_poleCarrier_atTop_zero
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    Tendsto (fun u : ℝ =>
      xiMassPrimeSquareLayer a ((sigma : ℂ) + u * I) -
        (Real.pi / 2 : ℂ) *
          xiMassAnalyticTest a ((sigma : ℂ) + u * I) 0)
      atTop (𝓝 0) := by
  have hreg :=
    tendsto_xiMassPrimeSquareRegularCenteredIntegral_vertical_atTop_zero ha hsigma
  have hhigh :=
    tendsto_xiMassPrimeSquareHigherCenteredTail_vertical_atTop_zero ha hsigma
  have hlim : Tendsto (fun u : ℝ =>
      xiMassPrimeSquareRegularCenteredIntegral a ((sigma : ℂ) + u * I) -
        xiMassPrimeSquareHigherCenteredTail a ((sigma : ℂ) + u * I))
      atTop (𝓝 0) := by
    simpa using hreg.sub hhigh
  refine hlim.congr' (Filter.Eventually.of_forall fun u => ?_)
  change xiMassPrimeSquareRegularCenteredIntegral a ((sigma : ℂ) + u * I) -
      xiMassPrimeSquareHigherCenteredTail a ((sigma : ℂ) + u * I) =
    xiMassPrimeSquareLayer a ((sigma : ℂ) + u * I) -
      (Real.pi / 2 : ℂ) *
        xiMassAnalyticTest a ((sigma : ℂ) + u * I) 0
  rw [xiMassPrimeSquareLayer_eq_pole_add_regular_sub_higher ha
    (show 0 < (((sigma : ℂ) + u * I)).re by simpa using hsigma)]
  ring

end

end RHTower
