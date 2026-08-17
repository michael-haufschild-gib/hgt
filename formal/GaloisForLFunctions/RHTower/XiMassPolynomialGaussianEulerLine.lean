import GaloisForLFunctions.RHTower.XiMassPolynomialEulerContourSourceIdentity

/-!
# The literal Euler-line Gaussian form of the polynomial-filtered heat trace

Rest-energy renormalization turns the relativistic mass multiplier into a Gaussian one at every
point of the Euler bottom line, with an `O(a⁻²)` error that is uniform on compacta and an
exponential envelope uniform in the aperture.  Dominated convergence therefore transports the exact
Euler-contour source identity to the parabolic limit.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Renormalized relativistic exponent at an arbitrary point of the plane. -/
def xiMassPointParabolicExponent (a : ℝ) (z : ℂ) : ℂ :=
  (((2 * a : ℝ) : ℂ)) * (xiMassAnalyticSqrt a z - (a : ℂ))

theorem xiMassAnalyticSqrt_re_nonneg (a : ℝ) (z : ℂ) :
    0 ≤ (xiMassAnalyticSqrt a z).re :=
  le_trans (abs_nonneg z.re) (abs_re_le_xiMassAnalyticSqrt_re a z)

theorem xiMassAnalyticSqrt_add_ne_zero {a : ℝ} (ha : 0 < a) (z : ℂ) :
    xiMassAnalyticSqrt a z + (a : ℂ) ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
  have := xiMassAnalyticSqrt_re_nonneg a z
  linarith

/-- Rest-energy renormalization of the analytic mass test at an arbitrary point. -/
theorem exp_restEnergy_mul_xiMassAnalyticTest (a t : ℝ) (z : ℂ) :
    Complex.exp (((2 * a ^ 2 * t : ℝ) : ℂ)) *
        xiMassAnalyticTest a (((2 * a * t : ℝ) : ℂ)) z =
      Complex.exp (-(t : ℂ) * xiMassPointParabolicExponent a z) := by
  rw [xiMassAnalyticTest, xiMassPointParabolicExponent, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact rational remainder of the renormalized exponent at an arbitrary point. -/
theorem xiMassPointParabolicExponent_eq_sq_sub_remainder {a : ℝ} (ha : 0 < a) (z : ℂ) :
    xiMassPointParabolicExponent a z =
      z ^ 2 - z ^ 4 / (xiMassAnalyticSqrt a z + (a : ℂ)) ^ 2 := by
  let beta : ℂ := xiMassAnalyticSqrt a z
  have hden : beta + (a : ℂ) ≠ 0 := xiMassAnalyticSqrt_add_ne_zero ha z
  have hsq : beta ^ 2 = z ^ 2 + ((a ^ 2 : ℝ) : ℂ) := by
    dsimp only [beta]
    rw [xiMassAnalyticSqrt_sq, xiMassAnalyticArg]
  have hprod : (beta - (a : ℂ)) * (beta + (a : ℂ)) = z ^ 2 := by
    calc (beta - (a : ℂ)) * (beta + (a : ℂ)) = beta ^ 2 - ((a : ℂ) ^ 2) := by ring
      _ = z ^ 2 := by rw [hsq]; push_cast; ring
  have hdiv : beta - (a : ℂ) = z ^ 2 / (beta + (a : ℂ)) := (eq_div_iff hden).2 hprod
  change (((2 * a : ℝ) : ℂ)) * (beta - (a : ℂ)) = z ^ 2 - z ^ 4 / (beta + (a : ℂ)) ^ 2
  calc (((2 * a : ℝ) : ℂ)) * (beta - (a : ℂ)) = z ^ 2 - (beta - (a : ℂ)) ^ 2 := by
        rw [← hprod]; push_cast; ring
    _ = z ^ 2 - z ^ 4 / (beta + (a : ℂ)) ^ 2 := by rw [hdiv]; field_simp [hden]

theorem norm_xiMassPointParabolicExponent_sub_sq_le {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ‖xiMassPointParabolicExponent a z - z ^ 2‖ ≤ ‖z‖ ^ 4 / a ^ 2 := by
  let beta : ℂ := xiMassAnalyticSqrt a z
  have hnn := xiMassAnalyticSqrt_re_nonneg a z
  have hdenNorm : a ≤ ‖beta + (a : ℂ)‖ := by
    calc a ≤ (beta + (a : ℂ)).re := by
          simp only [Complex.add_re, Complex.ofReal_re]
          linarith
      _ ≤ ‖beta + (a : ℂ)‖ := Complex.re_le_norm _
  have hdenSq : a ^ 2 ≤ ‖beta + (a : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg (beta + (a : ℂ))]
  have herr : xiMassPointParabolicExponent a z - z ^ 2 =
      -(z ^ 4 / (beta + (a : ℂ)) ^ 2) := by
    dsimp only [beta]
    rw [xiMassPointParabolicExponent_eq_sq_sub_remainder ha z]
    ring
  rw [herr, norm_neg, norm_div, norm_pow, norm_pow]
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ha) hdenSq

theorem tendsto_xiMassPointParabolicExponent_atTop (z : ℂ) :
    Tendsto (fun a : ℝ => xiMassPointParabolicExponent a z) atTop (𝓝 (z ^ 2)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hb : ∀ᶠ a : ℝ in atTop,
      ‖xiMassPointParabolicExponent a z - z ^ 2‖ ≤ ‖z‖ ^ 4 / a ^ 2 :=
    eventually_atTop.2 ⟨1, fun a ha =>
      norm_xiMassPointParabolicExponent_sub_sq_le (by linarith) z⟩
  have hbase : Tendsto (fun a : ℝ => a ^ 2) atTop atTop := by
    simp
  have hinv : Tendsto (fun a : ℝ => (a ^ 2)⁻¹) atTop (𝓝 0) := hbase.inv_tendsto_atTop
  have hg : Tendsto (fun a : ℝ => ‖z‖ ^ 4 / a ^ 2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul (‖z‖ ^ 4)
  exact squeeze_zero_norm' hb hg

/-- Pointwise rest-energy-renormalized parabolic limit at every point of the plane. -/
theorem tendsto_exp_restEnergy_mul_xiMassAnalyticTest (t : ℝ) (z : ℂ) :
    Tendsto (fun a : ℝ => Complex.exp (((2 * a ^ 2 * t : ℝ) : ℂ)) *
        xiMassAnalyticTest a (((2 * a * t : ℝ) : ℂ)) z) atTop
      (𝓝 (Complex.exp (-(t : ℂ) * z ^ 2))) := by
  have hexp := (tendsto_xiMassPointParabolicExponent_atTop z).const_mul (-(t : ℂ))
  have hcomp := (Complex.continuous_exp.tendsto (-(t : ℂ) * z ^ 2)).comp hexp
  refine hcomp.congr fun a => ?_
  exact (exp_restEnergy_mul_xiMassAnalyticTest a t z).symm

/-! ## A uniform exponential envelope on the Euler bottom line -/

theorem re_xiMassPointParabolicExponent_bottom_bounds {a c : ℝ} (hc : 0 ≤ c) (hca : c < a)
    (x : ℝ) :
    0 ≤ (xiMassAnalyticSqrt a ((x : ℂ) - c * I)).re ∧
      a ^ 2 + x ^ 2 - c ^ 2 ≤ (xiMassAnalyticSqrt a ((x : ℂ) - c * I)).re ^ 2 ∧
      (xiMassAnalyticSqrt a ((x : ℂ) - c * I)).re ≤ a + |x| + c ∧
      (xiMassPointParabolicExponent a ((x : ℂ) - c * I)).re =
        2 * a * ((xiMassAnalyticSqrt a ((x : ℂ) - c * I)).re - a) := by
  have ha : 0 < a := lt_of_le_of_lt hc hca
  set z : ℂ := (x : ℂ) - c * I with hzdef
  have hzre : z.re = x := by simp [hzdef]
  have hzim : z.im = -c := by simp [hzdef]
  have hargre : (xiMassAnalyticArg a z).re = x ^ 2 - c ^ 2 + a ^ 2 := by
    rw [xiMassAnalyticArg_re, hzre, hzim]
    ring
  have hnormge : (xiMassAnalyticArg a z).re ≤ ‖xiMassAnalyticArg a z‖ :=
    Complex.re_le_norm _
  have hznorm : ‖z‖ ^ 2 = x ^ 2 + c ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    ring
  have hnormle : ‖xiMassAnalyticArg a z‖ ≤ x ^ 2 + c ^ 2 + a ^ 2 := by
    have h := norm_add_le (z ^ 2) (((a ^ 2 : ℝ) : ℂ))
    rw [norm_pow] at h
    have hreal : ‖(((a ^ 2 : ℝ) : ℂ))‖ = a ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
    rw [hreal, hznorm] at h
    rw [xiMassAnalyticArg]
    exact h
  have hsq := xiMassAnalyticSqrt_re_sq a z
  have hnn := xiMassAnalyticSqrt_re_nonneg a z
  refine ⟨hnn, ?_, ?_, ?_⟩
  · rw [hsq, hargre] at *
    linarith [hnormge, hargre ▸ hnormge]
  · have hupper : (xiMassAnalyticSqrt a z).re ^ 2 ≤ x ^ 2 + c ^ 2 + a ^ 2 := by
      rw [hsq, hargre]
      linarith
    nlinarith [abs_nonneg x, sq_abs x, hnn, hc, ha.le]
  · rw [xiMassPointParabolicExponent]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, sub_zero]

/-- Uniform-in-aperture linear lower bound for the renormalized exponent on the bottom line. -/
theorem re_xiMassPointParabolicExponent_bottom_ge {a₀ c : ℝ} (hc : 0 ≤ c) (hca₀ : c < a₀)
    {a : ℝ} (ha : a₀ ≤ a) (x : ℝ) :
    a₀ / 2 * |x| - (a₀ / 2 * (2 * a₀ + 2 * c + 2) + 2 * c ^ 2) ≤
      (xiMassPointParabolicExponent a ((x : ℂ) - c * I)).re := by
  have ha₀ : 0 < a₀ := lt_of_le_of_lt hc hca₀
  have haa : 0 < a := lt_of_lt_of_le ha₀ ha
  have hca : c < a := lt_of_lt_of_le hca₀ ha
  obtain ⟨hnn, hlow, hupp, hEre⟩ := re_xiMassPointParabolicExponent_bottom_bounds hc hca x
  rw [hEre]
  set R : ℝ := (xiMassAnalyticSqrt a ((x : ℂ) - c * I)).re with hRdef
  set X : ℝ := |x| with hXdef
  have hX0 : 0 ≤ X := abs_nonneg x
  have hXsq : x ^ 2 = X ^ 2 := (sq_abs x).symm
  rw [hXsq] at hlow
  have hglobal : -2 * c ^ 2 ≤ 2 * a * (R - a) := by
    rcases le_or_gt a R with h | h
    · nlinarith
    · have h1 : 2 * a * (a - R) ≤ 2 * (a ^ 2 - R ^ 2) := by nlinarith [hnn]
      have h2 : a ^ 2 - R ^ 2 ≤ c ^ 2 := by nlinarith [sq_nonneg X]
      nlinarith
  have hT₀ : 0 ≤ a₀ / 2 * (2 * a₀ + 2 * c + 2) := by positivity
  rcases le_or_gt (2 * a₀ + 2 * c + 2) X with hbig | hsmall
  · have hxc : 2 * c ^ 2 ≤ X ^ 2 := by nlinarith
    have hRa : a ≤ R := by nlinarith
    have hden : 0 < 2 * a + X + c := by linarith
    have hpos : 0 ≤ 2 * a * (R - a) := by nlinarith
    have hRA : R + a ≤ 2 * a + X + c := by linarith
    have hmono : 2 * a * (R - a) * (R + a) ≤ 2 * a * (R - a) * (2 * a + X + c) :=
      mul_le_mul_of_nonneg_left hRA hpos
    have hexpand : 2 * a * (R - a) * (R + a) = 2 * a * (R ^ 2 - a ^ 2) := by ring
    have h2 : 2 * a * (X ^ 2 - c ^ 2) ≤ 2 * a * (R ^ 2 - a ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : a * X ^ 2 ≤ 2 * a * (X ^ 2 - c ^ 2) := by nlinarith
    have hbase : a * X ^ 2 ≤ 2 * a * (R - a) * (R + a) := by
      rw [hexpand]; linarith
    have hkey : a * X ^ 2 ≤ 2 * a * (R - a) * (2 * a + X + c) := by linarith
    have hstep1 : a₀ * a + a₀ * c / 2 ≤ a * (a₀ + c / 2) := by nlinarith
    have hstep2 : a * (a₀ + c / 2) ≤ a * (X / 2) := by nlinarith
    have hstep3 : X * (a / 2) ≤ X * (a - a₀ / 2) := by nlinarith
    have hinner : 0 ≤ a * X - a₀ * a - a₀ * X / 2 - a₀ * c / 2 := by nlinarith
    have hlin : a₀ / 2 * X * (2 * a + X + c) ≤ a * X ^ 2 := by
      nlinarith [mul_nonneg hX0 hinner]
    have hconc : a₀ / 2 * X ≤ 2 * a * (R - a) :=
      le_of_mul_le_mul_right (by linarith) hden
    linarith [sq_nonneg c]
  · nlinarith [sq_nonneg c]

/-! ## A global linear majorant for the bottom source factor -/

theorem exists_global_norm_bottomSourceFactor_bound {c : ℝ} (hhalf : 1 / 2 < c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ,
      ‖-I * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (xiMassBottomEulerPoint c x) -
        logDeriv archFactor (xiMassBottomEulerPoint c x))‖ ≤ A + |x| / 2 := by
  set T : ℝ := max 2 (1 / 2 + c) with hTdef
  have hcont : Continuous (fun x : ℝ => ‖logDeriv archFactor (xiMassBottomEulerPoint c x)‖) :=
    (continuous_xiMassBottomArchLogDeriv hhalf).norm
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨|xiMassBottomVonMangoldtBound c| + |xiMassBottomArchGrowthConstant c| + |M|,
    by positivity, fun x => ?_⟩
  have hL := norm_xiMassBottomVonMangoldtLSeries_le (x := x) hhalf
  have hsplit : ‖-I * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (xiMassBottomEulerPoint c x) -
      logDeriv archFactor (xiMassBottomEulerPoint c x))‖ ≤
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (xiMassBottomEulerPoint c x)‖ +
        ‖logDeriv archFactor (xiMassBottomEulerPoint c x)‖ := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact norm_sub_le _ _
  rcases le_or_gt T (|x|) with hbig | hsmall
  · have hA := norm_logDeriv_archFactor_xiMassBottom_le hhalf hbig
    have h1 : xiMassBottomVonMangoldtBound c ≤ |xiMassBottomVonMangoldtBound c| :=
      le_abs_self _
    have h2 : xiMassBottomArchGrowthConstant c ≤ |xiMassBottomArchGrowthConstant c| :=
      le_abs_self _
    have h3 : (0 : ℝ) ≤ |M| := abs_nonneg M
    linarith
  · have hmem : x ∈ Icc (-T) T := by
      constructor <;> [linarith [neg_abs_le x]; linarith [le_abs_self x]]
    have hbound := hM x hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hbound
    have h1 : xiMassBottomVonMangoldtBound c ≤ |xiMassBottomVonMangoldtBound c| :=
      le_abs_self _
    have h3 : M ≤ |M| := le_abs_self M
    have h4 : (0 : ℝ) ≤ |xiMassBottomArchGrowthConstant c| := abs_nonneg _
    have h5 : (0 : ℝ) ≤ |x| / 2 := by positivity
    linarith

/-! ## Dominated convergence on the Euler bottom line -/

/-- Gaussian limit integrand on the Euler bottom line. -/
def xiMassPolyGaussianBottomIntegrand (P : Polynomial ℝ) (c t : ℝ) (x : ℝ) : ℂ :=
  evalRealPolynomial P (((x : ℂ) - c * I) ^ 2) ^ 2 *
    Complex.exp (-(t : ℂ) * ((x : ℂ) - c * I) ^ 2) *
    (-I * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (xiMassBottomEulerPoint c x) -
      logDeriv archFactor (xiMassBottomEulerPoint c x)))

/-- Rest-energy-renormalized relativistic integrand on the Euler bottom line. -/
def xiMassPolyParabolicBottomIntegrand (P : Polynomial ℝ) (a c t : ℝ) (x : ℝ) : ℂ :=
  evalRealPolynomial P (((x : ℂ) - c * I) ^ 2) ^ 2 *
    (Complex.exp (((2 * a ^ 2 * t : ℝ) : ℂ)) *
      xiMassAnalyticTest a (((2 * a * t : ℝ) : ℂ)) ((x : ℂ) - c * I)) *
    (-I * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (xiMassBottomEulerPoint c x) -
      logDeriv archFactor (xiMassBottomEulerPoint c x)))

private theorem continuous_bottomWeight (P : Polynomial ℝ) (c : ℝ) :
    Continuous (fun x : ℝ => evalRealPolynomial P (((x : ℂ) - c * I) ^ 2) ^ 2) := by
  have hQ : Continuous (fun x : ℝ =>
      evalRealPolynomial (xiMassPolySquare P) ((x : ℂ) - c * I)) :=
    (continuous_evalRealPolynomial (xiMassPolySquare P)).comp (by fun_prop)
  exact hQ.congr fun x => evalRealPolynomial_xiMassPolySquare P _

private theorem continuous_bottomSourceFactor {c : ℝ} (hhalf : 1 / 2 < c) :
    Continuous (fun x : ℝ =>
      -I * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (xiMassBottomEulerPoint c x) -
        logDeriv archFactor (xiMassBottomEulerPoint c x))) :=
  continuous_const.mul
    ((continuous_xiMassBottomVonMangoldtLSeries hhalf).sub
      (continuous_xiMassBottomArchLogDeriv hhalf))

theorem continuous_xiMassPolyParabolicBottomIntegrand (P : Polynomial ℝ) {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (t : ℝ) :
    Continuous (xiMassPolyParabolicBottomIntegrand P a c t) := by
  have hmid : Continuous (fun x : ℝ =>
      Complex.exp (((2 * a ^ 2 * t : ℝ) : ℂ)) *
        xiMassAnalyticTest a (((2 * a * t : ℝ) : ℂ)) ((x : ℂ) - c * I)) :=
    continuous_const.mul (continuous_xiMassBottomTest hhalf hca _)
  exact ((continuous_bottomWeight P c).mul hmid).mul (continuous_bottomSourceFactor hhalf)

theorem continuous_xiMassPolyGaussianBottomIntegrand (P : Polynomial ℝ) {c : ℝ}
    (hhalf : 1 / 2 < c) (t : ℝ) :
    Continuous (xiMassPolyGaussianBottomIntegrand P c t) := by
  have hmid : Continuous (fun x : ℝ =>
      Complex.exp (-(t : ℂ) * ((x : ℂ) - c * I) ^ 2)) := by fun_prop
  exact ((continuous_bottomWeight P c).mul hmid).mul (continuous_bottomSourceFactor hhalf)

theorem tendsto_xiMassPolyParabolicBottomIntegrand (P : Polynomial ℝ) (c t : ℝ) (x : ℝ) :
    Tendsto (fun a : ℝ => xiMassPolyParabolicBottomIntegrand P a c t x) atTop
      (𝓝 (xiMassPolyGaussianBottomIntegrand P c t x)) := by
  have hmid := tendsto_exp_restEnergy_mul_xiMassAnalyticTest t ((x : ℂ) - c * I)
  exact (hmid.const_mul (evalRealPolynomial P (((x : ℂ) - c * I) ^ 2) ^ 2)).mul_const _

/-- **Dominated convergence on the Euler line.**  The rest-energy-renormalized relativistic
integrals converge to the Gaussian one. -/
theorem tendsto_integral_xiMassPolyParabolicBottomIntegrand (P : Polynomial ℝ)
    {c t : ℝ} (hhalf : 1 / 2 < c) (ht : 0 < t) :
    Tendsto (fun a : ℝ => ∫ x : ℝ, xiMassPolyParabolicBottomIntegrand P a c t x) atTop
      (𝓝 (∫ x : ℝ, xiMassPolyGaussianBottomIntegrand P c t x)) := by
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hhalf).le
  set a₀ : ℝ := c + 1 with ha₀def
  have hca₀ : c < a₀ := by simp [ha₀def]
  have ha₀ : 0 < a₀ := by linarith
  obtain ⟨A, hA0, hA⟩ := exists_global_norm_bottomSourceFactor_bound hhalf
  set D : ℕ := (xiMassPolySquare P).natDegree with hDdef
  set G : ℝ := xiMassPolyWeightConstant P c with hGdef
  have hG : 0 ≤ G := xiMassPolyWeightConstant_nonneg P hc0
  set kappa : ℝ := t * (a₀ / 2) with hkdef
  have hkappa : 0 < kappa := by rw [hkdef]; positivity
  set C₀ : ℝ := Real.exp (t * (a₀ / 2 * (2 * a₀ + 2 * c + 2) + 2 * c ^ 2)) with hC₀def
  have hC₀ : 0 < C₀ := Real.exp_pos _
  set bound : ℝ → ℝ := fun x =>
    (G * (1 + |x| ^ D)) * (C₀ * Real.exp (-kappa * |x|)) * (A + |x| / 2) with hbdef
  have hboundInt : Integrable bound := by
    have hexp : ∀ x : ℝ, bound x =
        (G * C₀ * A) * (|x| ^ 0 * Real.exp (-kappa * |x|)) +
        (G * C₀ / 2) * (|x| ^ 1 * Real.exp (-kappa * |x|)) +
        (G * C₀ * A) * (|x| ^ D * Real.exp (-kappa * |x|)) +
        (G * C₀ / 2) * (|x| ^ (D + 1) * Real.exp (-kappa * |x|)) := by
      intro x
      rw [hbdef, pow_succ]
      ring
    have hsum : Integrable (fun x : ℝ =>
        (G * C₀ * A) * (|x| ^ 0 * Real.exp (-kappa * |x|)) +
        (G * C₀ / 2) * (|x| ^ 1 * Real.exp (-kappa * |x|)) +
        (G * C₀ * A) * (|x| ^ D * Real.exp (-kappa * |x|)) +
        (G * C₀ / 2) * (|x| ^ (D + 1) * Real.exp (-kappa * |x|))) :=
      ((((HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hkappa).const_mul
          (G * C₀ * A)).add
        ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1 hkappa).const_mul
          (G * C₀ / 2))).add
        ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs D hkappa).const_mul
          (G * C₀ * A))).add
        ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs (D + 1) hkappa).const_mul
          (G * C₀ / 2))
    exact hsum.congr (Filter.Eventually.of_forall fun x => (hexp x).symm)
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound ?_ ?_
    hboundInt ?_
  · filter_upwards [eventually_ge_atTop a₀] with a ha
    exact (continuous_xiMassPolyParabolicBottomIntegrand P hhalf
      (lt_of_lt_of_le hca₀ ha) t).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop a₀] with a ha
    filter_upwards with x
    have hmidNorm : ‖Complex.exp (((2 * a ^ 2 * t : ℝ) : ℂ)) *
        xiMassAnalyticTest a (((2 * a * t : ℝ) : ℂ)) ((x : ℂ) - c * I)‖ ≤
        C₀ * Real.exp (-kappa * |x|) := by
      rw [exp_restEnergy_mul_xiMassAnalyticTest, Complex.norm_exp]
      have hre : (-(t : ℂ) * xiMassPointParabolicExponent a ((x : ℂ) - c * I)).re =
          -t * (xiMassPointParabolicExponent a ((x : ℂ) - c * I)).re := by
        simp [Complex.mul_re]
      rw [hre, hC₀def, hkdef, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hlow := re_xiMassPointParabolicExponent_bottom_ge hc0 hca₀ ha x
      nlinarith [hlow, ht]
    have hw := norm_xiMassPolyBottomWeight_le P hc0 x
    have hs := hA x
    rw [xiMassPolyParabolicBottomIntegrand, norm_mul, norm_mul, hbdef]
    refine mul_le_mul (mul_le_mul hw hmidNorm (norm_nonneg _) (by positivity)) hs
      (norm_nonneg _) (by positivity)
  · filter_upwards with x
    exact tendsto_xiMassPolyParabolicBottomIntegrand P c t x

/-- **(24.119)** The polynomial-square Gaussian Xi heat trace is one absolutely convergent
Euler-line integral of the literal prime--archimedean source. -/
theorem xiPolynomialGaussianHeatTrace_eq_literalEulerLine (P : Polynomial ℝ)
    {c t : ℝ} (hhalf : 1 / 2 < c) (ht : 0 < t) :
    xiPolynomialGaussianHeatTrace P t =
      (2 * Real.pi * I)⁻¹ * (2 * ∫ x : ℝ, xiMassPolyGaussianBottomIntegrand P c t x) := by
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hhalf).le
  have h1 := tendsto_xiMassPolynomialParabolicTrace_atTop P ht
  have h2 := tendsto_integral_xiMassPolyParabolicBottomIntegrand P hhalf ht
  have hscaled := (h2.const_mul (2 : ℂ)).const_mul ((2 * Real.pi * I)⁻¹)
  have h3 : Tendsto (fun a : ℝ => xiMassPolynomialParabolicTrace P a t) atTop
      (𝓝 ((2 * Real.pi * I)⁻¹ *
        (2 * ∫ x : ℝ, xiMassPolyGaussianBottomIntegrand P c t x))) := by
    refine hscaled.congr' ?_
    filter_upwards [eventually_ge_atTop (max 1 (c + 1))] with a ha
    have ha1 : 1 ≤ a := le_trans (le_max_left _ _) ha
    have hca : c < a := lt_of_lt_of_le (by linarith) (le_trans (le_max_right 1 (c + 1)) ha)
    exact (xiMassPolynomialParabolicTrace_eq_literalEulerLine P ha1 hhalf hca ht).symm
  exact tendsto_nhds_unique h1 h3

end

end RHTower
