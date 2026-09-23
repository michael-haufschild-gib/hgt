import GaloisForLFunctions.HTGeometry.WaveTraceSpectrum

/-!
# Laplace transform of a wave trace

A single complex frequency contributes the elementary Laplace kernel
`∫₀^∞ sin (gamma * t) e^{-s t} dt = gamma / (s ^ (2 : ℕ) + gamma ^ (2 : ℕ))`,
valid on the half-plane to the right of the frequency's horizontal width.

Summed against a polynomial weight this produces the meromorphic active-pole transform of
the wave trace, whose poles sit exactly at `± i * gamma`.
-/

open Complex Filter MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The elementary sine kernel -/

variable {gamma s : ℂ}

private theorem laplace_exp_re_neg_left (h : |gamma.im| < s.re) :
    (-(gamma * Complex.I) - s).re < 0 := by
  have h1 : (-(gamma * Complex.I) - s).re = gamma.im - s.re := by
    simp [Complex.sub_re, Complex.neg_re, Complex.mul_re]
  rw [h1]
  have := le_abs_self gamma.im
  linarith

private theorem laplace_exp_re_neg_right (h : |gamma.im| < s.re) :
    (gamma * Complex.I - s).re < 0 := by
  have h1 : (gamma * Complex.I - s).re = -gamma.im - s.re := by
    simp [Complex.sub_re, Complex.mul_re]
  rw [h1]
  have := neg_le_abs gamma.im
  linarith

theorem sin_mul_exp_eq (gamma s : ℂ) (t : ℝ) :
    Complex.sin (gamma * t) * Complex.exp (-s * t) =
      (Complex.exp ((-(gamma * Complex.I) - s) * t) -
        Complex.exp ((gamma * Complex.I - s) * t)) * Complex.I / 2 := by
  rw [Complex.sin]
  rw [show (-(gamma * (t : ℂ)) * Complex.I) = (-(gamma * Complex.I)) * (t : ℂ) by ring,
    show (gamma * (t : ℂ) * Complex.I) = (gamma * Complex.I) * (t : ℂ) by ring]
  rw [show ((-(gamma * Complex.I) - s) * (t : ℂ)) =
      (-(gamma * Complex.I)) * (t : ℂ) + (-s * (t : ℂ)) by ring,
    show ((gamma * Complex.I - s) * (t : ℂ)) =
      (gamma * Complex.I) * (t : ℂ) + (-s * (t : ℂ)) by ring]
  rw [Complex.exp_add, Complex.exp_add]
  ring

theorem integrableOn_sin_mul_exp (h : |gamma.im| < s.re) :
    IntegrableOn (fun t : ℝ => Complex.sin (gamma * t) * Complex.exp (-s * t))
      (Ioi (0 : ℝ)) := by
  have h1 := integrableOn_exp_mul_complex_Ioi (laplace_exp_re_neg_left h) 0
  have h2 := integrableOn_exp_mul_complex_Ioi (laplace_exp_re_neg_right h) 0
  have hint : IntegrableOn
      (fun t : ℝ =>
        (Complex.exp ((-(gamma * Complex.I) - s) * t) -
          Complex.exp ((gamma * Complex.I - s) * t)) * Complex.I / 2)
      (Ioi (0 : ℝ)) := ((h1.sub h2).mul_const Complex.I).div_const 2
  refine hint.congr_fun ?_ measurableSet_Ioi
  intro t _
  exact (sin_mul_exp_eq gamma s t).symm

theorem sq_add_sq_ne_zero (h : |gamma.im| < s.re) : s ^ (2 : ℕ) + gamma ^ (2 : ℕ) ≠ 0 := by
  have hleft : s + gamma * Complex.I ≠ 0 := by
    intro hz
    have : (s + gamma * Complex.I).re = 0 := by rw [hz]; simp
    rw [Complex.add_re, Complex.mul_re] at this
    simp at this
    have h2 := le_abs_self gamma.im
    linarith
  have hright : s - gamma * Complex.I ≠ 0 := by
    intro hz
    have : (s - gamma * Complex.I).re = 0 := by rw [hz]; simp
    rw [Complex.sub_re, Complex.mul_re] at this
    simp at this
    have h2 := neg_le_abs gamma.im
    linarith
  have hfac : s ^ (2 : ℕ) + gamma ^ (2 : ℕ) = (s + gamma * Complex.I) * (s - gamma * Complex.I) := by
    linear_combination (gamma ^ (2 : ℕ)) * Complex.I_sq
  rw [hfac]
  exact mul_ne_zero hleft hright

/-- **Elementary sine Laplace kernel.** To the right of the horizontal width of a frequency,
its damped sine integrates to the resolvent kernel. -/
theorem integral_sin_mul_exp (h : |gamma.im| < s.re) :
    (∫ t in Ioi (0 : ℝ), Complex.sin (gamma * t) * Complex.exp (-s * t)) =
      gamma / (s ^ (2 : ℕ) + gamma ^ (2 : ℕ)) := by
  have hleft := laplace_exp_re_neg_left h
  have hright := laplace_exp_re_neg_right h
  have h1 := integrableOn_exp_mul_complex_Ioi hleft 0
  have h2 := integrableOn_exp_mul_complex_Ioi hright 0
  have hcongr : (∫ t in Ioi (0 : ℝ), Complex.sin (gamma * t) * Complex.exp (-s * t)) =
      ∫ t in Ioi (0 : ℝ),
        (Complex.exp ((-(gamma * Complex.I) - s) * t) -
          Complex.exp ((gamma * Complex.I - s) * t)) * Complex.I / 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    exact sin_mul_exp_eq gamma s t
  rw [hcongr]
  rw [integral_div, integral_mul_const, integral_sub h1 h2,
    integral_exp_mul_complex_Ioi hleft, integral_exp_mul_complex_Ioi hright]
  have hane : (-(gamma * Complex.I) - s) ≠ 0 := fun hz => by
    rw [hz] at hleft; simp at hleft
  have hbne : (gamma * Complex.I - s) ≠ 0 := fun hz => by
    rw [hz] at hright; simp at hright
  have hsq := sq_add_sq_ne_zero h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring_nf
  linear_combination (-(2 * gamma * s ^ (2 : ℕ))) * Complex.I_sq



/-! ## Shifted sine kernel -/

theorem integrableOn_sin_mul_exp_Ioi (h : |gamma.im| < s.re) (T : ℝ) :
    IntegrableOn (fun t : ℝ => Complex.sin (gamma * t) * Complex.exp (-s * t))
      (Ioi T) := by
  have h1 := integrableOn_exp_mul_complex_Ioi (laplace_exp_re_neg_left h) T
  have h2 := integrableOn_exp_mul_complex_Ioi (laplace_exp_re_neg_right h) T
  have hint : IntegrableOn
      (fun t : ℝ =>
        (Complex.exp ((-(gamma * Complex.I) - s) * t) -
          Complex.exp ((gamma * Complex.I - s) * t)) * Complex.I / 2)
      (Ioi T) := ((h1.sub h2).mul_const Complex.I).div_const 2
  refine hint.congr_fun ?_ measurableSet_Ioi
  intro t _
  exact (sin_mul_exp_eq gamma s t).symm

/-- **Shifted sine Laplace kernel.** Starting the damped sine integral at time `T` keeps the
resolvent denominator and produces the phase numerator `s sin (gamma T) + gamma cos (gamma T)`,
which equals `gamma` at the resolvent poles. -/
theorem integral_sin_mul_exp_Ioi (h : |gamma.im| < s.re) (T : ℝ) :
    (∫ t in Ioi T, Complex.sin (gamma * t) * Complex.exp (-s * t)) =
      Complex.exp (-s * T) *
        (s * Complex.sin (gamma * T) + gamma * Complex.cos (gamma * T)) /
          (s ^ (2 : ℕ) + gamma ^ (2 : ℕ)) := by
  have hleft := laplace_exp_re_neg_left h
  have hright := laplace_exp_re_neg_right h
  have h1 := integrableOn_exp_mul_complex_Ioi hleft T
  have h2 := integrableOn_exp_mul_complex_Ioi hright T
  have hcongr : (∫ t in Ioi T, Complex.sin (gamma * t) * Complex.exp (-s * t)) =
      ∫ t in Ioi T,
        (Complex.exp ((-(gamma * Complex.I) - s) * t) -
          Complex.exp ((gamma * Complex.I - s) * t)) * Complex.I / 2 :=
    setIntegral_congr_fun measurableSet_Ioi (fun t _ => sin_mul_exp_eq gamma s t)
  rw [hcongr, integral_div, integral_mul_const, integral_sub h1 h2,
    integral_exp_mul_complex_Ioi hleft, integral_exp_mul_complex_Ioi hright]
  have hane : (-(gamma * Complex.I) - s) ≠ 0 := fun hz => by
    rw [hz] at hleft; simp at hleft
  have hbne : (gamma * Complex.I - s) ≠ 0 := fun hz => by
    rw [hz] at hright; simp at hright
  have hsq := sq_add_sq_ne_zero h
  have hexp1 : Complex.exp ((-(gamma * Complex.I) - s) * T) =
      Complex.exp (-s * T) * Complex.exp (-(gamma * T) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hexp2 : Complex.exp ((gamma * Complex.I - s) * T) =
      Complex.exp (-s * T) * Complex.exp (gamma * T * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp1, hexp2, Complex.sin, Complex.cos]
  set A : ℂ := Complex.exp (-(gamma * (T : ℂ)) * Complex.I) with hA
  set B : ℂ := Complex.exp (gamma * (T : ℂ) * Complex.I) with hB
  set E : ℂ := Complex.exp (-s * (T : ℂ)) with hE
  field_simp
  ring_nf
  linear_combination
    (Complex.I * E * gamma ^ (2 : ℕ) * s * (A - B) - E * gamma * s ^ (2 : ℕ) * (A + B)) * Complex.I_sq

/-! ## Termwise Laplace transform of the wave trace -/

namespace WaveSpectrum

variable {G : Type*} [Countable G] (S : WaveSpectrum G)

/-- Coefficient of a frequency in the wave trace. -/
def traceCoeff (P : Polynomial ℝ) (g : G) : ℂ :=
  Polynomial.aeval ((S.gamma g ^ (2 : ℕ)) ⁻¹) P / S.gamma g ^ (3 : ℕ)

/-- Phase numerator produced by starting the Laplace integral at time `T`. -/
def poleNumer (T : ℝ) (s : ℂ) (g : G) : ℂ :=
  Complex.exp (-s * T) *
    (s * Complex.sin (S.gamma g * T) + S.gamma g * Complex.cos (S.gamma g * T))

/-- One resolvent term of the active-pole transform. -/
def poleTerm (P : Polynomial ℝ) (T : ℝ) (s : ℂ) (g : G) : ℂ :=
  S.traceCoeff P g * S.poleNumer T s g / (s ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ))

/-- One damped wave-trace term. -/
def dampedTerm (P : Polynomial ℝ) (s : ℂ) (t : ℝ) (g : G) : ℂ :=
  S.traceTerm P t g * Complex.exp (-s * t)

omit [Countable G] in
theorem dampedTerm_eq (P : Polynomial ℝ) (s : ℂ) (t : ℝ) (g : G) :
    S.dampedTerm P s t g =
      S.traceCoeff P g * (Complex.sin (S.gamma g * t) * Complex.exp (-s * t)) := by
  simp only [dampedTerm, traceTerm, traceCoeff]
  ring

omit [Countable G] in
theorem integrableOn_dampedTerm (P : Polynomial ℝ) {s : ℂ} (hs : S.width < s.re) (T : ℝ)
    (g : G) :
    IntegrableOn (fun t : ℝ => S.dampedTerm P s t g) (Ioi T) := by
  have hIm : |(S.gamma g).im| < s.re := lt_of_le_of_lt (S.im_le g) hs
  have hbase := integrableOn_sin_mul_exp_Ioi (gamma := S.gamma g) (s := s) hIm T
  have hconst : IntegrableOn
      (fun t : ℝ => S.traceCoeff P g *
        (Complex.sin (S.gamma g * t) * Complex.exp (-s * t))) (Ioi T) :=
    hbase.const_mul (S.traceCoeff P g)
  refine hconst.congr_fun ?_ measurableSet_Ioi
  intro t _
  exact (S.dampedTerm_eq P s t g).symm

omit [Countable G] in
/-- Exact Laplace transform of one damped wave-trace term started at time `T`. -/
theorem integral_dampedTerm (P : Polynomial ℝ) {s : ℂ} (hs : S.width < s.re) (T : ℝ) (g : G) :
    (∫ t in Ioi T, S.dampedTerm P s t g) = S.poleTerm P T s g := by
  have hIm : |(S.gamma g).im| < s.re := lt_of_le_of_lt (S.im_le g) hs
  have hsq := sq_add_sq_ne_zero (gamma := S.gamma g) (s := s) hIm
  have hcongr : (∫ t in Ioi T, S.dampedTerm P s t g) =
      ∫ t in Ioi T,
        S.traceCoeff P g * (Complex.sin (S.gamma g * t) * Complex.exp (-s * t)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun t _ => S.dampedTerm_eq P s t g)
  rw [hcongr, integral_const_mul, integral_sin_mul_exp_Ioi hIm, poleTerm, poleNumer]
  field_simp

omit [Countable G] in
theorem norm_dampedTerm_le (P : Polynomial ℝ) (s : ℂ) {t : ℝ} (ht : 0 < t) (g : G) :
    ‖S.dampedTerm P s t g‖ ≤
      polyBallBound P (S.lower⁻¹ ^ (2 : ℕ)) * ‖S.gamma g‖⁻¹ ^ (3 : ℕ) *
        Real.exp ((S.width - s.re) * t) := by
  rw [dampedTerm, norm_mul, Complex.norm_exp]
  have hre : (-s * (t : ℂ)).re = -(s.re * t) := by simp [Complex.mul_re]
  rw [hre]
  have hterm := S.norm_traceTerm_le P t g
  rw [abs_of_pos ht] at hterm
  have hpos : (0 : ℝ) < Real.exp (-(s.re * t)) := Real.exp_pos _
  calc ‖S.traceTerm P t g‖ * Real.exp (-(s.re * t))
      ≤ (Real.exp (S.width * t) * polyBallBound P (S.lower⁻¹ ^ (2 : ℕ))) * ‖S.gamma g‖⁻¹ ^ (3 : ℕ) *
          Real.exp (-(s.re * t)) := mul_le_mul_of_nonneg_right hterm hpos.le
    _ = polyBallBound P (S.lower⁻¹ ^ (2 : ℕ)) * ‖S.gamma g‖⁻¹ ^ (3 : ℕ) *
          Real.exp ((S.width - s.re) * t) := by
        rw [show (S.width - s.re) * t = S.width * t + -(s.re * t) by ring, Real.exp_add]
        ring

omit [Countable G] in
theorem integral_norm_dampedTerm_le (P : Polynomial ℝ) {s : ℂ} (hs : S.width < s.re)
    {T : ℝ} (hT : 0 ≤ T) (g : G) :
    (∫ t in Ioi T, ‖S.dampedTerm P s t g‖) ≤
      polyBallBound P (S.lower⁻¹ ^ (2 : ℕ)) * Real.exp ((S.width - s.re) * T) / (s.re - S.width) *
        ‖S.gamma g‖⁻¹ ^ (3 : ℕ) := by
  have hneg : S.width - s.re < 0 := by linarith
  have hmaj : IntegrableOn
      (fun t : ℝ => polyBallBound P (S.lower⁻¹ ^ (2 : ℕ)) * ‖S.gamma g‖⁻¹ ^ (3 : ℕ) *
        Real.exp ((S.width - s.re) * t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi hneg T).const_mul _
  have hint := (S.integrableOn_dampedTerm P hs T g).norm
  have hmono := setIntegral_mono_on hint hmaj measurableSet_Ioi
    (fun t ht => S.norm_dampedTerm_le P s (lt_of_le_of_lt hT ht) g)
  refine le_trans hmono (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_mul_Ioi hneg]
  have hgne : ‖S.gamma g‖ ≠ 0 := ne_of_gt (S.norm_gamma_pos g)
  have hd : S.width - s.re ≠ 0 := ne_of_lt hneg
  have hd' : s.re - S.width ≠ 0 := by intro h; apply hd; linarith
  field_simp
  ring

omit [Countable G] in
theorem summable_integral_norm_dampedTerm (P : Polynomial ℝ) {s : ℂ} (hs : S.width < s.re)
    {T : ℝ} (hT : 0 ≤ T) :
    Summable fun g => ∫ t in Ioi T, ‖S.dampedTerm P s t g‖ := by
  have hnn : ∀ g : G, 0 ≤ ∫ t in Ioi T, ‖S.dampedTerm P s t g‖ :=
    fun g => integral_nonneg fun t => norm_nonneg _
  exact Summable.of_nonneg_of_le hnn (fun g => S.integral_norm_dampedTerm_le P hs hT g)
    (S.summable_inv_cube.mul_left _)

/-- **Active-pole Laplace transform.** To the right of the horizontal width, the Laplace
transform of the wave trace started at time `T` is the sum of the shifted resolvent kernels
of its frequencies. -/
theorem hasSum_integral_dampedTerm (P : Polynomial ℝ) {s : ℂ} (hs : S.width < s.re)
    {T : ℝ} (hT : 0 ≤ T) :
    HasSum (fun g => S.poleTerm P T s g)
      (∫ t in Ioi T, S.waveTrace P t * Complex.exp (-s * t)) := by
  have hsum :=
    hasSum_integral_of_summable_integral_norm
      (F := fun g => fun t : ℝ => S.dampedTerm P s t g)
      (μ := volume.restrict (Ioi T))
      (fun g => S.integrableOn_dampedTerm P hs T g)
      (S.summable_integral_norm_dampedTerm P hs hT)
  have hval : ∀ t : ℝ, (∑' g, S.dampedTerm P s t g) =
      S.waveTrace P t * Complex.exp (-s * t) := by
    intro t
    simp only [dampedTerm, waveTrace]
    exact tsum_mul_right
  simp_rw [hval] at hsum
  simp_rw [S.integral_dampedTerm P hs T] at hsum
  exact hsum

end WaveSpectrum

end

end GaloisForLFunctions.HTGeometry
