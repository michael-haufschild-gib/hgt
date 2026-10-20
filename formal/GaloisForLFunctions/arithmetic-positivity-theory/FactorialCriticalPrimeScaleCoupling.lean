import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelNegativeDefinite

/-!
# Scale coupling and isotropy of the critical prime channel

Translation invariance of the limiting prime form makes it a Toeplitz form in the pattern:
`P∞(S,b) = (4/π⁴) Σ_{i,j} b_i b_j R̂_{|i-j|}`, where `R̂_k` is the `k`-th cosine coefficient of the
critical kernel. The diagonal `R̂_0` is the singleton limit `Σ A(m) J_m / m⁴`. For `k ≥ 1` the
Poisson window turns `R̂_k` into the absolutely convergent charge series
`Σ_m (A(m)/m³) ∫₀^{π/6} (π/6 - ξ) ξ sin(mξ)/(4π²k² - ξ²) dξ`, so distant scales couple with
strength `O(1/k²)`. The curvature budget of the kernel gives the isotropy law: every pattern's
prime energy is the singleton value times `Σ b_j²`, up to the explicit budget.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- One cosine cell of the window: `∫₀¹ cos(ξ(t+n)) cos(2πkt) dt` for `ξ ≠ ±2πk`. -/
private theorem integral_cos_shift_mul_cos {ξ : ℝ} {k : ℕ} (h1 : ξ - 2 * Real.pi * k ≠ 0)
    (h2 : ξ + 2 * Real.pi * k ≠ 0) (c : ℝ) :
    ∫ t in (0 : ℝ)..1, Real.cos (ξ * t + c) * Real.cos (2 * Real.pi * k * t) =
      (Real.sin (ξ + c) - Real.sin c) / 2 *
        (1 / (ξ - 2 * Real.pi * k) + 1 / (ξ + 2 * Real.pi * k)) := by
  have hprod (t : ℝ) : Real.cos (ξ * t + c) * Real.cos (2 * Real.pi * k * t) =
      (Real.cos ((ξ - 2 * Real.pi * k) * t + c) + Real.cos ((ξ + 2 * Real.pi * k) * t + c)) / 2 := by
    have key (A B : ℝ) : Real.cos A * Real.cos B = (Real.cos (A - B) + Real.cos (A + B)) / 2 := by
      rw [Real.cos_sub, Real.cos_add]; ring
    rw [key, show (ξ - 2 * Real.pi * k) * t + c = (ξ * t + c) - 2 * Real.pi * k * t by ring,
      show (ξ + 2 * Real.pi * k) * t + c = (ξ * t + c) + 2 * Real.pi * k * t by ring]
  have hint (α : ℝ) (hα : α ≠ 0) : ∫ t in (0 : ℝ)..1, Real.cos (α * t + c) =
      (Real.sin (α + c) - Real.sin c) / α := by
    rw [intervalIntegral.integral_comp_mul_add (fun u => Real.cos u) hα, integral_cos]
    simp only [mul_zero, zero_add, mul_one, smul_eq_mul]
    field_simp
  simp_rw [hprod]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    hint _ h1, hint _ h2]
  have e1 : Real.sin (ξ - 2 * Real.pi * k + c) = Real.sin (ξ + c) := by
    rw [show ξ - 2 * Real.pi * k + c = ξ + c - (k : ℤ) * (2 * Real.pi) by push_cast; ring,
      Real.sin_sub_int_mul_two_pi]
  have e2 : Real.sin (ξ + 2 * Real.pi * k + c) = Real.sin (ξ + c) := by
    rw [show ξ + 2 * Real.pi * k + c = ξ + c + (k : ℤ) * (2 * Real.pi) by push_cast; ring,
      Real.sin_add_int_mul_two_pi]
  rw [e1, e2]
  field_simp

/-- Cosine moment of the window kernel: telescoping over the `2m` cells. -/
theorem integral_criticalBandWindowCos_mul_cos {ξ : ℝ} {k : ℕ} (h1 : ξ - 2 * Real.pi * k ≠ 0)
    (h2 : ξ + 2 * Real.pi * k ≠ 0) (m : ℕ) :
    ∫ t in (0 : ℝ)..1, criticalBandWindowCos m ξ t * Real.cos (2 * Real.pi * k * t) =
      Real.sin (ξ * m) * (1 / (ξ - 2 * Real.pi * k) + 1 / (ξ + 2 * Real.pi * k)) := by
  unfold criticalBandWindowCos
  simp_rw [Finset.sum_mul, add_mul]
  rw [intervalIntegral.integral_finsetSum fun n _ => by apply Continuous.intervalIntegrable; fun_prop]
  have hcell (n : ℕ) : ∫ t in (0 : ℝ)..1, (Real.cos (ξ * (t + n)) * Real.cos (2 * Real.pi * k * t) +
      Real.cos (ξ * (t - n - 1)) * Real.cos (2 * Real.pi * k * t)) =
      (Real.sin (ξ * (n + 1 : ℕ)) - Real.sin (ξ * n)) *
        (1 / (ξ - 2 * Real.pi * k) + 1 / (ξ + 2 * Real.pi * k)) := by
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have ha : (fun t => Real.cos (ξ * (t + n)) * Real.cos (2 * Real.pi * k * t)) =
        fun t => Real.cos (ξ * t + ξ * n) * Real.cos (2 * Real.pi * k * t) := by
      funext t; ring_nf
    have hb : (fun t => Real.cos (ξ * (t - n - 1)) * Real.cos (2 * Real.pi * k * t)) =
        fun t => Real.cos (ξ * t + -(ξ * (n + 1))) * Real.cos (2 * Real.pi * k * t) := by
      funext t; ring_nf
    rw [ha, hb, integral_cos_shift_mul_cos h1 h2, integral_cos_shift_mul_cos h1 h2]
    push_cast
    rw [show ξ + -(ξ * ((n : ℝ) + 1)) = -(ξ * n) by ring, Real.sin_neg, Real.sin_neg,
      show ξ + ξ * (n : ℝ) = ξ * (n + 1) by ring]
    ring
  rw [Finset.sum_congr rfl fun n _ => hcell n, ← Finset.sum_mul,
    Finset.sum_range_sub (fun n : ℕ => Real.sin (ξ * n))]
  simp

/-- Band weight of the scale coupling at distance `k` from harmonic `m`. -/
def criticalBandCouplingWeight (k m : ℕ) : ℝ :=
  ∫ ξ in (0 : ℝ)..Real.pi / 6,
    (Real.pi / 6 - ξ) * ξ * Real.sin (ξ * m) / (4 * Real.pi ^ 2 * k ^ 2 - ξ ^ 2)

private theorem band_freq_ne {k : ℕ} (hk : 1 ≤ k) {ξ : ℝ} (hξ : ξ ∈ Set.uIcc (0 : ℝ) (Real.pi / 6)) :
    ξ - 2 * Real.pi * k ≠ 0 ∧ ξ + 2 * Real.pi * k ≠ 0 := by
  rw [Set.uIcc_of_le (by positivity)] at hξ
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpi := Real.pi_pos
  constructor
  · have : ξ < 2 * Real.pi * k := by nlinarith [hξ.2]
    linarith
  · have : 0 < 2 * Real.pi * k := by positivity
    linarith [hξ.1]

/-- Cosine moments of the window deviation are band coupling weights. -/
theorem integral_criticalBandWindowDeviation_mul_cos {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    ∫ t in (0 : ℝ)..1, criticalBandWindowDeviation m t * Real.cos (2 * Real.pi * k * t) =
      -2 * criticalBandCouplingWeight k m := by
  have hcos0 : ∫ t in (0 : ℝ)..1, Real.cos (2 * Real.pi * k * t) = 0 := by
    have hk0 : (2 * Real.pi * k : ℝ) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun u => Real.cos u) hk0, integral_cos]
    simp only [mul_zero, mul_one, Real.sin_zero, sub_zero, smul_eq_mul]
    rw [show 2 * Real.pi * (k : ℝ) = ((2 * k : ℕ) : ℝ) * Real.pi by push_cast; ring, Real.sin_nat_mul_pi,
      mul_zero]
  have hcwc : Continuous fun p : ℝ × ℝ => criticalBandWindowCos m p.2 p.1 := by
    unfold criticalBandWindowCos; fun_prop
  simp_rw [criticalBandWindowDeviation_eq_integral, ← intervalIntegral.integral_mul_const]
  rw [GaloisForLFunctions.HTGeometry.intervalIntegral_integral_swap_of_continuous
    (F := fun t ξ => (Real.pi / 6 - ξ) * (criticalBandWindowCos m ξ t -
      2 * ((m : ℝ) * Real.sinc (ξ * m))) * Real.cos (2 * Real.pi * k * t))
    (by have := Real.continuous_sinc; fun_prop) zero_le_one (by positivity)]
  unfold criticalBandCouplingWeight
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun ξ hξ => ?_
  obtain ⟨h1, h2⟩ := band_freq_ne hk hξ
  show ∫ t in (0 : ℝ)..1, (Real.pi / 6 - ξ) * (criticalBandWindowCos m ξ t -
      2 * ((m : ℝ) * Real.sinc (ξ * m))) * Real.cos (2 * Real.pi * k * t) = _
  have hsplit : (fun t => (Real.pi / 6 - ξ) * (criticalBandWindowCos m ξ t -
      2 * ((m : ℝ) * Real.sinc (ξ * m))) * Real.cos (2 * Real.pi * k * t)) =
      fun t => (Real.pi / 6 - ξ) * (criticalBandWindowCos m ξ t * Real.cos (2 * Real.pi * k * t)) -
        (Real.pi / 6 - ξ) * (2 * ((m : ℝ) * Real.sinc (ξ * m))) * Real.cos (2 * Real.pi * k * t) := by
    funext t; ring
  rw [hsplit, intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; unfold criticalBandWindowCos; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_criticalBandWindowCos_mul_cos h1 h2, hcos0]
  have hden : 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - ξ ^ 2 ≠ 0 := by
    have : (ξ - 2 * Real.pi * k) * (ξ + 2 * Real.pi * k) ≠ 0 := mul_ne_zero h1 h2
    intro h; apply this; linear_combination -h
  have hpf : 1 / (ξ - 2 * Real.pi * k) + 1 / (ξ + 2 * Real.pi * k) =
      -2 * ξ / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - ξ ^ 2) := by
    rw [div_add_div _ _ h1 h2, eq_div_iff hden]
    field_simp
    ring
  rw [hpf]
  field_simp
  ring

/-- Scale-coupling coefficient: the `k`-th cosine coefficient of the critical prime kernel. -/
def factorialCriticalPrimeCoupling (k : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, factorialCriticalPrimeContinuousRealKernel t * Real.cos (2 * Real.pi * k * t)

private theorem continuous_criticalBandWindowDeviation (m : ℕ) :
    Continuous (criticalBandWindowDeviation m) := by
  have := continuous_criticalBandWeight
  unfold criticalBandWindowDeviation criticalBandWindow; fun_prop

/-- Exchange of the unit-cell cosine moment with the harmonic charge series. -/
private theorem coupling_tsum_exchange (k : ℕ) :
    ∫ t in (0 : ℝ)..1, (∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
      criticalBandWindowDeviation m t) * Real.cos (2 * Real.pi * k * t) =
      ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
        ∫ t in (0 : ℝ)..1, criticalBandWindowDeviation m t * Real.cos (2 * Real.pi * k * t) := by
  set c : ℕ → ℝ := fun m => factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3
  set F : ℕ → ℝ → ℝ := fun m t => c m * criticalBandWindowDeviation m t * Real.cos (2 * Real.pi * k * t)
  have hcont (m : ℕ) : Continuous (F m) := by
    have := continuous_criticalBandWindowDeviation m; simp only [F]; fun_prop
  have hint (m : ℕ) : Integrable (F m) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hcont m).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hbound (m : ℕ) : ∫ t in Ioc (0 : ℝ) 1, ‖F m t‖ ≤ |c m| * ((Real.pi / 6) ^ 3 / 35) := by
    calc ∫ t in Ioc (0 : ℝ) 1, ‖F m t‖ ≤ ∫ t in Ioc (0 : ℝ) 1, |c m| * ((Real.pi / 6) ^ 3 / 35) := by
          refine setIntegral_mono_on (hint m).norm (integrableOn_const measure_Ioc_lt_top.ne)
            measurableSet_Ioc fun t ht => ?_
          simp only [F, norm_mul, Real.norm_eq_abs]
          have h1 := abs_criticalBandWindowDeviation_le_cube m (Ioc_subset_Icc_self ht)
          have h2 := Real.abs_cos_le_one (2 * Real.pi * k * t)
          calc |c m| * |criticalBandWindowDeviation m t| * |Real.cos (2 * Real.pi * k * t)| ≤
              |c m| * ((Real.pi / 6) ^ 3 / 35) * 1 := by gcongr
            _ = _ := mul_one _
      _ = |c m| * ((Real.pi / 6) ^ 3 / 35) := by simp
  have hsum : Summable fun m => ∫ t in Ioc (0 : ℝ) 1, ‖F m t‖ :=
    Summable.of_nonneg_of_le (fun m => integral_nonneg fun t => norm_nonneg _) hbound
      ((summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube.congr fun m => by
        simp only [c, abs_div, abs_pow, Nat.abs_cast]).mul_right _)
  rw [intervalIntegral.integral_of_le zero_le_one]
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  have hcomm : (fun t => (∑' m : ℕ, c m * criticalBandWindowDeviation m t) *
      Real.cos (2 * Real.pi * k * t)) = fun t => ∑' m, F m t := by
    funext t; simp only [F]; rw [← tsum_mul_right]
  rw [show (fun t => (∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
    criticalBandWindowDeviation m t) * Real.cos (2 * Real.pi * k * t)) = fun t => ∑' m, F m t from hcomm,
    ← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun m => ?_
  simp only [F, mul_assoc]
  rw [integral_const_mul]

/-- **Scale-coupling law.** For `k ≥ 1` the coupling between translated scales at distance `k`
is the charge series of band weights `∫₀^{π/6}(π/6-ξ)ξ sin(mξ)/(4π²k² - ξ²) dξ`. -/
theorem factorialCriticalPrimeCoupling_eq_tsum {k : ℕ} (hk : 1 ≤ k) :
    factorialCriticalPrimeCoupling k = ∑' m : ℕ,
      factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 * criticalBandCouplingWeight k m := by
  have hcos0 : ∫ t in (0 : ℝ)..1, Real.cos (2 * Real.pi * k * t) = 0 := by
    have hk0 : (2 * Real.pi * k : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    rw [intervalIntegral.integral_comp_mul_left (fun u => Real.cos u) hk0, integral_cos]
    simp only [mul_zero, mul_one, Real.sin_zero, sub_zero, smul_eq_mul]
    rw [show 2 * Real.pi * (k : ℝ) = ((2 * k : ℕ) : ℝ) * Real.pi by push_cast; ring, Real.sin_nat_mul_pi,
      mul_zero]
  unfold factorialCriticalPrimeCoupling
  have hR : ∫ t in (0 : ℝ)..1, factorialCriticalPrimeContinuousRealKernel t * Real.cos (2 * Real.pi * k * t) =
      ∫ t in (0 : ℝ)..1, ((∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m * factorialCriticalHarmonicDefect m /
        (m : ℝ) ^ 4) * Real.cos (2 * Real.pi * k * t) - (1 / 2) * ((∑' m : ℕ,
          factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 * criticalBandWindowDeviation m t) *
            Real.cos (2 * Real.pi * k * t))) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [factorialCriticalPrimeContinuousRealKernel_eq ht]
    ring
  have hi1 : IntervalIntegrable (fun t => (∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m *
      factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4) * Real.cos (2 * Real.pi * k * t)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hi2 : IntervalIntegrable (fun t => (1 / 2) * ((∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m /
      (m : ℝ) ^ 3 * criticalBandWindowDeviation m t) * Real.cos (2 * Real.pi * k * t))) volume 0 1 := by
    have h := hi1.sub (show IntervalIntegrable (fun t => factorialCriticalPrimeContinuousRealKernel t *
      Real.cos (2 * Real.pi * k * t)) volume 0 1 from ?_)
    · refine h.congr fun t ht => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [factorialCriticalPrimeContinuousRealKernel_eq (Ioc_subset_Icc_self ht)]
      ring
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact continuousOn_factorialCriticalPrimeContinuousRealKernel.mul (by fun_prop)
  rw [hR, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul, hcos0,
    intervalIntegral.integral_const_mul, coupling_tsum_exchange]
  simp_rw [integral_criticalBandWindowDeviation_mul_cos hk]
  rw [mul_zero, zero_sub, ← tsum_mul_left, ← tsum_neg]
  refine tsum_congr fun m => ?_
  ring

private theorem integral_band_moment :
    ∫ ξ in (0 : ℝ)..Real.pi / 6, (Real.pi / 6 - ξ) * ξ = (Real.pi / 6) ^ 3 / 6 := by
  have hd : ∀ ξ ∈ Set.uIcc (0 : ℝ) (Real.pi / 6), HasDerivAt
      (fun ξ : ℝ => Real.pi / 6 * ξ ^ 2 / 2 - ξ ^ 3 / 3) ((Real.pi / 6 - ξ) * ξ) ξ := by
    intro ξ _
    have := (((hasDerivAt_pow 2 ξ).const_mul (Real.pi / 6)).div_const 2).sub ((hasDerivAt_pow 3 ξ).div_const 3)
    exact this.congr_deriv (by push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- Each band coupling weight is `O(1/k²)` uniformly in the harmonic. -/
theorem abs_criticalBandCouplingWeight_le {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    |criticalBandCouplingWeight k m| ≤
      (Real.pi / 6) ^ 3 / 6 / (4 * Real.pi ^ 2 * k ^ 2 - (Real.pi / 6) ^ 2) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpi := Real.pi_pos
  have hD : 0 < 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - (Real.pi / 6) ^ 2 := by
    have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hkR
    have hp2 : 0 < Real.pi ^ 2 := by positivity
    nlinarith
  unfold criticalBandCouplingWeight
  rw [← Real.norm_eq_abs, show (Real.pi / 6) ^ 3 / 6 / (4 * Real.pi ^ 2 * k ^ 2 - (Real.pi / 6) ^ 2) =
    ∫ ξ in (0 : ℝ)..Real.pi / 6, (Real.pi / 6 - ξ) * ξ / (4 * Real.pi ^ 2 * k ^ 2 - (Real.pi / 6) ^ 2) by
      rw [intervalIntegral.integral_div, integral_band_moment]]
  apply intervalIntegral.norm_integral_le_of_norm_le (by positivity)
  · refine Eventually.of_forall fun ξ hξ => ?_
    obtain ⟨h0, h1⟩ := hξ
    have hξ2 : ξ ^ 2 ≤ (Real.pi / 6) ^ 2 := pow_le_pow_left₀ h0.le h1 2
    have hden : 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 - (Real.pi / 6) ^ 2 ≤ 4 * Real.pi ^ 2 * k ^ 2 - ξ ^ 2 := by
      linarith
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.pi / 6 - ξ),
      abs_of_pos h0, abs_of_pos (hD.trans_le hden)]
    calc (Real.pi / 6 - ξ) * ξ * |Real.sin (ξ * m)| / (4 * Real.pi ^ 2 * k ^ 2 - ξ ^ 2) ≤
        (Real.pi / 6 - ξ) * ξ * 1 / (4 * Real.pi ^ 2 * k ^ 2 - (Real.pi / 6) ^ 2) := by
          apply div_le_div₀ (by nlinarith) (by gcongr; exact Real.abs_sin_le_one _) hD hden
      _ = _ := by rw [mul_one]
  · apply Continuous.intervalIntegrable; fun_prop

/-- The coupling coefficients decay like `1/k²`, with the total absolute harmonic charge. -/
theorem abs_factorialCriticalPrimeCoupling_le {k : ℕ} (hk : 1 ≤ k) :
    |factorialCriticalPrimeCoupling k| ≤
      (∑' m : ℕ, |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3) *
        ((Real.pi / 6) ^ 3 / 6 / (4 * Real.pi ^ 2 * k ^ 2 - (Real.pi / 6) ^ 2)) := by
  rw [factorialCriticalPrimeCoupling_eq_tsum hk]
  set B := (Real.pi / 6) ^ 3 / 6 / (4 * Real.pi ^ 2 * k ^ 2 - (Real.pi / 6) ^ 2)
  have hs := summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube
  have hb (m : ℕ) : ‖factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 * criticalBandCouplingWeight k m‖ ≤
      |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 * B := by
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (abs_criticalBandCouplingWeight_le hk m)
      (div_nonneg (abs_nonneg _) (by positivity))
  rw [← Real.norm_eq_abs, ← tsum_mul_right]
  exact tsum_of_norm_bounded (hs.mul_right B).hasSum hb

/-- The diagonal coupling is the singleton prime limit `Σ A(m) J_m / m⁴`. -/
theorem factorialCriticalPrimeCoupling_zero :
    factorialCriticalPrimeCoupling 0 = ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m *
      factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4 := by
  have h := factorialCriticalTranslatedPrimeLimit_eq_continuous_kernel_integral {0} (fun _ => 1)
  rw [factorialCriticalTranslatedPrimeLimit_singleton, factorialCriticalPrimeLimit_eq_harmonic_diagonal] at h
  have hQ (t : ℝ) : factorialCriticalPatternDensity {0} (fun _ => 1) t = 1 := by
    simp [factorialCriticalPatternDensity]
  simp only [hQ, mul_one, one_pow, one_mul] at h
  unfold factorialCriticalPrimeCoupling
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one]
  have hpi : (4 / Real.pi ^ 4 : ℝ) ≠ 0 := by positivity
  exact (mul_left_cancel₀ hpi h).symm

/-- **Toeplitz form of the critical prime channel.** Two translated scales at distance `k`
interact through the single coupling coefficient `R̂_k`. -/
theorem factorialCriticalTranslatedPrimeLimit_eq_coupling (S : Finset ℕ) (b : ℕ → ℝ) :
    factorialCriticalTranslatedPrimeLimit S b = (4 / Real.pi ^ 4) *
      ∑ i ∈ S, ∑ j ∈ S, b i * b j * factorialCriticalPrimeCoupling ((i : ℤ) - j).natAbs := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_continuous_kernel_integral]
  congr 1
  simp_rw [factorialCriticalPatternDensity_eq, Finset.mul_sum]
  have hc := continuousOn_factorialCriticalPrimeContinuousRealKernel
  rw [intervalIntegral.integral_finsetSum fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      unfold factorialCriticalPrimeCoupling
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      have hcos : Real.cos (2 * Real.pi * ((i : ℝ) - j) * t) =
          Real.cos (2 * Real.pi * (((i : ℤ) - j).natAbs : ℝ) * t) := by
        rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
        rcases le_total 0 ((i : ℝ) - j) with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, ← Real.cos_neg]; congr 1; ring
      rw [hcos]; ring
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact hc.mul (by fun_prop)
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_finsetSum _ fun j _ => hc.mul (by fun_prop)

/-- The curvature budget of the critical kernel around its mean. -/
def factorialCriticalPrimeCurvatureBudget : ℝ :=
  (Real.log 2 / 4 * ((Real.pi / 6) ^ 4 / 35) + Real.log 3 / 9 * (3 * (Real.pi / 6) ^ 4 / 70) +
    (Real.pi / 6) ^ 3 / 35 * ((2 * Real.log 2 + 1) / 4)) / 2

/-- The critical kernel stays within the curvature budget of its mean on the whole cell. -/
theorem abs_factorialCriticalPrimeContinuousRealKernel_sub_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |factorialCriticalPrimeContinuousRealKernel t - factorialCriticalPrimeCoupling 0| ≤
      factorialCriticalPrimeCurvatureBudget := by
  rw [factorialCriticalPrimeCoupling_zero, factorialCriticalPrimeContinuousRealKernel_eq ht]
  have hs := summable_charge_mul_criticalBandWindowDeviation ht
  have hB := tsum_abs_charge_mul_criticalBandWindowDeviation_le ht
  have hn := norm_tsum_le_tsum_norm (f := fun m : ℕ => factorialCriticalPrimeHarmonicCharge m /
    (m : ℝ) ^ 3 * criticalBandWindowDeviation m t) (by simpa only [Real.norm_eq_abs] using hs)
  simp only [Real.norm_eq_abs] at hn
  rw [show ∀ x y : ℝ, x - 1 / 2 * y - x = -(y / 2) by intros; ring, abs_neg, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold factorialCriticalPrimeCurvatureBudget
  exact div_le_div_of_nonneg_right (hn.trans hB) (by norm_num)

/-- **Critical isotropy law.** Every finite real pattern has limiting prime energy within the
curvature budget of the singleton value times its coefficient energy:
`|P∞(S,b) - (4/π⁴) R̂₀ Σ b_j²| ≤ (4/π⁴) · budget · Σ b_j²`. -/
theorem abs_factorialCriticalTranslatedPrimeLimit_sub_isotropic_le (S : Finset ℕ) (b : ℕ → ℝ) :
    |factorialCriticalTranslatedPrimeLimit S b -
      (4 / Real.pi ^ 4) * factorialCriticalPrimeCoupling 0 * ∑ j ∈ S, b j ^ 2| ≤
      (4 / Real.pi ^ 4) * factorialCriticalPrimeCurvatureBudget * ∑ j ∈ S, b j ^ 2 := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_continuous_kernel_integral]
  set R := factorialCriticalPrimeContinuousRealKernel
  set Q := factorialCriticalPatternDensity S b
  set M := factorialCriticalPrimeCoupling 0
  have hQc := continuous_factorialCriticalPatternDensity S b
  have hRc := continuousOn_factorialCriticalPrimeContinuousRealKernel
  have hE : ∫ t in (0 : ℝ)..1, Q t = ∑ j ∈ S, b j ^ 2 := by
    simpa using factorialCriticalPatternDensity_cell S b one_pos 0
  have hi1 : IntervalIntegrable (fun t => (R t - M) * Q t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le zero_le_one]
    exact (hRc.sub continuousOn_const).mul hQc.continuousOn
  have hsplit : ∫ t in (0 : ℝ)..1, R t * Q t = M * ∑ j ∈ S, b j ^ 2 + ∫ t in (0 : ℝ)..1, (R t - M) * Q t := by
    rw [← hE, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop) hi1]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have hdev : |∫ t in (0 : ℝ)..1, (R t - M) * Q t| ≤
      factorialCriticalPrimeCurvatureBudget * ∑ j ∈ S, b j ^ 2 := by
    rw [← hE, ← intervalIntegral.integral_const_mul, ← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    · refine Eventually.of_forall fun t ht => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (factorialCriticalPatternDensity_nonneg S b t)]
      exact mul_le_mul_of_nonneg_right
        (abs_factorialCriticalPrimeContinuousRealKernel_sub_le (Ioc_subset_Icc_self ht))
        (factorialCriticalPatternDensity_nonneg S b t)
    · apply Continuous.intervalIntegrable; fun_prop
  rw [hsplit, mul_add, show ∀ x y : ℝ, (4 / Real.pi ^ 4) * (M * y) + x - (4 / Real.pi ^ 4) * M * y = x by
    intros; ring, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi ^ 4), mul_assoc]
  exact mul_le_mul_of_nonneg_left hdev (by positivity)

end GaloisForLFunctions.ArithmeticPositivityTheory
