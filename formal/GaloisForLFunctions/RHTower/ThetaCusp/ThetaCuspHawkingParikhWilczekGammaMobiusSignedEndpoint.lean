import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaMobiusGlobalAdmission
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusAbel
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusHarmonicZero

/-!
# The literal Gamma/Möbius signed endpoint and reconstruction mass defect

A direct Gamma dilation-difference bound has integrable cost O(n^-2).
The unconditional inverse-square Mertens estimate therefore admits the
complete signed Abel assembly at coefficient parameter zero. Exact finite
summation by parts and terminal decay identify it with the original source.
That source has zero mass and strictly positive finite L1 norm.

Every positive dilation still has zero mass, while their full arithmetic
reconstruction is the integrable Gamma source with mass Gamma(3/2)>0.
The exact integral-interchange defect and failure of absolute reconstruction
mass summability are retained. No vanishing spectral Ward law, global
logarithmic-current admission, or Riemann hypothesis is assumed or asserted.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

private theorem pwGamma_sqrt_increment {r : ℝ} (hr : 0 < r) :
    Real.sqrt (r + 1) - Real.sqrt r ≤ Real.sqrt r / r := by
  have ha := Real.sq_sqrt hr.le
  have hb := Real.sq_sqrt (show 0 ≤ r + 1 by positivity)
  have hab : Real.sqrt r ≤ Real.sqrt (r + 1) := Real.sqrt_le_sqrt (by linarith)
  have hprod : (Real.sqrt (r + 1) - Real.sqrt r) *
      (Real.sqrt (r + 1) + Real.sqrt r) = 1 := by nlinarith
  have hstep : (Real.sqrt (r + 1) - Real.sqrt r) * Real.sqrt r ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (Real.sqrt_nonneg (r + 1))]
  apply (le_div_iff₀ hr).mpr
  calc
    _ = ((Real.sqrt (r + 1) - Real.sqrt r) * Real.sqrt r) * Real.sqrt r := by
      rw [mul_assoc, ← pow_two, ha]
    _ ≤ 1 * Real.sqrt r := mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg r)
    _ = _ := one_mul _

theorem pwGammaRaySource_adjacent_norm_le {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    ‖pwGammaRaySource ((r + 1) * x) - pwGammaRaySource (r * x)‖ ≤
      (1 / r + x) * ‖pwGammaRaySource (r * x)‖ := by
  have hr1 : 0 < r + 1 := by positivity
  have he : Real.exp (-x) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -x ≤ 0 by linarith)
  have hsmall : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
  have hinc : 0 ≤ Real.sqrt (r + 1) - Real.sqrt r :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hincbound := pwGamma_sqrt_increment hr
  rw [pwGammaRaySource_eq (mul_pos hr1 hx), pwGammaRaySource_eq (mul_pos hr hx),
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [Real.sqrt_mul hr1.le, Real.sqrt_mul hr.le,
    show -((r + 1) * x) = -(r * x) + -x by ring, Real.exp_add]
  have hsplit :
      Real.sqrt (r + 1) * Real.sqrt x * (Real.exp (-(r * x)) * Real.exp (-x)) -
          Real.sqrt r * Real.sqrt x * Real.exp (-(r * x)) =
      (Real.sqrt (r + 1) - Real.sqrt r) * Real.sqrt x * Real.exp (-(r * x)) * Real.exp (-x) -
        Real.sqrt r * Real.sqrt x * Real.exp (-(r * x)) * (1 - Real.exp (-x)) := by ring
  rw [hsplit]
  calc
    _ ≤ |(Real.sqrt (r + 1) - Real.sqrt r) * Real.sqrt x * Real.exp (-(r * x)) * Real.exp (-x)| +
        |Real.sqrt r * Real.sqrt x * Real.exp (-(r * x)) * (1 - Real.exp (-x))| := abs_sub _ _
    _ = (Real.sqrt (r + 1) - Real.sqrt r) * Real.sqrt x * Real.exp (-(r * x)) * Real.exp (-x) +
        Real.sqrt r * Real.sqrt x * Real.exp (-(r * x)) * (1 - Real.exp (-x)) := by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ (Real.sqrt r / r) * Real.sqrt x * Real.exp (-(r * x)) * 1 +
        Real.sqrt r * Real.sqrt x * Real.exp (-(r * x)) * x := by
      gcongr
    _ = _ := by ring

private theorem pwGammaRaySource_moment_eq {y : ℝ} (hy : 0 < y) :
    y * ‖pwGammaRaySource y‖ = Real.exp (-y) * y ^ ((5 / 2 : ℝ) - 1) := by
  rw [pwGammaRaySource_eq hy, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.sqrt_eq_rpow, show (5 / 2 : ℝ) - 1 = 1 + 1 / 2 by ring,
    Real.rpow_add hy, Real.rpow_one]
  ring

theorem pwGammaRaySource_first_moment_integrable :
    IntegrableOn (fun y : ℝ => y * ‖pwGammaRaySource y‖) (Ioi 0) := by
  refine IntegrableOn.congr_fun (Real.GammaIntegral_convergent (s := 5 / 2) (by positivity))
    (fun y hy => (pwGammaRaySource_moment_eq hy).symm) measurableSet_Ioi

theorem pwGammaRaySource_first_moment_integral :
    (∫ y in Ioi (0 : ℝ), y * ‖pwGammaRaySource y‖) = Real.Gamma (5 / 2) := by
  rw [Real.Gamma_eq_integral (s := 5 / 2) (by positivity)]
  exact setIntegral_congr_fun measurableSet_Ioi fun y hy => pwGammaRaySource_moment_eq hy

private theorem pwGammaRaySource_dilation_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => pwGammaRaySource (r * x)) (Ioi 0) := by
  apply (integrableOn_Ioi_comp_mul_left_iff pwGammaRaySource 0 hr).mpr
  simpa only [mul_zero] using pwGammaRaySource_integrable

private theorem pwGammaRaySource_dilation_first_moment_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => x * ‖pwGammaRaySource (r * x)‖) (Ioi 0) := by
  have h : IntegrableOn (fun x => (r * x) * ‖pwGammaRaySource (r * x)‖) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (fun y => y * ‖pwGammaRaySource y‖) 0 hr).mpr
    simpa only [mul_zero] using pwGammaRaySource_first_moment_integrable
  refine IntegrableOn.congr_fun (h.const_mul r⁻¹) ?_ measurableSet_Ioi
  intro x _
  dsimp only
  field_simp

private theorem pwGammaRaySource_dilation_first_moment_integral {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), x * ‖pwGammaRaySource (r * x)‖) = Real.Gamma (5 / 2) / r ^ 2 := by
  have hf : (fun x => x * ‖pwGammaRaySource (r * x)‖) =
      (fun x => r⁻¹ * ((r * x) * ‖pwGammaRaySource (r * x)‖)) := by
    funext x
    field_simp
  rw [hf, integral_const_mul,
    integral_comp_mul_left_Ioi (fun y => y * ‖pwGammaRaySource y‖) 0 hr,
    mul_zero, smul_eq_mul, pwGammaRaySource_first_moment_integral]
  ring

theorem pwGammaRaySource_adjacent_integral_norm_le {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), ‖pwGammaRaySource ((r + 1) * x) - pwGammaRaySource (r * x)‖) ≤
      (Real.Gamma (3 / 2) + Real.Gamma (5 / 2)) / r ^ 2 := by
  have h0 := pwGammaRaySource_dilation_integrable hr
  have h1 := pwGammaRaySource_dilation_integrable (show 0 < r + 1 by positivity)
  have hm := (h0.norm.const_mul (1 / r)).add (pwGammaRaySource_dilation_first_moment_integrable hr)
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), (1 / r) * ‖pwGammaRaySource (r * x)‖ +
          x * ‖pwGammaRaySource (r * x)‖ := by
      apply integral_mono_ae (h1.sub h0).norm hm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      change ‖pwGammaRaySource ((r + 1) * x) - pwGammaRaySource (r * x)‖ ≤
        (1 / r) * ‖pwGammaRaySource (r * x)‖ + x * ‖pwGammaRaySource (r * x)‖
      rw [← add_mul]
      exact pwGammaRaySource_adjacent_norm_le hr hx
    _ = _ := by
      rw [integral_add (h0.norm.const_mul (1 / r)) (pwGammaRaySource_dilation_first_moment_integrable hr),
        integral_const_mul, integral_comp_mul_left_Ioi (fun y => ‖pwGammaRaySource y‖) 0 hr,
        mul_zero, smul_eq_mul, pwGammaRaySource_norm_integral,
        pwGammaRaySource_dilation_first_moment_integral hr]
      ring

/-- Signed Abel atoms for the literal Gamma source. -/
def pwGammaMobiusAbelAtom (n : ℕ) (x : ℝ) : ℂ :=
  (Sieve.mertensM n : ℂ) *
    (pwGammaRaySource ((n : ℝ) * x) - pwGammaRaySource (((n : ℝ) + 1) * x))

private theorem pwGammaMertens_zero : Sieve.mertensM 0 = 0 := by
  simp [Sieve.mertensM]

private theorem pwGammaMobiusAbelAtom_zero : pwGammaMobiusAbelAtom 0 = 0 := by
  funext x
  simp [pwGammaMobiusAbelAtom, pwGammaMertens_zero]

theorem pwGammaMobiusAbelAtom_integrable (n : ℕ) :
    IntegrableOn (pwGammaMobiusAbelAtom n) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pwGammaMobiusAbelAtom_zero]
    exact integrable_zero ℝ ℂ _
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact ((pwGammaRaySource_dilation_integrable hnr).sub
      (pwGammaRaySource_dilation_integrable (show 0 < (n : ℝ) + 1 by positivity))).const_mul _

theorem pwGammaMobiusAbelAtom_integral_norm_le (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusAbelAtom n x‖) ≤
      (Real.Gamma (3 / 2) + Real.Gamma (5 / 2)) * (|Sieve.mertensM n| / (n : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusAbelAtom_zero]
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hb := pwGammaRaySource_adjacent_integral_norm_le hnr
    have hrev : (fun x : ℝ => ‖pwGammaRaySource ((n : ℝ) * x) -
          pwGammaRaySource (((n : ℝ) + 1) * x)‖) =
        (fun x : ℝ => ‖pwGammaRaySource (((n : ℝ) + 1) * x) -
          pwGammaRaySource ((n : ℝ) * x)‖) := funext fun x => norm_sub_rev _ _
    simp only [pwGammaMobiusAbelAtom, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      integral_const_mul]
    rw [hrev]
    calc
      _ ≤ |Sieve.mertensM n| * ((Real.Gamma (3 / 2) + Real.Gamma (5 / 2)) / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = _ := by ring

theorem pwGammaMobiusAbelAtom_norm_integrals_summable :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusAbelAtom n x‖) :=
  (deningerMertensM_invSq_summable.mul_left (Real.Gamma (3 / 2) + Real.Gamma (5 / 2))).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _) pwGammaMobiusAbelAtom_integral_norm_le

theorem pwGammaMobiusAbelAtom_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => pwGammaMobiusAbelAtom n x) := by
  let C : ℝ := Real.exp ((5 / 2) * Real.log (5 / 2) - 5 / 2)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  refine Summable.of_norm_bounded (deningerMertensM_invSq_summable.mul_left (2 * C / x ^ 2)) ?_
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusAbelAtom_zero]
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnx := mul_pos hnr hx
    have hn1x : 0 < ((n : ℝ) + 1) * x := by positivity
    have hq0 : ‖pwGammaRaySource ((n : ℝ) * x)‖ ≤ C / ((n : ℝ) * x) ^ 2 :=
      pwGammaRaySource_norm_le_inv_sq hnx
    have hq1 : ‖pwGammaRaySource (((n : ℝ) + 1) * x)‖ ≤ C / ((n : ℝ) * x) ^ 2 := by
      refine (pwGammaRaySource_norm_le_inv_sq hn1x).trans ?_
      apply div_le_div_of_nonneg_left hC (sq_pos_of_pos hnx)
      gcongr
      linarith
    rw [pwGammaMobiusAbelAtom, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |Sieve.mertensM n| *
          (‖pwGammaRaySource ((n : ℝ) * x)‖ + ‖pwGammaRaySource (((n : ℝ) + 1) * x)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
      _ ≤ |Sieve.mertensM n| * (C / ((n : ℝ) * x) ^ 2 + C / ((n : ℝ) * x) ^ 2) := by gcongr
      _ = _ := by rw [mul_pow]; ring

/-- The exact finite identity retains the terminal source contribution. -/
theorem pwGammaMobiusAbel_finite (N : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.range N, pwGammaMobiusAbelAtom n x) =
      (∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℂ) * pwGammaRaySource ((n : ℝ) * x)) -
        pwGammaRaySource ((N : ℝ) * x) * (Sieve.mertensM N : ℂ) := by
  classical
  let F : ℕ → ℂ := fun n => pwGammaRaySource ((n : ℝ) * x)
  let G : ℕ → ℂ := fun n => ((moebius n : ℤ) : ℂ)
  have hsum : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), G j) = (Sieve.mertensM n : ℂ) := by
    intro n
    simp only [Sieve.mertensM, G, Complex.ofReal_sum, Complex.ofReal_intCast]
  have hparts := Finset.sum_range_by_parts F G (N + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul, hsum] at hparts
  have hdiff : (∑ n ∈ Finset.range N, (F (n + 1) - F n) * (Sieve.mertensM n : ℂ)) =
      -(∑ n ∈ Finset.range N, pwGammaMobiusAbelAtom n x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [F, pwGammaMobiusAbelAtom, Nat.cast_add, Nat.cast_one]
    ring
  have hmain : (∑ n ∈ Finset.range (N + 1), F n * G n) =
      (∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℂ) * pwGammaRaySource ((n : ℝ) * x)) := by
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [hdiff, hmain] at hparts
  dsimp only [F] at hparts
  linear_combination -hparts

theorem pwGammaMobiusAbel_boundary_tendsto_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => pwGammaRaySource ((n : ℝ) * x) * (Sieve.mertensM n : ℂ))
      atTop (𝓝 0) := by
  let C : ℝ := Real.exp ((5 / 2) * Real.log (5 / 2) - 5 / 2)
  have hmaj : Tendsto (fun n : ℕ => (C / x ^ 2) * (1 / (n : ℝ) + 1 / (n : ℝ) ^ 2))
      atTop (𝓝 0) := by
    have h1 := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 : Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
      have hm := h1.mul h1
      rw [mul_zero] at hm
      refine hm.congr fun n => ?_
      rw [div_mul_div_comm, one_mul, ← pow_two]
    simpa using (h1.add h2).const_mul (C / x ^ 2)
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hq := pwGammaRaySource_norm_le_inv_sq (mul_pos hnr hx)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (C / ((n : ℝ) * x) ^ 2) * ((n : ℝ) + 1) :=
      mul_le_mul hq (deningerMertensM_abs_le n) (abs_nonneg _) (by positivity)
    _ = _ := by field_simp

/-- Actual source equality, including the full terminal-limit check. -/
theorem pwGammaMobiusPreimage_eq_abel {x : ℝ} (hx : 0 < x) :
    pwGammaMobiusPreimage x = ∑' n, pwGammaMobiusAbelAtom n x := by
  have hpartial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
      ((moebius n : ℤ) : ℂ) * pwGammaRaySource ((n : ℝ) * x)) atTop (𝓝 (pwGammaMobiusPreimage x)) :=
    (pwGammaMobiusPreimage_summable hx).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hlim := hpartial.sub (pwGammaMobiusAbel_boundary_tendsto_zero hx)
  simp only [sub_zero] at hlim
  have hlim' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, pwGammaMobiusAbelAtom n x)
      atTop (𝓝 (pwGammaMobiusPreimage x)) :=
    hlim.congr fun N => (pwGammaMobiusAbel_finite N x).symm
  exact tendsto_nhds_unique hlim' (pwGammaMobiusAbelAtom_summable hx).hasSum.tendsto_sum_nat

/-- The signed zero-parameter source crosses the original absolute-atom boundary. -/
theorem pwGammaMobiusPreimage_integrable : IntegrableOn pwGammaMobiusPreimage (Ioi 0) := by
  have hsum := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    pwGammaMobiusAbelAtom_integrable pwGammaMobiusAbelAtom_norm_integrals_summable
  exact IntegrableOn.congr_fun hsum (fun x hx => (pwGammaMobiusPreimage_eq_abel hx).symm) measurableSet_Ioi

theorem pwGammaRaySource_integral :
    (∫ x in Ioi (0 : ℝ), pwGammaRaySource x) = (Real.Gamma (3 / 2) : ℂ) := by
  have h : (∫ x in Ioi (0 : ℝ), pwGammaRaySource x) =
      ∫ x in Ioi (0 : ℝ), (‖pwGammaRaySource x‖ : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [pwGammaRaySource_eq hx, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [h, integral_complex_ofReal, pwGammaRaySource_norm_integral]

theorem pwGammaMobiusAbelAtom_integral (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusAbelAtom n x) =
      ((Sieve.mertensM n / ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) * (Real.Gamma (3 / 2) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusAbelAtom_zero, pwGammaMertens_zero]
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn1 : 0 < (n : ℝ) + 1 := by positivity
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnr.ne'
    have hn1C : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast hn1.ne'
    change (∫ x in Ioi (0 : ℝ), (Sieve.mertensM n : ℂ) *
      (pwGammaRaySource ((n : ℝ) * x) - pwGammaRaySource (((n : ℝ) + 1) * x))) = _
    rw [integral_const_mul,
      integral_sub (pwGammaRaySource_dilation_integrable hnr) (pwGammaRaySource_dilation_integrable hn1),
      integral_comp_mul_left_Ioi pwGammaRaySource 0 hnr,
      integral_comp_mul_left_Ioi pwGammaRaySource 0 hn1]
    simp only [mul_zero, pwGammaRaySource_integral, Complex.real_smul, Complex.ofReal_inv]
    push_cast
    field_simp [hnC, hn1C]
    ring

/-- Complete signed cancellation of global mass; the source itself is nonzero. -/
theorem pwGammaMobiusPreimage_integral_zero :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusPreimage x) = 0 := by
  have hsource : (∫ x in Ioi (0 : ℝ), pwGammaMobiusPreimage x) =
      ∫ x in Ioi (0 : ℝ), ∑' n, pwGammaMobiusAbelAtom n x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => pwGammaMobiusPreimage_eq_abel hx
  rw [hsource, ← integral_tsum_of_summable_integral_norm pwGammaMobiusAbelAtom_integrable
    pwGammaMobiusAbelAtom_norm_integrals_summable]
  simp_rw [pwGammaMobiusAbelAtom_integral]
  rw [tsum_mul_right]
  have hcast := Complex.ofRealCLM.map_tsum deningerMertensHarmonic_summable
  change ((∑' n : ℕ, Sieve.mertensM n / ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) =
    ∑' n : ℕ, ((Sieve.mertensM n / ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) at hcast
  rw [← hcast]
  change (deningerHarmonicLimit : ℂ) * (Real.Gamma (3 / 2) : ℂ) = 0
  rw [deningerHarmonicLimit_eq_zero, Complex.ofReal_zero, zero_mul]


/-- Every positive dilation of the admitted source still has zero mass. -/
theorem pwGammaMobiusPreimage_dilation_integral_zero {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusPreimage (r * x)) = 0 := by
  rw [integral_comp_mul_left_Ioi pwGammaMobiusPreimage 0 hr, mul_zero,
    pwGammaMobiusPreimage_integral_zero, smul_zero]

/-- The complete arithmetic reconstruction is itself integrable. -/
theorem pwGammaMobiusReconstruction_integrable :
    IntegrableOn (deningerRaySum pwGammaMobiusPreimage) (Ioi 0) := by
  exact IntegrableOn.congr_fun pwGammaRaySource_integrable
    (fun x hx => (pwGammaMobius_rightInverse hx).symm) measurableSet_Ioi

theorem pwGammaMobiusReconstruction_integral :
    (∫ x in Ioi (0 : ℝ), deningerRaySum pwGammaMobiusPreimage x) =
      (Real.Gamma (3 / 2) : ℂ) := by
  rw [← pwGammaRaySource_integral]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => pwGammaMobius_rightInverse hx

/-- The entire source boundary defect survives the signed zero-mass preimage. -/
theorem pwGammaMobiusReconstruction_integral_defect :
    (∫ x in Ioi (0 : ℝ), deningerRaySum pwGammaMobiusPreimage x) -
      (∑' n : ℕ, ∫ x in Ioi (0 : ℝ), pwGammaMobiusPreimage (((n : ℝ) + 1) * x)) =
        (Real.Gamma (3 / 2) : ℂ) := by
  rw [pwGammaMobiusReconstruction_integral]
  have hzero : ∀ n : ℕ, (∫ x in Ioi (0 : ℝ), pwGammaMobiusPreimage (((n : ℝ) + 1) * x)) = 0 :=
    fun n => pwGammaMobiusPreimage_dilation_integral_zero (by positivity)
  simp only [hzero, tsum_zero, sub_zero]

/-- Absolute integral interchange for the reconstructed source is impossible. -/
theorem pwGammaMobiusReconstruction_not_summable_norm_integrals :
    ¬ Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ),
      ‖pwGammaMobiusPreimage (((n : ℝ) + 1) * x)‖) := by
  intro hs
  have hint : ∀ n : ℕ, IntegrableOn
      (fun x => pwGammaMobiusPreimage (((n : ℝ) + 1) * x)) (Ioi 0) := by
    intro n
    apply (integrableOn_Ioi_comp_mul_left_iff pwGammaMobiusPreimage 0 (by positivity)).mpr
    simpa only [mul_zero] using pwGammaMobiusPreimage_integrable
  have hswap := integral_tsum_of_summable_integral_norm hint hs
  change (∑' n : ℕ, ∫ x in Ioi (0 : ℝ), pwGammaMobiusPreimage (((n : ℝ) + 1) * x)) =
    (∫ x in Ioi (0 : ℝ), deningerRaySum pwGammaMobiusPreimage x) at hswap
  have hdefect := pwGammaMobiusReconstruction_integral_defect
  rw [hswap, sub_self] at hdefect
  have hGamma : 0 < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  exact (Complex.ofReal_ne_zero.mpr hGamma.ne') hdefect.symm


/-- The admitted zero-mass source represents a nonzero L1 class. -/
theorem pwGammaMobiusPreimage_integral_norm_pos :
    0 < ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusPreimage x‖ := by
  have hn : 0 ≤ ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusPreimage x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  by_contra h
  have hz : (∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusPreimage x‖) = 0 := le_antisymm (not_lt.mp h) hn
  apply pwGammaMobiusReconstruction_not_summable_norm_integrals
  have hzero : ∀ n : ℕ, (∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusPreimage (((n : ℝ) + 1) * x)‖) = 0 := by
    intro n
    rw [integral_comp_mul_left_Ioi (fun x => ‖pwGammaMobiusPreimage x‖) 0 (by positivity),
      mul_zero, hz, smul_zero]
  simp only [hzero, summable_zero]

/-- Full closed source statement, including the exact reconstruction defect. -/
theorem pwGammaMobiusSignedReconstruction_closed :
    IntegrableOn pwGammaMobiusPreimage (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusPreimage x) = 0 ∧
    (∃ x : ℝ, 0 < x ∧ pwGammaMobiusPreimage x ≠ 0) ∧
    (0 < ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusPreimage x‖) ∧
    IntegrableOn (deningerRaySum pwGammaMobiusPreimage) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), deningerRaySum pwGammaMobiusPreimage x) = (Real.Gamma (3 / 2) : ℂ) ∧
    (∀ r : ℝ, 0 < r → (∫ x in Ioi (0 : ℝ), pwGammaMobiusPreimage (r * x)) = 0) ∧
    (¬ Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusPreimage (((n : ℝ) + 1) * x)‖)) :=
  ⟨pwGammaMobiusPreimage_integrable, pwGammaMobiusPreimage_integral_zero,
    pwGammaMobiusPreimage_nontrivial, pwGammaMobiusPreimage_integral_norm_pos,
    pwGammaMobiusReconstruction_integrable,
    pwGammaMobiusReconstruction_integral, fun _ hr => pwGammaMobiusPreimage_dilation_integral_zero hr,
    pwGammaMobiusReconstruction_not_summable_norm_integrals⟩

end
end RHTower
