import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusCoordinateGenerator

/-!
# Signed coordinate endpoint and separation from the arithmetic current

The actual weighted shift at zero is admitted by a complete signed Abel assembly.
Its mass, and the mass of the weighted coordinate derivative, vanish. Every
constant combination of the source and its coordinate derivative therefore
retains an exact nonzero mass defect from the full logarithmic current, giving
an explicit positive L1 norm gap. No spectral stationarity is assumed or proved.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

def pwGammaRayFirstMomentSource (x : ℝ) : ℂ := (x : ℂ)*pwGammaRaySource x

private theorem pwGammaCoordinateEndpoint_second_eq {x : ℝ} (hx : 0 < x) :
    x^2*‖pwGammaRaySource x‖ = Real.exp (-x)*x^((7/2 : ℝ)-1) := by
  rw [pwGammaRaySource_eq hx, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.sqrt_eq_rpow, show (7/2 : ℝ)-1=2+1/2 by ring, Real.rpow_add hx, Real.rpow_two]
  ring

theorem pwGammaRaySource_second_moment_integrable :
    IntegrableOn (fun x : ℝ => x^2*‖pwGammaRaySource x‖) (Ioi 0) :=
  IntegrableOn.congr_fun (Real.GammaIntegral_convergent (s := 7/2) (by positivity))
    (fun _ hx => (pwGammaCoordinateEndpoint_second_eq hx).symm) measurableSet_Ioi

theorem pwGammaRaySource_second_moment_integral :
    (∫ x in Ioi (0 : ℝ), x^2*‖pwGammaRaySource x‖) = Real.Gamma (7/2) := by
  rw [Real.Gamma_eq_integral (s := 7/2) (by positivity)]
  exact setIntegral_congr_fun measurableSet_Ioi fun _ hx => pwGammaCoordinateEndpoint_second_eq hx

private theorem pwGammaCoordinateEndpoint_R_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => pwGammaRayFirstMomentSource (r*x)) (Ioi 0) := by
  apply (integrableOn_Ioi_comp_mul_left_iff pwGammaRayFirstMomentSource 0 hr).mpr
  simp only [mul_zero]
  change IntegrableOn (fun x : ℝ => (x : ℂ)*pwGammaRaySource x) (Ioi 0)
  exact pwGammaRaySource_mul_moment_integrable

private theorem pwGammaCoordinateEndpoint_first_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => x*‖pwGammaRaySource (r*x)‖) (Ioi 0) := by
  have hh : IntegrableOn (fun x => (r*x)*‖pwGammaRaySource (r*x)‖) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (fun y => y*‖pwGammaRaySource y‖) 0 hr).mpr
    simpa only [mul_zero] using pwGammaRaySource_first_moment_integrable
  refine IntegrableOn.congr_fun (hh.const_mul r⁻¹) (fun x _ => ?_) measurableSet_Ioi
  field_simp

private theorem pwGammaCoordinateEndpoint_second_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => x^2*‖pwGammaRaySource (r*x)‖) (Ioi 0) := by
  have hh : IntegrableOn (fun x => (r*x)^2*‖pwGammaRaySource (r*x)‖) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (fun y => y^2*‖pwGammaRaySource y‖) 0 hr).mpr
    simpa only [mul_zero] using pwGammaRaySource_second_moment_integrable
  refine IntegrableOn.congr_fun (hh.const_mul ((r⁻¹)^2)) (fun x _ => ?_) measurableSet_Ioi
  field_simp

private theorem pwGammaCoordinateEndpoint_first_integral {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), x*‖pwGammaRaySource (r*x)‖) = Real.Gamma (5/2)/r^2 := by
  have hf : (fun x => x*‖pwGammaRaySource (r*x)‖) =
      (fun x => r⁻¹*((r*x)*‖pwGammaRaySource (r*x)‖)) := by funext x; field_simp
  rw [hf, integral_const_mul, integral_comp_mul_left_Ioi (fun y => y*‖pwGammaRaySource y‖) 0 hr,
    mul_zero, smul_eq_mul, pwGammaRaySource_first_moment_integral]
  ring

private theorem pwGammaCoordinateEndpoint_second_integral {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), x^2*‖pwGammaRaySource (r*x)‖) = Real.Gamma (7/2)/r^3 := by
  have hf : (fun x => x^2*‖pwGammaRaySource (r*x)‖) =
      (fun x => (r⁻¹)^2*((r*x)^2*‖pwGammaRaySource (r*x)‖)) := by funext x; field_simp
  rw [hf, integral_const_mul, integral_comp_mul_left_Ioi (fun y => y^2*‖pwGammaRaySource y‖) 0 hr,
    mul_zero, smul_eq_mul, pwGammaRaySource_second_moment_integral]
  ring

theorem pwGammaRayFirstMomentSource_adjacent_norm_le {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    ‖pwGammaRayFirstMomentSource ((r+1)*x)-pwGammaRayFirstMomentSource (r*x)‖ ≤
      x*‖pwGammaRaySource ((r+1)*x)‖ + x*‖pwGammaRaySource (r*x)‖ + r*(x^2*‖pwGammaRaySource (r*x)‖) := by
  have heq : pwGammaRayFirstMomentSource ((r+1)*x)-pwGammaRayFirstMomentSource (r*x) =
      (x : ℂ)*pwGammaRaySource ((r+1)*x) + ((r*x : ℝ) : ℂ)*
        (pwGammaRaySource ((r+1)*x)-pwGammaRaySource (r*x)) := by
    simp only [pwGammaRayFirstMomentSource]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖(x : ℂ)*pwGammaRaySource ((r+1)*x)‖ +
        ‖((r*x : ℝ) : ℂ)*(pwGammaRaySource ((r+1)*x)-pwGammaRaySource (r*x))‖ := norm_add_le _ _
    _ = x*‖pwGammaRaySource ((r+1)*x)‖ + (r*x)*‖pwGammaRaySource ((r+1)*x)-pwGammaRaySource (r*x)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hx.le, Real.norm_of_nonneg (mul_pos hr hx).le]
    _ ≤ x*‖pwGammaRaySource ((r+1)*x)‖ + (r*x)*((1/r+x)*‖pwGammaRaySource (r*x)‖) := by
      gcongr
      exact pwGammaRaySource_adjacent_norm_le hr hx
    _ = _ := by field_simp; ring

theorem pwGammaRayFirstMomentSource_adjacent_integral_norm_le {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), ‖pwGammaRayFirstMomentSource ((r+1)*x)-pwGammaRayFirstMomentSource (r*x)‖) ≤
      (2*Real.Gamma (5/2)+Real.Gamma (7/2))/r^2 := by
  have hr1 : 0 < r+1 := by positivity
  have h1 := pwGammaCoordinateEndpoint_first_integrable hr1
  have h0 := pwGammaCoordinateEndpoint_first_integrable hr
  have h2 := (pwGammaCoordinateEndpoint_second_integrable hr).const_mul r
  have h10 : IntegrableOn (fun x => x*‖pwGammaRaySource ((r+1)*x)‖ + x*‖pwGammaRaySource (r*x)‖) (Ioi 0) := h1.add h0
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), x*‖pwGammaRaySource ((r+1)*x)‖ + x*‖pwGammaRaySource (r*x)‖ +
        r*(x^2*‖pwGammaRaySource (r*x)‖) := by
      apply integral_mono_ae ((pwGammaCoordinateEndpoint_R_integrable hr1).sub
        (pwGammaCoordinateEndpoint_R_integrable hr)).norm ((h1.add h0).add h2)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact pwGammaRayFirstMomentSource_adjacent_norm_le hr hx
    _ = Real.Gamma (5/2)/(r+1)^2 + Real.Gamma (5/2)/r^2 + r*(Real.Gamma (7/2)/r^3) := by
      rw [integral_add h10 h2, integral_add h1 h0, integral_const_mul,
        pwGammaCoordinateEndpoint_first_integral hr1, pwGammaCoordinateEndpoint_first_integral hr,
        pwGammaCoordinateEndpoint_second_integral hr]
    _ ≤ Real.Gamma (5/2)/r^2 + Real.Gamma (5/2)/r^2 + r*(Real.Gamma (7/2)/r^3) := by
      gcongr
      linarith
    _ = _ := by field_simp; ring

/-- Complete signed Abel atoms for the actual weighted coordinate shift at zero. -/
def pwGammaMobiusCoordinateAbelAtom (n : ℕ) (x : ℝ) : ℂ :=
  (Sieve.mertensM n : ℂ)*(pwGammaRayFirstMomentSource ((n : ℝ)*x)-
    pwGammaRayFirstMomentSource (((n : ℝ)+1)*x))

private theorem pwGammaCoordinateEndpoint_abel_zero : pwGammaMobiusCoordinateAbelAtom 0 = 0 := by
  funext x
  simp [pwGammaMobiusCoordinateAbelAtom, Sieve.mertensM]

theorem pwGammaMobiusCoordinateAbelAtom_integrable (n : ℕ) :
    IntegrableOn (pwGammaMobiusCoordinateAbelAtom n) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pwGammaCoordinateEndpoint_abel_zero]; exact integrable_zero ℝ ℂ _
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  exact ((pwGammaCoordinateEndpoint_R_integrable hnr).sub
    (pwGammaCoordinateEndpoint_R_integrable (by positivity : 0 < (n : ℝ)+1))).const_mul _

theorem pwGammaMobiusCoordinateAbelAtom_integral_norm_le (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusCoordinateAbelAtom n x‖) ≤
      (2*Real.Gamma (5/2)+Real.Gamma (7/2))*(|Sieve.mertensM n|/(n : ℝ)^2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaCoordinateEndpoint_abel_zero]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hrev : (fun x : ℝ => ‖pwGammaRayFirstMomentSource ((n : ℝ)*x)-
      pwGammaRayFirstMomentSource (((n : ℝ)+1)*x)‖) =
      (fun x : ℝ => ‖pwGammaRayFirstMomentSource (((n : ℝ)+1)*x)-
        pwGammaRayFirstMomentSource ((n : ℝ)*x)‖) := funext fun x => norm_sub_rev _ _
  simp only [pwGammaMobiusCoordinateAbelAtom, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, integral_const_mul]
  rw [hrev]
  calc
    _ ≤ |Sieve.mertensM n| *((2*Real.Gamma (5/2)+Real.Gamma (7/2))/(n : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (pwGammaRayFirstMomentSource_adjacent_integral_norm_le hnr) (abs_nonneg _)
    _ = _ := by ring

theorem pwGammaMobiusCoordinateAbelAtom_norm_integrals_summable :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusCoordinateAbelAtom n x‖) :=
  (deningerMertensM_invSq_summable.mul_left (2*Real.Gamma (5/2)+Real.Gamma (7/2))).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _) pwGammaMobiusCoordinateAbelAtom_integral_norm_le

theorem pwGammaRayFirstMomentSource_polynomial_moment_summable {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ)^k*‖pwGammaRayFirstMomentSource ((n : ℝ)*x)‖) := by
  refine ((pwGammaRaySource_polynomial_moment_summable hx (k+1)).mul_left x).congr (fun n => ?_)
  rw [pwGammaRayFirstMomentSource, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hx.le), pow_succ]
  ring

private theorem pwGammaCoordinateEndpoint_terminal_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => (Sieve.mertensM n : ℂ)*pwGammaRayFirstMomentSource ((n : ℝ)*x)) := by
  have hmaj : Summable (fun n : ℕ => (n : ℝ)*‖pwGammaRayFirstMomentSource ((n : ℝ)*x)‖ +
      ‖pwGammaRayFirstMomentSource ((n : ℝ)*x)‖) := by
    simpa only [pow_one, pow_zero, one_mul] using
      (pwGammaRayFirstMomentSource_polynomial_moment_summable hx 1).add
        (pwGammaRayFirstMomentSource_polynomial_moment_summable hx 0)
  refine Summable.of_norm_bounded hmaj (fun n => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← add_one_mul]
  exact mul_le_mul_of_nonneg_right (deningerMertensM_abs_le n) (norm_nonneg _)

theorem pwGammaMobiusCoordinateAbelAtom_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => pwGammaMobiusCoordinateAbelAtom n x) := by
  have hmaj : Summable (fun n : ℕ => (n : ℝ)*‖pwGammaRayFirstMomentSource ((n : ℝ)*x)‖ +
      ‖pwGammaRayFirstMomentSource ((n : ℝ)*x)‖) := by
    simpa only [pow_one, pow_zero, one_mul] using
      (pwGammaRayFirstMomentSource_polynomial_moment_summable hx 1).add
        (pwGammaRayFirstMomentSource_polynomial_moment_summable hx 0)
  have hnext : Summable (fun n : ℕ => (Sieve.mertensM n : ℂ)*
      pwGammaRayFirstMomentSource (((n : ℝ)+1)*x)) := by
    refine Summable.of_norm_bounded (hmaj.comp_injective Nat.succ_injective) (fun n => ?_)
    simp only [Function.comp_def, Nat.cast_succ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ ((n : ℝ)+1)*‖pwGammaRayFirstMomentSource (((n : ℝ)+1)*x)‖ :=
        mul_le_mul_of_nonneg_right (deningerMertensM_abs_le n) (norm_nonneg _)
      _ ≤ _ := le_add_of_nonneg_right (norm_nonneg _)
  exact ((pwGammaCoordinateEndpoint_terminal_summable hx).sub hnext).congr (fun n => by
    simp only [pwGammaMobiusCoordinateAbelAtom, mul_sub])

theorem pwGammaMobiusCoordinateAbel_boundary_tendsto_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => pwGammaRayFirstMomentSource ((n : ℝ)*x)*(Sieve.mertensM n : ℂ))
      atTop (𝓝 0) := by
  simpa only [mul_comm] using (pwGammaCoordinateEndpoint_terminal_summable hx).tendsto_atTop_zero

theorem pwGammaMobiusCoordinateAbel_finite (N : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.range N, pwGammaMobiusCoordinateAbelAtom n x) =
      (∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℂ) * pwGammaRayFirstMomentSource ((n : ℝ) * x)) -
        pwGammaRayFirstMomentSource ((N : ℝ) * x) * (Sieve.mertensM N : ℂ) := by
  classical
  let F : ℕ → ℂ := fun n => pwGammaRayFirstMomentSource ((n : ℝ) * x)
  let G : ℕ → ℂ := fun n => ((moebius n : ℤ) : ℂ)
  have hsum : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), G j) = (Sieve.mertensM n : ℂ) := by
    intro n
    simp only [Sieve.mertensM, G, Complex.ofReal_sum, Complex.ofReal_intCast]
  have hparts := Finset.sum_range_by_parts F G (N + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul, hsum] at hparts
  have hdiff : (∑ n ∈ Finset.range N, (F (n + 1) - F n) * (Sieve.mertensM n : ℂ)) =
      -(∑ n ∈ Finset.range N, pwGammaMobiusCoordinateAbelAtom n x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [F, pwGammaMobiusCoordinateAbelAtom, Nat.cast_add, Nat.cast_one]
    ring
  have hmain : (∑ n ∈ Finset.range (N + 1), F n * G n) =
      (∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℂ) * pwGammaRayFirstMomentSource ((n : ℝ) * x)) := by
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [hdiff, hmain] at hparts
  dsimp only [F] at hparts
  linear_combination -hparts


theorem pwGammaMobiusCoordinateShiftAtom_zero_eq (n : ℕ) (x : ℝ) :
    pwGammaMobiusCoordinateShiftAtom 0 n x = ((moebius n : ℤ) : ℂ)*pwGammaRayFirstMomentSource ((n : ℝ)*x) := by
  simp only [pwGammaMobiusCoordinateShiftAtom_eq, neg_zero, zero_mul, Complex.exp_zero,
    mul_one, pwGammaRayFirstMomentSource]

theorem pwGammaMobiusTilt_weighted_shift_zero_eq_abel {x : ℝ} (hx : 0 < x) :
    (x : ℂ)*pwGammaMobiusTilt (-1) x = ∑' n, pwGammaMobiusCoordinateAbelAtom n x := by
  have hsF : Summable (fun n : ℕ => pwGammaMobiusCoordinateShiftAtom 0 n x) := by
    change Summable (fun n => (x : ℂ)*pwGammaMobiusGlobalAtom (0-1) n x)
    simp only [zero_sub]
    exact (pwGammaMobiusTilt_summable (-1) hx).mul_left (x : ℂ)
  have hsR : Summable (fun n : ℕ => ((moebius n : ℤ) : ℂ)*pwGammaRayFirstMomentSource ((n : ℝ)*x)) :=
    hsF.congr (fun n => pwGammaMobiusCoordinateShiftAtom_zero_eq n x)
  have hpartial := hsR.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hlim := hpartial.sub (pwGammaMobiusCoordinateAbel_boundary_tendsto_zero hx)
  simp only [sub_zero] at hlim
  have hlim' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, pwGammaMobiusCoordinateAbelAtom n x)
      atTop (𝓝 (∑' n, ((moebius n : ℤ) : ℂ)*pwGammaRayFirstMomentSource ((n : ℝ)*x))) :=
    hlim.congr fun N => (pwGammaMobiusCoordinateAbel_finite N x).symm
  calc
    _ = ∑' n, pwGammaMobiusCoordinateShiftAtom 0 n x := by
      simpa only [zero_sub] using pwGammaMobiusTilt_weighted_shift_eq_tsum 0 x
    _ = ∑' n, ((moebius n : ℤ) : ℂ)*pwGammaRayFirstMomentSource ((n : ℝ)*x) :=
      tsum_congr (fun n => pwGammaMobiusCoordinateShiftAtom_zero_eq n x)
    _ = _ := tendsto_nhds_unique hlim' (pwGammaMobiusCoordinateAbelAtom_summable hx).hasSum.tendsto_sum_nat

/-- Signed admission of the actual weighted shifted source at the absolute boundary. -/
theorem pwGammaMobiusTilt_weighted_shift_zero_integrable :
    IntegrableOn (fun x : ℝ => (x : ℂ)*pwGammaMobiusTilt (-1) x) (Ioi 0) := by
  have hh := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    pwGammaMobiusCoordinateAbelAtom_integrable pwGammaMobiusCoordinateAbelAtom_norm_integrals_summable
  exact IntegrableOn.congr_fun hh (fun x hx => (pwGammaMobiusTilt_weighted_shift_zero_eq_abel hx).symm)
    measurableSet_Ioi

private theorem pwGammaCoordinateEndpoint_Gamma_step :
    Real.Gamma (5/2) = (3/2 : ℝ)*Real.Gamma (3/2) := by
  have h := Real.Gamma_add_one (s := 3/2) (by positivity)
  rwa [show (3/2 : ℝ)+1=5/2 by ring] at h

theorem pwGammaMobiusCoordinateAbelAtom_integral (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusCoordinateAbelAtom n x) =
      (3/2 : ℂ)*(∫ x in Ioi (0 : ℝ), pwGammaMobiusAbelAtom n x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaCoordinateEndpoint_abel_zero, pwGammaMobiusAbelAtom, Sieve.mertensM]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ)+1 := by positivity
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnr.ne'
  have hn1C : (n : ℂ)+1 ≠ 0 := by exact_mod_cast hn1.ne'
  change (∫ x in Ioi (0 : ℝ), (Sieve.mertensM n : ℂ)*
    (pwGammaRayFirstMomentSource ((n : ℝ)*x)-pwGammaRayFirstMomentSource (((n : ℝ)+1)*x))) = _
  rw [integral_const_mul, integral_sub (pwGammaCoordinateEndpoint_R_integrable hnr)
    (pwGammaCoordinateEndpoint_R_integrable hn1), integral_comp_mul_left_Ioi pwGammaRayFirstMomentSource 0 hnr,
    integral_comp_mul_left_Ioi pwGammaRayFirstMomentSource 0 hn1, pwGammaMobiusAbelAtom_integral]
  simp only [mul_zero, pwGammaRayFirstMomentSource, pwGammaRaySource_mul_moment_integral,
    pwGammaCoordinateEndpoint_Gamma_step, Complex.real_smul, Complex.ofReal_inv]
  push_cast
  field_simp [hnC, hn1C]
  ring

/-- The admitted weighted coordinate forcing has zero mass at the original signed source. -/
theorem pwGammaMobiusTilt_weighted_shift_zero_integral :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)*pwGammaMobiusTilt (-1) x) = 0 := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaMobiusTilt_weighted_shift_zero_eq_abel hx),
    ← integral_tsum_of_summable_integral_norm pwGammaMobiusCoordinateAbelAtom_integrable
      pwGammaMobiusCoordinateAbelAtom_norm_integrals_summable]
  simp_rw [pwGammaMobiusCoordinateAbelAtom_integral]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm pwGammaMobiusAbelAtom_integrable
    pwGammaMobiusAbelAtom_norm_integrals_summable]
  have hsource : (∫ x in Ioi (0 : ℝ), ∑' n, pwGammaMobiusAbelAtom n x) =
      ∫ x in Ioi (0 : ℝ), pwGammaMobiusPreimage x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => (pwGammaMobiusPreimage_eq_abel hx).symm
  rw [hsource, pwGammaMobiusPreimage_integral_zero, mul_zero]

theorem pwGammaMobiusPreimage_weighted_coordinate_deriv {x : ℝ} (hx : 0 < x) :
    (x : ℂ)*deriv pwGammaMobiusPreimage x =
      (1/2 : ℂ)*pwGammaMobiusPreimage x-(x : ℂ)*pwGammaMobiusTilt (-1) x := by
  have heq : pwGammaMobiusTilt 0 = pwGammaMobiusPreimage := funext fun y => pwGammaMobiusTilt_zero y
  simpa only [heq, zero_sub] using pwGammaMobiusTilt_weighted_coordinate_deriv 0 hx

theorem pwGammaMobiusPreimage_weighted_coordinate_integrable :
    IntegrableOn (fun x : ℝ => (x : ℂ)*deriv pwGammaMobiusPreimage x) (Ioi 0) := by
  have hh := (pwGammaMobiusPreimage_integrable.const_mul (1/2 : ℂ)).sub
    pwGammaMobiusTilt_weighted_shift_zero_integrable
  exact IntegrableOn.congr_fun hh (fun x hx => (pwGammaMobiusPreimage_weighted_coordinate_deriv hx).symm)
    measurableSet_Ioi

theorem pwGammaMobiusPreimage_weighted_coordinate_integral :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)*deriv pwGammaMobiusPreimage x) = 0 := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaMobiusPreimage_weighted_coordinate_deriv hx)]
  rw [integral_sub (pwGammaMobiusPreimage_integrable.const_mul (1/2 : ℂ))
    pwGammaMobiusTilt_weighted_shift_zero_integrable, integral_const_mul,
    pwGammaMobiusPreimage_integral_zero, pwGammaMobiusTilt_weighted_shift_zero_integral, mul_zero, sub_zero]

/-- Every constant combination of the actual source and its coordinate generator is globally admitted. -/
theorem pwGammaMobius_generator_span_integrable (a c : ℂ) :
    IntegrableOn (fun x : ℝ => a*pwGammaMobiusPreimage x+c*((x : ℂ)*deriv pwGammaMobiusPreimage x)) (Ioi 0) :=
  (pwGammaMobiusPreimage_integrable.const_mul a).add
    (pwGammaMobiusPreimage_weighted_coordinate_integrable.const_mul c)

theorem pwGammaMobius_generator_span_integral (a c : ℂ) :
    (∫ x in Ioi (0 : ℝ), a*pwGammaMobiusPreimage x+c*((x : ℂ)*deriv pwGammaMobiusPreimage x)) = 0 := by
  rw [integral_add (pwGammaMobiusPreimage_integrable.const_mul a)
    (pwGammaMobiusPreimage_weighted_coordinate_integrable.const_mul c), integral_const_mul,
    integral_const_mul, pwGammaMobiusPreimage_integral_zero, pwGammaMobiusPreimage_weighted_coordinate_integral,
    mul_zero, mul_zero, add_zero]

/-- The full arithmetic current retains the same nonzero mass outside every such coordinate combination. -/
theorem pwGammaMobius_generator_span_mass_defect (a c : ℂ) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x-
      (a*pwGammaMobiusPreimage x+c*((x : ℂ)*deriv pwGammaMobiusPreimage x))) = (Real.Gamma (3/2) : ℂ) := by
  rw [integral_sub pwGammaMobiusLogCurrent_integrable (pwGammaMobius_generator_span_integrable a c),
    pwGammaMobiusLogCurrent_integral, pwGammaMobius_generator_span_integral, sub_zero]

theorem pwGammaMobius_generator_span_norm_gap (a c : ℂ) :
    Real.Gamma (3/2) ≤ ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusLogCurrent x-
      (a*pwGammaMobiusPreimage x+c*((x : ℂ)*deriv pwGammaMobiusPreimage x))‖ := by
  have hGamma : 0 < Real.Gamma (3/2) := Real.Gamma_pos_of_pos (by positivity)
  calc
    _ = ‖(Real.Gamma (3/2) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hGamma.le]
    _ = ‖∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x-
        (a*pwGammaMobiusPreimage x+c*((x : ℂ)*deriv pwGammaMobiusPreimage x))‖ := by
      rw [pwGammaMobius_generator_span_mass_defect]
    _ ≤ _ := norm_integral_le_integral_norm _

theorem pwGammaMobiusLogCurrent_not_coordinate_span (a c : ℂ) :
    ¬ ∀ x : ℝ, 0 < x → pwGammaMobiusLogCurrent x =
      a*pwGammaMobiusPreimage x+c*((x : ℂ)*deriv pwGammaMobiusPreimage x) := by
  intro heq
  have hzero : (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x-
      (a*pwGammaMobiusPreimage x+c*((x : ℂ)*deriv pwGammaMobiusPreimage x))) = 0 := by
    calc
      _ = ∫ _x in Ioi (0 : ℝ), (0 : ℂ) :=
        setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [heq x hx, sub_self]
      _ = 0 := integral_zero _ _
  have hGamma : (Real.Gamma (3/2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < 3/2)).ne'
  exact hGamma ((pwGammaMobius_generator_span_mass_defect a c).symm.trans hzero)

/-- Closed signed endpoint, exact source mass separation and a positive norm gap. -/
theorem pwGammaMobiusCoordinateEndpoint_closed :
    IntegrableOn (fun x : ℝ => (x : ℂ)*pwGammaMobiusTilt (-1) x) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), (x : ℂ)*pwGammaMobiusTilt (-1) x) = 0 ∧
    IntegrableOn (fun x : ℝ => (x : ℂ)*deriv pwGammaMobiusPreimage x) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), (x : ℂ)*deriv pwGammaMobiusPreimage x) = 0 ∧
    (∀ a c : ℂ,
      (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x-
        (a*pwGammaMobiusPreimage x+c*((x : ℂ)*deriv pwGammaMobiusPreimage x))) = (Real.Gamma (3/2) : ℂ) ∧
      Real.Gamma (3/2) ≤ ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusLogCurrent x-
        (a*pwGammaMobiusPreimage x+c*((x : ℂ)*deriv pwGammaMobiusPreimage x))‖) ∧
    (∀ a c : ℂ, ¬ ∀ x : ℝ, 0 < x → pwGammaMobiusLogCurrent x =
      a*pwGammaMobiusPreimage x+c*((x : ℂ)*deriv pwGammaMobiusPreimage x)) :=
  ⟨pwGammaMobiusTilt_weighted_shift_zero_integrable, pwGammaMobiusTilt_weighted_shift_zero_integral,
    pwGammaMobiusPreimage_weighted_coordinate_integrable, pwGammaMobiusPreimage_weighted_coordinate_integral,
    fun a c => ⟨pwGammaMobius_generator_span_mass_defect a c, pwGammaMobius_generator_span_norm_gap a c⟩,
    pwGammaMobiusLogCurrent_not_coordinate_span⟩

end
end RHTower
