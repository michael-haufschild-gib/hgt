import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusFrullaniCurrent

/-!
# Signed global admission of the actual Frullani response

The complete response is integrable on the product of the two positive rays.
Its exact signed Abel assembly has summable norm integrals, even at the
boundary where the original separate atom norm masses are not summable.
Finite summation retains its terminal until its limit is proved. Valid Fubini
preserves the nonzero arithmetic mass; admission supplies no spectral balance.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section
local notation "μ₊" => (volume.restrict (Ioi (0 : ℝ)))

def pwGammaFrullaniIncrement (n : ℕ) (h : ℝ) : ℂ :=
  pwGammaFrullaniKernel n h-pwGammaFrullaniKernel (n+1) h

theorem pwGammaFrullaniIncrement_eq_real (n : ℕ) (h : ℝ) :
    pwGammaFrullaniIncrement n h =
      (((Real.exp (-((n : ℝ)*h))-Real.exp (-(((n : ℝ)+1)*h)))/h : ℝ) : ℂ) := by
  simp only [pwGammaFrullaniIncrement, pwGammaFrullaniKernel_eq_real, Nat.cast_add, Nat.cast_one,
    ← Complex.ofReal_sub]
  congr 1
  ring

theorem pwGammaFrullaniIncrement_integrable {n : ℕ} (hn : 0 < n) :
    IntegrableOn (pwGammaFrullaniIncrement n) (Ioi 0) :=
  (pwGammaFrullaniKernel_integrable hn).sub (pwGammaFrullaniKernel_integrable (Nat.succ_pos n))

theorem pwGammaFrullaniIncrement_integral {n : ℕ} (hn : 0 < n) :
    (∫ h in Ioi (0 : ℝ), pwGammaFrullaniIncrement n h) =
      ((Real.log ((n : ℝ)+1)-Real.log (n : ℝ) : ℝ) : ℂ) := by
  simp only [pwGammaFrullaniIncrement]
  rw [integral_sub (pwGammaFrullaniKernel_integrable hn)
    (pwGammaFrullaniKernel_integrable (Nat.succ_pos n)), pwGammaFrullaniKernel_integral hn,
    pwGammaFrullaniKernel_integral (Nat.succ_pos n)]
  push_cast
  ring

theorem pwGammaFrullaniIncrement_norm_eq (n : ℕ) {h : ℝ} (hh : 0 < h) :
    ‖pwGammaFrullaniIncrement n h‖ = (pwGammaFrullaniIncrement n h).re := by
  have he : Real.exp (-(((n : ℝ)+1)*h)) ≤ Real.exp (-((n : ℝ)*h)) := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [pwGammaFrullaniIncrement_eq_real, Complex.norm_real, Complex.ofReal_re,
    Real.norm_of_nonneg (div_nonneg (sub_nonneg.mpr he) hh.le)]

theorem pwGammaFrullaniIncrement_norm_integral {n : ℕ} (hn : 0 < n) :
    (∫ h in Ioi (0 : ℝ), ‖pwGammaFrullaniIncrement n h‖) =
      Real.log ((n : ℝ)+1)-Real.log (n : ℝ) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun h hh => pwGammaFrullaniIncrement_norm_eq n hh)]
  have hre := integral_re (pwGammaFrullaniIncrement_integrable hn)
  change (∫ h in Ioi (0 : ℝ), (pwGammaFrullaniIncrement n h).re) =
    (∫ h in Ioi (0 : ℝ), pwGammaFrullaniIncrement n h).re at hre
  rw [hre, pwGammaFrullaniIncrement_integral hn, Complex.ofReal_re]

theorem pwGammaFrullaniKernel_norm_le {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) :
    ‖pwGammaFrullaniKernel n h‖ ≤ Real.exp (-h)/h := by
  rw [pwGammaFrullaniKernel_norm_eq hn hh, pwGammaFrullaniKernel_eq_real,
    Complex.ofReal_re, ← neg_div, neg_sub]
  exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hh.le

/-- Actual signed Abel atom on the two positive rays, with translation coordinate first. -/
def pwGammaMobiusFrullaniAbelAtom (n : ℕ) (p : ℝ × ℝ) : ℂ :=
  (Sieve.mertensM n : ℂ)*(pwGammaFrullaniKernel n p.1*pwGammaRaySource ((n : ℝ)*p.2)-
    pwGammaFrullaniKernel (n+1) p.1*pwGammaRaySource (((n : ℝ)+1)*p.2))

private theorem pwGammaFrullaniAbel_zero : pwGammaMobiusFrullaniAbelAtom 0 = 0 := by
  funext p
  simp [pwGammaMobiusFrullaniAbelAtom, Sieve.mertensM]

private theorem pwGammaFrullani_Q_dilation_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => pwGammaRaySource (r*x)) (Ioi 0) := by
  apply (integrableOn_Ioi_comp_mul_left_iff pwGammaRaySource 0 hr).mpr
  simpa only [mul_zero] using pwGammaRaySource_integrable

theorem pwGammaMobiusFrullaniAbelAtom_integrable (n : ℕ) :
    Integrable (pwGammaMobiusFrullaniAbelAtom n) (μ₊.prod μ₊) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pwGammaFrullaniAbel_zero]; exact integrable_zero _ _ _
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 := (pwGammaFrullaniKernel_integrable hn).mul_prod (pwGammaFrullani_Q_dilation_integrable hnr)
  have h1 := (pwGammaFrullaniKernel_integrable (Nat.succ_pos n)).mul_prod
    (pwGammaFrullani_Q_dilation_integrable (by positivity : 0 < (n : ℝ)+1))
  exact (h0.sub h1).const_mul _

theorem pwGammaMobiusFrullaniAbelAtom_split (n : ℕ) (p : ℝ × ℝ) :
    pwGammaMobiusFrullaniAbelAtom n p = pwGammaFrullaniKernel n p.1*pwGammaMobiusAbelAtom n p.2+
      ((Sieve.mertensM n : ℂ)*pwGammaFrullaniIncrement n p.1)*pwGammaRaySource (((n : ℝ)+1)*p.2) := by
  simp only [pwGammaMobiusFrullaniAbelAtom, pwGammaMobiusAbelAtom, pwGammaFrullaniIncrement]
  ring

private theorem pwGammaFrullani_Q_dilation_norm_integral {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), ‖pwGammaRaySource (r*x)‖) = Real.Gamma (3/2)/r := by
  rw [integral_comp_mul_left_Ioi (fun x => ‖pwGammaRaySource x‖) 0 hr,
    mul_zero, smul_eq_mul, pwGammaRaySource_norm_integral]
  ring

theorem pwGammaMobiusFrullaniAbelAtom_integral_norm_le (n : ℕ) :
    (∫ p, ‖pwGammaMobiusFrullaniAbelAtom n p‖ ∂(μ₊.prod μ₊)) ≤
      (Real.Gamma (3/2)+Real.Gamma (5/2))*(|Sieve.mertensM n| *Real.log (n : ℝ)/(n : ℝ)^2)+
        Real.Gamma (3/2)*(|Sieve.mertensM n|/(n : ℝ)^2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaFrullaniAbel_zero, Sieve.mertensM]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ)+1 := by positivity
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hG : 0 ≤ Real.Gamma (3/2) := (Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < 3/2)).le
  have hd := log_natCast_succ_sub_log_natCast_le_inv n hn
  have hu := (pwGammaFrullaniKernel_integrable hn).norm.mul_prod (pwGammaMobiusAbelAtom_integrable n).norm
  have hv := ((pwGammaFrullaniIncrement_integrable hn).norm.const_mul |Sieve.mertensM n|).mul_prod
    (pwGammaFrullani_Q_dilation_integrable hn1).norm
  calc
    _ ≤ ∫ p : ℝ × ℝ, ‖pwGammaFrullaniKernel n p.1‖*‖pwGammaMobiusAbelAtom n p.2‖+
        (|Sieve.mertensM n| * ‖pwGammaFrullaniIncrement n p.1‖)*‖pwGammaRaySource (((n : ℝ)+1)*p.2)‖
        ∂(μ₊.prod μ₊) := by
      apply integral_mono_ae (pwGammaMobiusFrullaniAbelAtom_integrable n).norm (hu.add hv)
      filter_upwards [] with p
      rw [pwGammaMobiusFrullaniAbelAtom_split]
      calc
        _ ≤ ‖pwGammaFrullaniKernel n p.1*pwGammaMobiusAbelAtom n p.2‖+
            ‖((Sieve.mertensM n : ℂ)*pwGammaFrullaniIncrement n p.1)*pwGammaRaySource (((n : ℝ)+1)*p.2)‖ :=
          norm_add_le _ _
        _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Pi.add_apply]
    _ = Real.log (n : ℝ)*(∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusAbelAtom n x‖)+
        (|Sieve.mertensM n| *(Real.log ((n : ℝ)+1)-Real.log (n : ℝ)))*(Real.Gamma (3/2)/((n : ℝ)+1)) := by
      rw [integral_add hu hv,
        integral_prod_mul (fun h : ℝ => ‖pwGammaFrullaniKernel n h‖)
          (fun x : ℝ => ‖pwGammaMobiusAbelAtom n x‖),
        integral_prod_mul (fun h : ℝ => |Sieve.mertensM n| * ‖pwGammaFrullaniIncrement n h‖)
          (fun x : ℝ => ‖pwGammaRaySource (((n : ℝ)+1)*x)‖), integral_const_mul,
        pwGammaFrullaniKernel_norm_integral hn, pwGammaFrullaniIncrement_norm_integral hn,
        pwGammaFrullani_Q_dilation_norm_integral hn1]
    _ ≤ Real.log (n : ℝ)*((Real.Gamma (3/2)+Real.Gamma (5/2))*(|Sieve.mertensM n|/(n : ℝ)^2))+
        (|Sieve.mertensM n| *(1/(n : ℝ)))*(Real.Gamma (3/2)/(n : ℝ)) := by
      gcongr
      · exact pwGammaMobiusAbelAtom_integral_norm_le n
      · linarith
    _ = _ := by ring

theorem pwGammaMobiusFrullaniAbelAtom_norm_integrals_summable :
    Summable (fun n : ℕ => ∫ p, ‖pwGammaMobiusFrullaniAbelAtom n p‖ ∂(μ₊.prod μ₊)) :=
  ((pwGammaMertens_log_invSq_summable.mul_left (Real.Gamma (3/2)+Real.Gamma (5/2))).add
    (deningerMertensM_invSq_summable.mul_left (Real.Gamma (3/2)))).of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _) pwGammaMobiusFrullaniAbelAtom_integral_norm_le

theorem pwGammaMobiusFrullaniAbelAtom_summable {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    Summable (fun n : ℕ => pwGammaMobiusFrullaniAbelAtom n (h,x)) := by
  let C : ℝ := Real.exp ((5/2)*Real.log (5/2)-5/2)
  let H : ℝ := Real.exp (-h)/h
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine Summable.of_norm_bounded (deningerMertensM_invSq_summable.mul_left (2*H*C/x^2)) (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaFrullaniAbel_zero, Sieve.mertensM]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx := mul_pos hnr hx
  have hq0 : ‖pwGammaRaySource ((n : ℝ)*x)‖ ≤ C/((n : ℝ)*x)^2 := pwGammaRaySource_norm_le_inv_sq hnx
  have hq1 : ‖pwGammaRaySource (((n : ℝ)+1)*x)‖ ≤ C/((n : ℝ)*x)^2 := by
    refine (pwGammaRaySource_norm_le_inv_sq (by positivity : 0 < ((n : ℝ)+1)*x)).trans ?_
    apply div_le_div_of_nonneg_left hC (sq_pos_of_pos hnx)
    gcongr
    linarith
  have hk0 : ‖pwGammaFrullaniKernel n h‖ ≤ H := pwGammaFrullaniKernel_norm_le hn hh
  have hk1 : ‖pwGammaFrullaniKernel (n+1) h‖ ≤ H := pwGammaFrullaniKernel_norm_le (Nat.succ_pos n) hh
  rw [pwGammaMobiusFrullaniAbelAtom, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |Sieve.mertensM n| * (‖pwGammaFrullaniKernel n h*pwGammaRaySource ((n : ℝ)*x)‖+
        ‖pwGammaFrullaniKernel (n+1) h*pwGammaRaySource (((n : ℝ)+1)*x)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
    _ ≤ |Sieve.mertensM n| * (H*(C/((n : ℝ)*x)^2)+H*(C/((n : ℝ)*x)^2)) := by
      simp only [norm_mul]
      gcongr
    _ = _ := by rw [mul_pow]; ring

theorem pwGammaMobiusFrullaniAbel_boundary_tendsto_zero {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    Tendsto (fun n : ℕ => (pwGammaFrullaniKernel n h*pwGammaRaySource ((n : ℝ)*x))*(Sieve.mertensM n : ℂ))
      atTop (𝓝 0) := by
  have hlim := (pwGammaMobiusAbel_boundary_tendsto_zero hx).norm.const_mul (Real.exp (-h)/h)
  simp only [norm_zero, mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_right (pwGammaFrullaniKernel_norm_le hn hh) (norm_nonneg _)

/-- Exact finite identity for the original two-variable source; no terminal is discarded. -/
theorem pwGammaMobiusFrullaniAbel_finite (N : ℕ) (h x : ℝ) :
    (∑ n ∈ Finset.range N, pwGammaMobiusFrullaniAbelAtom n (h,x)) =
      (∑ n ∈ Finset.range (N+1), pwGammaMobiusFrullaniAtom 0 x n h)-
        (pwGammaFrullaniKernel N h*pwGammaRaySource ((N : ℝ)*x))*(Sieve.mertensM N : ℂ) := by
  classical
  let F : ℕ → ℂ := fun n => pwGammaFrullaniKernel n h*pwGammaRaySource ((n : ℝ)*x)
  let G : ℕ → ℂ := fun n => ((moebius n : ℤ) : ℂ)
  have hsum : ∀ n : ℕ, (∑ j ∈ Finset.range (n+1), G j) = (Sieve.mertensM n : ℂ) := by
    intro n
    simp only [Sieve.mertensM, G, Complex.ofReal_sum, Complex.ofReal_intCast]
  have hparts := Finset.sum_range_by_parts F G (N+1)
  simp only [Nat.add_sub_cancel, smul_eq_mul, hsum] at hparts
  have hdiff : (∑ n ∈ Finset.range N, (F (n+1)-F n)*(Sieve.mertensM n : ℂ)) =
      -(∑ n ∈ Finset.range N, pwGammaMobiusFrullaniAbelAtom n (h,x)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [F, pwGammaMobiusFrullaniAbelAtom, Nat.cast_add, Nat.cast_one]
    ring
  have hmain : (∑ n ∈ Finset.range (N+1), F n*G n) =
      ∑ n ∈ Finset.range (N+1), pwGammaMobiusFrullaniAtom 0 x n h := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [F, G, pwGammaMobiusFrullaniAtom, pwGammaMobiusGlobalAtom, neg_zero,
      zero_mul, Complex.exp_zero, mul_one]
    ring
  rw [hdiff, hmain] at hparts
  dsimp only [F] at hparts
  linear_combination -hparts

theorem pwGammaMobiusFrullaniResponse_eq_abel {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    pwGammaMobiusFrullaniResponse 0 x h = ∑' n, pwGammaMobiusFrullaniAbelAtom n (h,x) := by
  have hpartial := (pwGammaMobiusFrullaniAtom_summable 0 hh.le hx).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  have hlim := hpartial.sub (pwGammaMobiusFrullaniAbel_boundary_tendsto_zero hh hx)
  simp only [sub_zero] at hlim
  have hlim' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, pwGammaMobiusFrullaniAbelAtom n (h,x))
      atTop (𝓝 (∑' n, pwGammaMobiusFrullaniAtom 0 x n h)) :=
    hlim.congr (fun N => (pwGammaMobiusFrullaniAbel_finite N h x).symm)
  rw [pwGammaMobiusFrullaniResponse_eq_tsum 0 hh.le hx]
  exact tendsto_nhds_unique hlim' (pwGammaMobiusFrullaniAbelAtom_summable hh hx).hasSum.tendsto_sum_nat

/-- Global signed admission on both positive rays, beyond the original atomwise boundary. -/
theorem pwGammaMobiusFrullaniResponse_joint_integrable :
    Integrable (fun p : ℝ × ℝ => pwGammaMobiusFrullaniResponse 0 p.2 p.1) (μ₊.prod μ₊) := by
  have hs := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    pwGammaMobiusFrullaniAbelAtom_integrable pwGammaMobiusFrullaniAbelAtom_norm_integrals_summable
  apply Integrable.congr hs
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  exact (pwGammaMobiusFrullaniResponse_eq_abel hp.1 hp.2).symm

theorem pwGammaMobiusFrullaniResponse_integral_interchange :
    (∫ h in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse 0 x h) =
      ∫ x in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse 0 x h :=
  integral_integral_swap pwGammaMobiusFrullaniResponse_joint_integrable

theorem pwGammaMobiusFrullaniResponse_reversed_integral :
    (∫ h in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse 0 x h) =
      (Real.Gamma (3/2) : ℂ) := by
  rw [pwGammaMobiusFrullaniResponse_integral_interchange, pwGammaMobiusFrullaniResponse_iterated_integral]

theorem pwGammaMobiusFrullaniResponse_joint_integral :
    (∫ p, pwGammaMobiusFrullaniResponse 0 p.2 p.1 ∂(μ₊.prod μ₊)) = (Real.Gamma (3/2) : ℂ) := by
  rw [integral_prod _ pwGammaMobiusFrullaniResponse_joint_integrable]
  exact pwGammaMobiusFrullaniResponse_reversed_integral

theorem pwGammaMobiusFrullaniResponse_joint_norm_pos :
    0 < ∫ p, ‖pwGammaMobiusFrullaniResponse 0 p.2 p.1‖ ∂(μ₊.prod μ₊) := by
  have hGamma : 0 < Real.Gamma (3/2) := Real.Gamma_pos_of_pos (by positivity)
  have hh := norm_integral_le_integral_norm
    (fun p : ℝ × ℝ => pwGammaMobiusFrullaniResponse 0 p.2 p.1) (μ := μ₊.prod μ₊)
  rw [pwGammaMobiusFrullaniResponse_joint_integral, Complex.norm_real, Real.norm_of_nonneg hGamma.le] at hh
  exact hGamma.trans_le hh

theorem pwGammaMobiusFrullaniAtom_zero_not_iterated_absolute :
    ¬ Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ),
      ‖pwGammaMobiusFrullaniAtom 0 x n h‖) := by
  simpa only [Complex.zero_re, lt_self_iff_false, iff_false] using
    pwGammaMobiusFrullaniAtom_iterated_absolute_admission 0

/-- Closed actual source, signed product admission, valid Fubini and surviving positive mass. -/
theorem pwGammaMobiusFrullaniJoint_closed :
    Integrable (fun p : ℝ × ℝ => pwGammaMobiusFrullaniResponse 0 p.2 p.1) (μ₊.prod μ₊) ∧
    (∫ h in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse 0 x h) =
      (∫ x in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse 0 x h) ∧
    (∫ p, pwGammaMobiusFrullaniResponse 0 p.2 p.1 ∂(μ₊.prod μ₊)) = (Real.Gamma (3/2) : ℂ) ∧
    0 < (∫ p, ‖pwGammaMobiusFrullaniResponse 0 p.2 p.1‖ ∂(μ₊.prod μ₊)) ∧
    ¬ Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ),
      ‖pwGammaMobiusFrullaniAtom 0 x n h‖) :=
  ⟨pwGammaMobiusFrullaniResponse_joint_integrable, pwGammaMobiusFrullaniResponse_integral_interchange,
    pwGammaMobiusFrullaniResponse_joint_integral, pwGammaMobiusFrullaniResponse_joint_norm_pos,
    pwGammaMobiusFrullaniAtom_zero_not_iterated_absolute⟩

end
end RHTower
