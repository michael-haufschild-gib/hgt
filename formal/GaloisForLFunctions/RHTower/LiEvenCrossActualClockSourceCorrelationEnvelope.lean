import GaloisForLFunctions.RHTower.LiEvenCrossActualClockHistoryBarrier
import GaloisForLFunctions.RHTower.LiClockThetaCompactGammaMarking
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Set MeasureTheory Filter Topology
namespace RHTower
noncomputable section
local notation "B" => liEvenCrossActualClockBorelKernel
local notation "K" => deriv liEvenCrossActualClockBorelKernel
local notation "K1" => deriv (deriv liEvenCrossActualClockBorelKernel)
local notation "ell" => liEvenCrossActualClockHistoryScale
local notation "e" => liEvenCrossActualClockHistoryScale
local notation "P" => liEvenCrossActualClockPrimitive
local notation "Resp" => liEvenCrossActualClockResponse
local notation "Dens" => liEvenCrossActualClockLogHistoryDensity
local notation "D" => liEvenCrossActualClockLogHistory
local notation "Cout" => liEvenCrossActualClockHistoryOutsideCorrelation
local notation "A0" => xiShiftAbsoluteMass 0

 def liEvenCrossActualClockSourceFirstZeroGuard (t : ℝ) : Prop :=
  20 < t ∧ D t = 0 ∧ ∀ s ∈ Icc 0 t, 0 ≤ D s

-- E02: arbitrary MATHEMATICAL mass/rate envelope on true oriented interval
 def liEvenCrossActualClockSourceTerminalEnvelope (M γ t s : ℝ) : ℝ :=
  M/2 * ∫ u in s..t, u * Real.exp (γ*u)

-- E03: full compact norm majorant, never actual Cout itself
 def liEvenCrossActualClockSourceNormMajorant (M γ t : ℝ) : ℝ :=
  ∫ s in e t..t,
    liEvenCrossActualClockSourceTerminalEnvelope M γ t s *
      max (s*K1 (t-s)-K (t-s)) 0

-- E04: literal M15 comparison budget
 def liEvenCrossActualClockSourceCorrelationBudget (t : ℝ) : ℝ :=
  t*K t + K t/2 * ∫ s in 0..e t, D s

-- E05: mathematical upper-envelope budget, same actual K and e
 def liEvenCrossActualClockSourceEnvelopeBudget (M γ t : ℝ) : ℝ :=
  K t * (t + M/24 * (e t)^3 * Real.exp (γ*(e t)))

-- E06: exact compact signed cost; values outside Ioc0t never used as bounded test
 def liEvenCrossActualClockHistoryMarkedCost (t u : ℝ) : ℝ :=
  if u ≤ e t then e t * K (t-e t) else u * K (t-u)


private theorem hgt_hs_response_smooth : ContDiff ℝ (⊤ : ℕ∞) Resp := by
  have heq : deriv P = Resp := funext fun t =>
    (hasDerivAt_liEvenCrossActualClockPrimitive t).deriv
  rw [← heq]
  exact (contDiff_infty_iff_deriv.mp contDiff_liEvenCrossActualClockPrimitive).2

private theorem hgt_hs_response_zero : Resp 0 = 0 := by
  simp [liEvenCrossActualClockResponse]

private def hgt_hs_jet (n : ℕ) (s : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, v ^ n * iteratedDeriv n Resp (v * s)

private theorem hgt_hs_integrand_continuous (n : ℕ) (s : ℝ) :
    Continuous (fun v : ℝ => v ^ n * iteratedDeriv n Resp (v * s)) := by
  have hc := hgt_hs_response_smooth.continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  exact (continuous_id.pow n).mul (hc.comp (continuous_id.mul continuous_const))

private theorem hgt_hs_integrand_admission (n : ℕ) (s : ℝ) :
    IntervalIntegrable (fun v : ℝ => v ^ n * iteratedDeriv n Resp (v * s)) volume 0 1 :=
  (hgt_hs_integrand_continuous n s).intervalIntegrable 0 1

private theorem hgt_hs_compact_bound (n : ℕ) (s₀ : ℝ) :
    ∃ C : ℝ, ∀ s ∈ Icc (s₀ - 1) (s₀ + 1), ∀ v ∈ Icc (0 : ℝ) 1,
      ‖v ^ n * iteratedDeriv n Resp (v * s)‖ ≤ C := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      p.2 ^ n * iteratedDeriv n Resp (p.2 * p.1)) :=
    (continuous_snd.pow n).mul
      ((hgt_hs_response_smooth.continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).comp
        (continuous_snd.mul continuous_fst))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := (Icc (s₀ - 1) (s₀ + 1)) ×ˢ (Icc (0 : ℝ) 1)) hc.continuousOn
  exact ⟨C, fun s hs v hv => hC (s, v) ⟨hs, hv⟩⟩

private theorem hgt_hs_integrand_deriv (n : ℕ) (v s : ℝ) :
    HasDerivAt (fun x : ℝ => v ^ n * iteratedDeriv n Resp (v * x))
      (v ^ (n + 1) * iteratedDeriv (n + 1) Resp (v * s)) s := by
  have h := ((hgt_hs_response_smooth.differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n))
    (v * s)).hasDerivAt
  have hi : HasDerivAt (fun x : ℝ => v * x) v s := by
    simpa using (hasDerivAt_id s).const_mul v
  apply ((h.comp s hi).const_mul (v ^ n)).congr_deriv
  rw [iteratedDeriv_succ, pow_succ]
  ring

private theorem hgt_hs_jet_deriv (n : ℕ) (s₀ : ℝ) :
    HasDerivAt (hgt_hs_jet n) (hgt_hs_jet (n + 1) s₀) s₀ := by
  obtain ⟨C, hC⟩ := hgt_hs_compact_bound (n + 1) s₀
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1) (bound := fun _ : ℝ => C)
    (F := fun s v : ℝ => v ^ n * iteratedDeriv n Resp (v * s))
    (F' := fun s v : ℝ => v ^ (n + 1) * iteratedDeriv (n + 1) Resp (v * s))
    (x₀ := s₀) (s := Icc (s₀ - 1) (s₀ + 1))
    (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun s =>
      (hgt_hs_integrand_continuous n s).aestronglyMeasurable.restrict)
    (hgt_hs_integrand_admission n s₀)
    (hgt_hs_integrand_continuous (n + 1) s₀).aestronglyMeasurable.restrict
    (ae_of_all volume fun v hv s hs => by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
      exact hC s hs v ⟨hv.1.le, hv.2⟩)
    intervalIntegrable_const
    (ae_of_all volume fun v _ s _ => hgt_hs_integrand_deriv n v s)).2

private theorem hgt_hs_quotient_eq_jet (s : ℝ) : P s / s = hgt_hs_jet 0 s := by
  by_cases hs : s = 0
  · subst s
    simp [hgt_hs_jet, hgt_hs_response_zero]
  have h := intervalIntegral.smul_integral_comp_mul_right
    (a := (0 : ℝ)) (b := 1) Resp s
  have hm : s * hgt_hs_jet 0 s = P s := by
    simpa only [hgt_hs_jet, iteratedDeriv_zero, pow_zero, one_mul, zero_mul,
      smul_eq_mul, liEvenCrossActualClockPrimitive] using h
  apply (div_eq_iff hs).2
  simpa [mul_comm] using hm.symm

private theorem hgt_hs_quotient_iteratedDeriv (n : ℕ) :
    iteratedDeriv n (fun s : ℝ => P s / s) = hgt_hs_jet n := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    exact funext hgt_hs_quotient_eq_jet
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun s => (hgt_hs_jet_deriv n s).deriv

private theorem hgt_hs_quotient_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => P s / s) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [hgt_hs_quotient_iteratedDeriv]
  exact fun s => (hgt_hs_jet_deriv n s).differentiableAt


section KernelHelpers
local notation "b" => liEvenCrossActualClockHistoryOriginSlope
private theorem hgt_ek_slope_smooth : ContDiff ℝ (⊤ : ℕ∞) K :=
  (contDiff_infty_iff_deriv.mp contDiff_liEvenCrossActualClockBorelKernel).2

private theorem hgt_ek_slope_deriv (t : ℝ) : HasDerivAt K (K1 t) t :=
  ((contDiff_infty_iff_deriv.mp hgt_ek_slope_smooth).1 t).hasDerivAt

private theorem hgt_ek_curvature_continuous : Continuous K1 :=
  (contDiff_infty_iff_deriv.mp hgt_ek_slope_smooth).2.continuous

private theorem hgt_ek_slope_integral (t : ℝ) : (∫ s in (0 : ℝ)..t, K1 s) = K t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hgt_ek_slope_deriv s) (hgt_ek_curvature_continuous.intervalIntegrable 0 t)
  simpa only [liEvenCrossActualClockHistory_origin.1, sub_zero] using h

private theorem hgt_ek_slope_lower {t : ℝ} (ht : 0 ≤ t) : b * t ≤ K t := by
  calc
    b * t = ∫ _s in (0 : ℝ)..t, b := by simp [mul_comm]
    _ ≤ ∫ s in (0 : ℝ)..t, K1 s :=
      intervalIntegral.integral_mono_on ht intervalIntegrable_const
        (hgt_ek_curvature_continuous.intervalIntegrable 0 t)
        (fun s hs => (liEvenCrossActualClockHistory_source_curvature.1 s hs.1).1)
    _ = K t := hgt_ek_slope_integral t

private theorem hgt_ek_source_basics :
    (0 < b) ∧ K 0 = 0 ∧
    (∀ t : ℝ, 0 ≤ t → b*t ≤ K t ∧ b ≤ K1 t) ∧
    MonotoneOn K1 (Ici 0) ∧
    (∀ t : ℝ, 0 < t → 0 < K t ∧ 0 < ell t ∧ ell t < t/4) := by
  refine ⟨liEvenCrossActualClockHistory_origin.2.2.2,
    liEvenCrossActualClockHistory_origin.1, ?_,
    liEvenCrossActualClockHistory_source_curvature.2, ?_⟩
  · intro t ht
    exact ⟨hgt_ek_slope_lower ht, (liEvenCrossActualClockHistory_source_curvature.1 t ht).1⟩
  · intro t ht
    exact ⟨liEvenCrossActualClockBorel_deriv_pos ht,
      (liEvenCrossActualClockHistory_geometry ht).2.2⟩

private theorem hgt_ek_scale_zero : ell 0 = 0 := by
  simp [liEvenCrossActualClockHistoryScale, liEvenCrossActualClockHistory_origin.1]

private theorem hgt_ek_scale_atTop : Tendsto ell atTop atTop := by
  have hratio : Tendsto (fun t : ℝ => K1 t / K t) atTop (𝓝 (0 : ℝ)) := by
    simpa only [show (2 : ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero]
      using tendsto_liEvenCrossActualClockBorel_second_div_deriv_zero
  apply tendsto_atTop.mpr
  intro M
  let L : ℝ := max M 1
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right M 1)
  have hsmall := hratio.eventually_lt_const (show (0 : ℝ) < 1/(4*L) by positivity)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with t hst ht
  have hK : 0 < K t := liEvenCrossActualClockBorel_deriv_pos ht
  have hK1 : 0 < K1 t := (liEvenCrossActualClockHistory_geometry ht).2.1
  change M ≤ K t / (4*K1 t)
  apply (le_div_iff₀ (show 0 < 4*K1 t by positivity)).2
  have hm := (div_lt_div_iff₀ hK (show 0 < 4*L by positivity)).mp hst
  have hML : M * (4*K1 t) ≤ L * (4*K1 t) :=
    mul_le_mul_of_nonneg_right (le_max_left M 1) (by positivity)
  nlinarith

end KernelHelpers


theorem contDiff_liEvenCrossActualClockLogHistoryDensity :
    ContDiff ℝ (⊤ : ℕ∞) Dens := hgt_hs_quotient_smooth

theorem contDiff_liEvenCrossActualClockLogHistory :
    ContDiff ℝ (⊤ : ℕ∞) D := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · intro t
    exact (hasDerivAt_liEvenCrossActualClockLogHistory t).differentiableAt
  · have heq : deriv D = Dens := funext fun t =>
      (hasDerivAt_liEvenCrossActualClockLogHistory t).deriv
    rw [heq]
    exact contDiff_liEvenCrossActualClockLogHistoryDensity

section ResponseFormula
local notation "F" => liEvenCrossActualClockResponse
theorem liEvenCrossActualClockLogHistoryDensity_iteratedDeriv (n : ℕ) (s : ℝ) :
    IntervalIntegrable (fun v : ℝ => v^n * iteratedDeriv n F (v*s)) volume 0 1 ∧
    iteratedDeriv n Dens s = ∫ v in 0..1, v^n * iteratedDeriv n F (v*s) := by
  refine ⟨hgt_hs_integrand_admission n s, ?_⟩
  exact congrFun (hgt_hs_quotient_iteratedDeriv n) s
end ResponseFormula

theorem tendsto_liEvenCrossActualClockHistoryScale_atTop : Tendsto e atTop atTop :=
  hgt_ek_scale_atTop

private theorem hgt_se_terminal_cont (M γ t : ℝ) :
    Continuous (fun s => liEvenCrossActualClockSourceTerminalEnvelope M γ t s) := by
  have hf : Continuous (fun u : ℝ => u * Real.exp (γ*u)) := by fun_prop
  have hi : Continuous (fun s : ℝ => ∫ u in t..s, u * Real.exp (γ*u)) := by
    exact continuous_iff_continuousAt.mpr fun s =>
      (hf.integral_hasStrictDerivAt t s).hasDerivAt.continuousAt
  have heq : (fun s => liEvenCrossActualClockSourceTerminalEnvelope M γ t s) =
      (fun s => M/2 * -(∫ u in t..s, u * Real.exp (γ*u))) := by
    funext s
    rw [liEvenCrossActualClockSourceTerminalEnvelope, intervalIntegral.integral_symm]
  rw [heq]
  exact continuous_const.mul hi.neg

private theorem hgt_se_outer_coefficient_cont (t : ℝ) :
    Continuous (fun s : ℝ => s*K1 (t-s)-K (t-s)) := by
  exact continuous_id.mul (hgt_ek_curvature_continuous.comp (continuous_const.sub continuous_id)) |>.sub
    (hgt_ek_slope_smooth.continuous.comp (continuous_const.sub continuous_id))

theorem liEvenCrossActualClockSourceEnvelope_compact_admission (M γ t : ℝ) :
    Continuous (fun s => liEvenCrossActualClockSourceTerminalEnvelope M γ t s) ∧
    IntervalIntegrable Dens volume 0 t ∧
    IntervalIntegrable D volume 0 (e t) ∧
    IntervalIntegrable (fun s => liEvenCrossActualClockSourceTerminalEnvelope M γ t s *
      max (s*K1 (t-s)-K (t-s)) 0) volume (e t) t := by
  exact ⟨hgt_se_terminal_cont M γ t,
    continuous_liEvenCrossActualClockLogHistoryDensity.intervalIntegrable _ _,
    contDiff_liEvenCrossActualClockLogHistory.continuous.intervalIntegrable _ _,
    ((hgt_se_terminal_cont M γ t).mul
      ((hgt_se_outer_coefficient_cont t).max continuous_const)).intervalIntegrable _ _⟩

private theorem hgt_se_density_bound {γ u : ℝ}
    (hγ : (1/300 : ℝ) ≤ γ) (hu : 0 ≤ u) :
    |Dens u| ≤ A0*u/2 * Real.exp (γ*u) := by
  by_cases hz : u = 0
  · subst u
    rw [liEvenCrossActualClockLogHistory_origin.1, abs_zero]
    simp
  have hu0 : 0 < u := by positivity
  have hA := xiShiftAbsoluteMass_pos 0
  have he : Real.exp (u/300) ≤ Real.exp (γ*u) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hγ hu]
  have hp := abs_liEvenCrossActualClockPrimitive_le u
  rw [abs_of_nonneg hu] at hp
  have hp' : |P u| ≤ A0*u^2/2 * Real.exp (γ*u) :=
    hp.trans (mul_le_mul_of_nonneg_left he (by positivity))
  change |P u/u| ≤ _
  rw [abs_div, abs_of_nonneg hu]
  apply (div_le_iff₀ hu0).2
  calc
    |P u| ≤ A0*u^2/2 * Real.exp (γ*u) := hp'
    _ = (A0*u/2 * Real.exp (γ*u))*u := by ring

theorem abs_liEvenCrossActualClockLogHistory_le_source_envelope
    {γ s : ℝ} (hγ : (1/300 : ℝ) ≤ γ) (hs : 0 ≤ s) :
    |D s| ≤ A0*s^2/4 * Real.exp (γ*s) := by
  have hA := xiShiftAbsoluteMass_pos 0
  have hγ0 : 0 ≤ γ := le_trans (by norm_num : (0:ℝ) ≤ 1/300) hγ
  calc
    |D s| = |∫ u in (0:ℝ)..s, Dens u| := rfl
    _ ≤ ∫ u in (0:ℝ)..s, |Dens u| := intervalIntegral.abs_integral_le_integral_abs hs
    _ ≤ ∫ u in (0:ℝ)..s, (A0/2 * Real.exp (γ*s))*u := by
      apply intervalIntegral.integral_mono_on hs
        (continuous_liEvenCrossActualClockLogHistoryDensity.abs.intervalIntegrable _ _)
        ((show Continuous (fun u : ℝ => (A0/2 * Real.exp (γ*s))*u) by fun_prop).intervalIntegrable _ _)
      intro u hu
      have hu0 : 0 ≤ u := hu.1
      have he : Real.exp (γ*u) ≤ Real.exp (γ*s) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hγ0)
      calc
        |Dens u| ≤ A0*u/2 * Real.exp (γ*u) := hgt_se_density_bound hγ hu.1
        _ ≤ A0*u/2 * Real.exp (γ*s) := mul_le_mul_of_nonneg_left he (by positivity)
        _ = (A0/2 * Real.exp (γ*s))*u := by ring
    _ = A0*s^2/4 * Real.exp (γ*s) := by
      rw [intervalIntegral.integral_const_mul]
      have hi : (∫ u in (0:ℝ)..s, u) = s^2/2 := by
        norm_num
      rw [hi]
      ring

theorem liEvenCrossActualClockSourceTerminalEnvelope_bound
    {γ t : ℝ} (hγ : (1/300 : ℝ) ≤ γ)
    (hZ : liEvenCrossActualClockSourceFirstZeroGuard t) :
    ∀ s ∈ Icc 0 t, 0 ≤ D s ∧
      D s ≤ liEvenCrossActualClockSourceTerminalEnvelope A0 γ t s := by
  intro s hs
  refine ⟨hZ.2.2 s hs, ?_⟩
  have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuous_liEvenCrossActualClockLogHistoryDensity.intervalIntegrable 0 s)
    (continuous_liEvenCrossActualClockLogHistoryDensity.intervalIntegrable s t)
  change D s + (∫ u in s..t, Dens u) = D t at hadj
  rw [hZ.2.1] at hadj
  calc
    D s = -(∫ u in s..t, Dens u) := by linarith
    _ ≤ |∫ u in s..t, Dens u| := neg_le_abs _
    _ ≤ ∫ u in s..t, |Dens u| := intervalIntegral.abs_integral_le_integral_abs hs.2
    _ ≤ ∫ u in s..t, A0*u/2 * Real.exp (γ*u) := by
      apply intervalIntegral.integral_mono_on hs.2
        (continuous_liEvenCrossActualClockLogHistoryDensity.abs.intervalIntegrable _ _)
        ((show Continuous (fun u : ℝ => A0*u/2 * Real.exp (γ*u)) by fun_prop).intervalIntegrable _ _)
      intro u hu
      exact hgt_se_density_bound hγ (hs.1.trans hu.1)
    _ = A0/2 * ∫ u in s..t, u * Real.exp (γ*u) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      ring
    _ = liEvenCrossActualClockSourceTerminalEnvelope A0 γ t s := rfl

theorem liEvenCrossActualClockSourceEnvelope_budget_bound
    {γ t : ℝ} (hγ : (1/300 : ℝ) ≤ γ)
    (hZ : liEvenCrossActualClockSourceFirstZeroGuard t) :
    Cout t ≤ liEvenCrossActualClockSourceNormMajorant A0 γ t ∧
    0 < t*K t ∧
    t*K t ≤ liEvenCrossActualClockSourceCorrelationBudget t ∧
    liEvenCrossActualClockSourceCorrelationBudget t ≤
      liEvenCrossActualClockSourceEnvelopeBudget A0 γ t := by
  have ht : 0 < t := lt_trans (by norm_num : (0:ℝ) < 20) hZ.1
  have hK : 0 < K t := liEvenCrossActualClockBorel_deriv_pos ht
  have hgeo := (liEvenCrossActualClockHistory_geometry ht).2.2
  have he0 : 0 < e t := hgeo.1
  have het : e t ≤ t := by linarith [hgeo.2]
  have hD := contDiff_liEvenCrossActualClockLogHistory.continuous
  have hterm := liEvenCrossActualClockSourceTerminalEnvelope_bound hγ hZ
  have hcost : Cout t ≤ liEvenCrossActualClockSourceNormMajorant A0 γ t := by
    apply intervalIntegral.integral_mono_on het
      ((hD.mul (hgt_se_outer_coefficient_cont t)).intervalIntegrable _ _)
      (liEvenCrossActualClockSourceEnvelope_compact_admission A0 γ t).2.2.2
    intro s hs
    have hsd := hterm s ⟨he0.le.trans hs.1, hs.2⟩
    calc
      D s * (s*K1 (t-s)-K (t-s)) ≤ D s * max (s*K1 (t-s)-K (t-s)) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hsd.1
      _ ≤ liEvenCrossActualClockSourceTerminalEnvelope A0 γ t s *
          max (s*K1 (t-s)-K (t-s)) 0 :=
        mul_le_mul_of_nonneg_right hsd.2 (le_max_right _ _)
  have hnear0 : 0 ≤ ∫ s in (0:ℝ)..e t, D s := by
    apply intervalIntegral.integral_nonneg he0.le
    intro s hs
    exact hZ.2.2 s ⟨hs.1, hs.2.trans het⟩
  have hA := xiShiftAbsoluteMass_pos 0
  have hγ0 : 0 ≤ γ := le_trans (by norm_num : (0:ℝ) ≤ 1/300) hγ
  have hnear : (∫ s in (0:ℝ)..e t, D s) ≤
      A0*(e t)^3/12 * Real.exp (γ*(e t)) := by
    calc
      _ ≤ ∫ s in (0:ℝ)..e t, (A0/4 * Real.exp (γ*(e t)))*s^2 := by
        apply intervalIntegral.integral_mono_on he0.le (hD.intervalIntegrable _ _)
          ((show Continuous (fun s : ℝ => (A0/4 * Real.exp (γ*(e t)))*s^2) by fun_prop).intervalIntegrable _ _)
        intro s hs
        have he : Real.exp (γ*s) ≤ Real.exp (γ*(e t)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hγ0)
        calc
          D s ≤ |D s| := le_abs_self _
          _ ≤ A0*s^2/4 * Real.exp (γ*s) :=
            abs_liEvenCrossActualClockLogHistory_le_source_envelope hγ hs.1
          _ ≤ A0*s^2/4 * Real.exp (γ*(e t)) :=
            mul_le_mul_of_nonneg_left he (by positivity)
          _ = (A0/4 * Real.exp (γ*(e t)))*s^2 := by ring
      _ = A0*(e t)^3/12 * Real.exp (γ*(e t)) := by
        rw [intervalIntegral.integral_const_mul]
        have hi : (∫ s in (0:ℝ)..e t, s^2) = (e t)^3/3 := by
          rw [integral_pow]
          norm_num
        rw [hi]
        ring
  refine ⟨hcost, mul_pos ht hK, ?_, ?_⟩
  · change t*K t ≤ t*K t + K t/2 * (∫ s in (0:ℝ)..e t, D s)
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hnear0)
  · change t*K t + K t/2 * (∫ s in (0:ℝ)..e t, D s) ≤
      K t * (t + A0/24 * (e t)^3 * Real.exp (γ*(e t)))
    calc
      _ ≤ t*K t + K t/2 * (A0*(e t)^3/12 * Real.exp (γ*(e t))) :=
        by
          have hm := mul_le_mul_of_nonneg_left hnear (show (0:ℝ) ≤ K t/2 by positivity)
          linarith
      _ = _ := by ring

section EnvelopeEstimates
local notation "b" => liEvenCrossActualClockHistoryOriginSlope

private theorem eeMajorant_continuous (M γ t : ℝ) :
    Continuous (fun s : ℝ => liEvenCrossActualClockSourceTerminalEnvelope M γ t s *
      max (s*K1 (t-s)-K (t-s)) 0) :=
  (hgt_se_terminal_cont M γ t).mul ((hgt_se_outer_coefficient_cont t).max continuous_const)

private theorem eeTerminal_nonneg {M γ t s : ℝ} (hM : 0 ≤ M)
    (hs : 0 ≤ s) (hst : s ≤ t) : 0 ≤ liEvenCrossActualClockSourceTerminalEnvelope M γ t s := by
  unfold liEvenCrossActualClockSourceTerminalEnvelope
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg hst (fun u hu =>
    mul_nonneg (hs.trans hu.1) (Real.exp_pos _).le)

private theorem eeTerminal_floor {M γ t s a : ℝ} (hM : 0 ≤ M)
    (hγ : 0 ≤ γ) (hs : 0 ≤ s) (hsa : s ≤ a) (hat : a ≤ t) :
    M/2*(t-a)*a*Real.exp (γ*a) ≤ liEvenCrossActualClockSourceTerminalEnvelope M γ t s := by
  have ha : 0 ≤ a := hs.trans hsa
  have hf : Continuous (fun u : ℝ => u * Real.exp (γ*u)) := by fun_prop
  have hlow : (t-a)*(a*Real.exp (γ*a)) ≤
      ∫ u in a..t, u * Real.exp (γ*u) := by
    calc
      (t-a)*(a*Real.exp (γ*a)) = ∫ _u in a..t, a*Real.exp (γ*a) := by simp; ring
      _ ≤ ∫ u in a..t, u * Real.exp (γ*u) :=
        intervalIntegral.integral_mono_on hat intervalIntegrable_const
          (hf.intervalIntegrable a t) (fun u hu =>
            mul_le_mul hu.1 (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.1 hγ))
              (Real.exp_pos _).le (ha.trans hu.1))
  have henlarge : (∫ u in a..t, u * Real.exp (γ*u)) ≤
      ∫ u in s..t, u * Real.exp (γ*u) := by
    apply intervalIntegral.integral_mono_interval hsa hat le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact mul_nonneg (hs.trans hu.1.le) (Real.exp_pos _).le
    · exact hf.intervalIntegrable s t
  unfold liEvenCrossActualClockSourceTerminalEnvelope
  nlinarith [mul_le_mul_of_nonneg_left (hlow.trans henlarge) (show 0 ≤ M/2 by positivity)]

private theorem eeSkew_primitive (t s : ℝ) :
    HasDerivAt (fun u : ℝ => -(u*K (t-u))) (s*K1 (t-s)-K (t-s)) s := by
  have h := ((hasDerivAt_id s).mul
    ((hgt_ek_slope_deriv (t-s)).comp s ((hasDerivAt_const s t).sub (hasDerivAt_id s)))).neg
  simp only [Function.comp_apply, id_eq] at h
  have hd : -(1*K (t-s) + s*(K1 (t-s)*(0-1))) =
      s*K1 (t-s)-K (t-s) := by ring
  rw [hd] at h
  exact h

private theorem eeSkew_integral (t a z : ℝ) :
    (∫ s in a..z, s*K1 (t-s)-K (t-s)) = a*K (t-a)-z*K (t-z) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => eeSkew_primitive t s) ((hgt_se_outer_coefficient_cont t).intervalIntegrable a z)
  change (∫ s in a..z, s*K1 (t-s)-K (t-s)) =
    -(z*K (t-z))-(-(a*K (t-a))) at h
  linarith

private theorem eeSlope_tangent {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    K t - K (t-s) ≤ K1 t * s := by
  have h := (convex_Icc (t-s) t).image_sub_le_mul_sub_of_deriv_le
    (hgt_ek_slope_smooth.continuous.continuousOn)
    (hgt_ek_slope_smooth.differentiable (by norm_num)).differentiableOn
    (fun u hu => by
      have hi : u ∈ Icc (t-s) t := interior_subset hu
      exact hgt_ek_source_basics.2.2.2.1
        (show 0 ≤ u by linarith [hi.1]) (show 0 ≤ t by linarith) hi.2)
    (t-s) (show t-s ∈ Icc (t-s) t by constructor <;> linarith)
    t (show t ∈ Icc (t-s) t by constructor <;> linarith)
    (show t-s ≤ t by linarith)
  nlinarith [h]

private theorem eeScale_quarter {t : ℝ} (ht : 0 < t) :
    3*K t/4 ≤ K (t-ell t) := by
  have hgeom := liEvenCrossActualClockHistory_geometry ht
  have heq : K1 t * ell t = K t/4 := by
    unfold liEvenCrossActualClockHistoryScale
    field_simp [hgeom.2.1.ne']
  have h := eeSlope_tangent (t := t) (s := ell t)
    hgeom.2.2.1.le (by linarith [hgeom.2.2.2])
  rw [heq] at h
  linarith

private theorem eePositiveSkew_mass {t : ℝ} (ht : 2 ≤ t)
    (he : max 1 (4*(K 1)/b) ≤ ell t) :
    ell t*K t/2 ≤ ∫ s in ell t..(t-1), max (s*K1 (t-s)-K (t-s)) 0 := by
  have htpos : 0 < t := by linarith
  have hKt := liEvenCrossActualClockBorel_deriv_pos htpos
  have hb := hgt_ek_source_basics.1
  have hKu := liEvenCrossActualClockBorel_deriv_pos (by norm_num : (0 : ℝ) < 1)
  have hel := (liEvenCrossActualClockHistory_geometry htpos).2.2
  have hscale : 4*K 1 ≤ b*ell t := by
    have h := (le_max_right (1 : ℝ) (4*K 1/b)).trans he
    simpa only [mul_comm] using (div_le_iff₀ hb).mp h
  have hsource := hgt_ek_slope_lower (show 0 ≤ t by linarith)
  have hcost : (t-1)*K 1 ≤ ell t*K t/4 := by
    have h1 := mul_le_mul_of_nonneg_right hsource hKu.le
    have h2 := mul_le_mul_of_nonneg_right hscale hKt.le
    have h3 : 0 ≤ b*K 1 := mul_nonneg hb.le hKu.le
    have h4 : b*((t-1)*K 1) ≤ b*(ell t*K t/4) := by nlinarith
    nlinarith
  have hmain := eeScale_quarter htpos
  have hmass : ell t*K t/2 ≤ ∫ s in ell t..(t-1), s*K1 (t-s)-K (t-s) := by
    rw [eeSkew_integral]
    have heq : t-(t-1) = (1 : ℝ) := by ring
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hmain hel.1.le]
  apply hmass.trans
  apply intervalIntegral.integral_mono_on (show ell t ≤ t-1 by linarith [hel.2])
    ((hgt_se_outer_coefficient_cont t).intervalIntegrable _ _)
    (((hgt_se_outer_coefficient_cont t).max continuous_const).intervalIntegrable _ _)
  intro s _
  exact le_max_left _ _

private theorem eeNormMajorant_submass {M γ t a z C : ℝ}
    (hM : 0 ≤ M) (ht : 0 < t) (hea : ell t ≤ a) (haz : a ≤ z) (hzt : z ≤ t)
    (hfloor : ∀ s ∈ Icc a z, C ≤ liEvenCrossActualClockSourceTerminalEnvelope M γ t s) :
    C * (∫ s in a..z, max (s*K1 (t-s)-K (t-s)) 0) ≤ liEvenCrossActualClockSourceNormMajorant M γ t := by
  have hel := (liEvenCrossActualClockHistory_geometry ht).2.2
  calc
    C * (∫ s in a..z, max (s*K1 (t-s)-K (t-s)) 0) =
      ∫ s in a..z, C*max (s*K1 (t-s)-K (t-s)) 0 :=
        (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ ∫ s in a..z, liEvenCrossActualClockSourceTerminalEnvelope M γ t s * max (s*K1 (t-s)-K (t-s)) 0 := by
      apply intervalIntegral.integral_mono_on haz
        ((continuous_const.mul ((hgt_se_outer_coefficient_cont t).max continuous_const)).intervalIntegrable _ _)
        ((eeMajorant_continuous M γ t).intervalIntegrable _ _)
      intro s hs
      exact mul_le_mul_of_nonneg_right (hfloor s hs) (le_max_right _ _)
    _ ≤ liEvenCrossActualClockSourceNormMajorant M γ t := by
      unfold liEvenCrossActualClockSourceNormMajorant
      apply intervalIntegral.integral_mono_interval hea haz hzt
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact mul_nonneg (eeTerminal_nonneg hM (by linarith [hs.1]) hs.2)
          (le_max_right _ _)
      · exact (eeMajorant_continuous M γ t).intervalIntegrable _ _

private theorem eeNormMajorant_subconstant {M γ t a z C : ℝ}
    (hM : 0 ≤ M) (ht : 0 < t) (hea : ell t ≤ a) (haz : a ≤ z) (hzt : z ≤ t)
    (hfloor : ∀ s ∈ Icc a z,
      C ≤ liEvenCrossActualClockSourceTerminalEnvelope M γ t s * max (s*K1 (t-s)-K (t-s)) 0) :
    (z-a)*C ≤ liEvenCrossActualClockSourceNormMajorant M γ t := by
  have hel := (liEvenCrossActualClockHistory_geometry ht).2.2
  calc
    (z-a)*C = ∫ _s in a..z, C := by simp
    _ ≤ ∫ s in a..z, liEvenCrossActualClockSourceTerminalEnvelope M γ t s * max (s*K1 (t-s)-K (t-s)) 0 :=
      intervalIntegral.integral_mono_on haz intervalIntegrable_const
        ((eeMajorant_continuous M γ t).intervalIntegrable _ _) hfloor
    _ ≤ liEvenCrossActualClockSourceNormMajorant M γ t := by
      unfold liEvenCrossActualClockSourceNormMajorant
      apply intervalIntegral.integral_mono_interval hea haz hzt
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact mul_nonneg (eeTerminal_nonneg hM (by linarith [hs.1]) hs.2)
          (le_max_right _ _)
      · exact (eeMajorant_continuous M γ t).intervalIntegrable _ _

private theorem eeTerminal_unit_floor {M γ t s : ℝ} (hM : 0 < M)
    (hγ : 0 < γ) (ht : 2 ≤ t) (hs : 0 ≤ s) (hst : s ≤ t-1) :
    M*t*Real.exp (γ*(t-1))/4 ≤ liEvenCrossActualClockSourceTerminalEnvelope M γ t s := by
  have h := eeTerminal_floor hM.le hγ.le hs hst (show t-1 ≤ t by linarith)
  have he := Real.exp_pos (γ*(t-1))
  have hm : 0 ≤ M*Real.exp (γ*(t-1)) := mul_nonneg hM.le he.le
  nlinarith

theorem liEvenCrossActualClockSourceNormMajorant_lower {M γ t : ℝ}
    (hM : 0 < M) (hγ : 0 < γ) (ht : 2 ≤ t)
    (he : max 1 (4*(K 1)/b) ≤ ell t) :
    M*t*(ell t)*K t*Real.exp (γ*(t-1))/8 ≤ liEvenCrossActualClockSourceNormMajorant M γ t := by
  have htpos : 0 < t := by linarith
  have hel := (liEvenCrossActualClockHistory_geometry htpos).2.2
  have hmass := eePositiveSkew_mass ht he
  have hsub := eeNormMajorant_submass hM.le htpos le_rfl
    (show ell t ≤ t-1 by linarith [hel.2]) (show t-1 ≤ t by linarith)
    (fun s hs => eeTerminal_unit_floor hM hγ ht (by linarith [hs.1]) hs.2)
  have hC : 0 ≤ M*t*Real.exp (γ*(t-1))/4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmass hC
  calc
    M*t*(ell t)*K t*Real.exp (γ*(t-1))/8 =
      (M*t*Real.exp (γ*(t-1))/4)*(ell t*K t/2) := by ring
    _ ≤ _ := hmul
    _ ≤ liEvenCrossActualClockSourceNormMajorant M γ t := hsub

private theorem eeEnvelopeBudget_upper {M γ t : ℝ} (hM : 0 < M)
    (hγ : 0 < γ) (ht : 2 ≤ t) :
    0 < liEvenCrossActualClockSourceEnvelopeBudget M γ t ∧
    liEvenCrossActualClockSourceEnvelopeBudget M γ t ≤
      K t*(1+M/1536)*t^3*Real.exp (γ*t/4) := by
  have htpos : 0 < t := by linarith
  have hK := liEvenCrossActualClockBorel_deriv_pos htpos
  have hel := (liEvenCrossActualClockHistory_geometry htpos).2.2
  have hexp : Real.exp (γ*ell t) ≤ Real.exp (γ*t/4) :=
    Real.exp_le_exp.mpr (by nlinarith [hel.2])
  have hcube : (ell t)^3 ≤ t^3/64 := by
    calc
      (ell t)^3 ≤ (t/4)^3 := by
        gcongr
        · exact hel.1.le
        · exact hel.2.le
      _ = t^3/64 := by ring
  have hterm : M/24*(ell t)^3*Real.exp (γ*ell t) ≤
      M/1536*t^3*Real.exp (γ*t/4) := by
    calc
      M/24*(ell t)^3*Real.exp (γ*ell t) ≤
        M/24*(t^3/64)*Real.exp (γ*t/4) := by gcongr
      _ = M/1536*t^3*Real.exp (γ*t/4) := by ring
  have heone : 1 ≤ Real.exp (γ*t/4) := Real.one_le_exp (by positivity)
  have ht3 : t ≤ t^3 := by nlinarith [sq_nonneg (t-1)]
  have htmain : t ≤ t^3*Real.exp (γ*t/4) :=
    ht3.trans (by nlinarith [mul_le_mul_of_nonneg_left heone (show 0 ≤ t^3 by positivity)])
  have heltpos : 0 < ell t := hel.1
  unfold liEvenCrossActualClockSourceEnvelopeBudget
  refine ⟨by positivity, ?_⟩
  have hsum : t+M/24*(ell t)^3*Real.exp (γ*ell t) ≤
      (1+M/1536)*t^3*Real.exp (γ*t/4) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsum hK.le]

theorem liEvenCrossActualClockSourceEnvelope_ratio_lower {M γ t : ℝ}
    (hM : 0 < M) (hγ : 0 < γ) (ht : 2 ≤ t)
    (he : max 1 (4*(K 1)/b) ≤ ell t) :
    0 < liEvenCrossActualClockSourceEnvelopeBudget M γ t ∧
    M*Real.exp (-γ)/(8*(1+M/1536))*Real.exp (3*γ*t/4)/t^2 ≤
      liEvenCrossActualClockSourceNormMajorant M γ t / liEvenCrossActualClockSourceEnvelopeBudget M γ t := by
  have hbudget := eeEnvelopeBudget_upper hM hγ ht
  have htpos : 0 < t := by linarith
  have hK := liEvenCrossActualClockBorel_deriv_pos htpos
  have hscale : 1 ≤ ell t := (le_max_left (1 : ℝ) (4*K 1/b)).trans he
  have hlower := liEvenCrossActualClockSourceNormMajorant_lower hM hγ ht he
  have hR : 0 ≤ M*Real.exp (-γ)/(8*(1+M/1536))*Real.exp (3*γ*t/4)/t^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbudget.2 hR
  have hexp : Real.exp (-γ)*Real.exp (3*γ*t/4)*Real.exp (γ*t/4) =
      Real.exp (γ*(t-1)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have halgebra :
      (M*Real.exp (-γ)/(8*(1+M/1536))*Real.exp (3*γ*t/4)/t^2)*
        (K t*(1+M/1536)*t^3*Real.exp (γ*t/4)) =
      M*t*K t*Real.exp (γ*(t-1))/8 := by
    calc
      _ = M*t*K t*(Real.exp (-γ)*Real.exp (3*γ*t/4)*Real.exp (γ*t/4))/8 := by
        field_simp [htpos.ne', show 1+M/1536 ≠ 0 by positivity]
      _ = _ := by rw [hexp]
  have hscale_mul : M*t*K t*Real.exp (γ*(t-1))/8 ≤
      M*t*(ell t)*K t*Real.exp (γ*(t-1))/8 := by
    nlinarith [mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ M*t*K t*Real.exp (γ*(t-1))/8 by positivity)]
  refine ⟨hbudget.1, (le_div_iff₀ hbudget.1).mpr ?_⟩
  exact hmul.trans (halgebra.le.trans (hscale_mul.trans hlower))

theorem tendsto_liEvenCrossActualClockSourceEnvelope_ratio_atTop {M γ : ℝ} (hM : 0 < M) (hγ : 0 < γ) :
    Tendsto (fun t : ℝ => liEvenCrossActualClockSourceNormMajorant M γ t / liEvenCrossActualClockSourceEnvelopeBudget M γ t) atTop atTop := by
  have hc : 0 < M*Real.exp (-γ)/(8*(1+M/1536)) := by positivity
  have hbase : Tendsto (fun t : ℝ => Real.exp ((3*γ/4)*t)/t^2) atTop atTop := by
    have h := tendsto_exp_mul_div_rpow_atTop (2 : ℝ) (3*γ/4) (by positivity)
    change Tendsto (fun t : ℝ => Real.exp ((3*γ/4)*t)/t^((2 : ℕ) : ℝ)) atTop atTop at h
    simpa only [Real.rpow_natCast] using h
  have hbound : Tendsto (fun t : ℝ =>
      M*Real.exp (-γ)/(8*(1+M/1536))*Real.exp (3*γ*t/4)/t^2) atTop atTop := by
    have hfun : (fun t : ℝ =>
        M*Real.exp (-γ)/(8*(1+M/1536))*Real.exp (3*γ*t/4)/t^2) =
        fun t : ℝ => M*Real.exp (-γ)/(8*(1+M/1536)) *
          (Real.exp ((3*γ/4)*t)/t^2) := by
      funext t
      rw [show 3*γ*t/4 = (3*γ/4)*t by ring]
      ring
    rw [hfun]
    exact hbase.const_mul_atTop hc
  apply tendsto_atTop_mono' _ ?_ hbound
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    hgt_ek_scale_atTop.eventually_ge_atTop (max 1 (4*K 1/b))] with t ht he
  exact (liEvenCrossActualClockSourceEnvelope_ratio_lower hM hγ ht he).2

private theorem eeSlope_mono {a z : ℝ} (ha : 0 ≤ a) (haz : a ≤ z) : K a ≤ K z := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hgt_ek_slope_deriv u) (hgt_ek_curvature_continuous.intervalIntegrable a z)
  have hn : 0 ≤ ∫ u in a..z, K1 u :=
    intervalIntegral.integral_nonneg haz (fun u hu =>
      hgt_ek_source_basics.1.le.trans
        (hgt_ek_source_basics.2.2.1 u (ha.trans hu.1)).2)
  linarith

theorem liEvenCrossActualClockSourceNormMajorant_terminal_lower {M γ t : ℝ}
    (hM : 0 < M) (hγ : 0 < γ) (ht : 2 ≤ t)
    (hb : 2*(1+(K 1)/b) ≤ t) :
    M*b*t^2*Real.exp (γ*(t-1))/32 ≤ liEvenCrossActualClockSourceNormMajorant M γ t := by
  have htpos : 0 < t := by linarith
  have hbp := hgt_ek_source_basics.1
  have hel := (liEvenCrossActualClockHistory_geometry htpos).2.2
  have hband := eeNormMajorant_subconstant (γ := γ)
    (C := M*b*t^2*Real.exp (γ*(t-1))/16)
    hM.le htpos (show ell t ≤ t-1 by linarith [hel.2])
    (show t-1 ≤ t-1/2 by linarith) (show t-1/2 ≤ t by linarith) ?_
  · nlinarith [hband]
  intro s hs
  have hr0 : 0 ≤ t-s := by linarith [hs.2]
  have hr1 : t-s ≤ 1 := by linarith [hs.1]
  have hspos : 0 ≤ s := by linarith [hs.1]
  have hcurv : b ≤ K1 (t-s) := (hgt_ek_source_basics.2.2.1 _ hr0).2
  have hK : K (t-s) ≤ K 1 := eeSlope_mono hr0 hr1
  have hthreshold : 2*K 1 ≤ b*(t-2) := by
    have hh : 2 + 2*(K 1/b) ≤ t := by linarith
    have hh' := mul_le_mul_of_nonneg_left hh hbp.le
    have hbn : b ≠ 0 := hbp.ne'
    field_simp [hbn] at hh'
    nlinarith
  have hJ : b*t/2 ≤ s*K1 (t-s)-K (t-s) := by
    have hm := mul_le_mul_of_nonneg_left hcurv hspos
    nlinarith [mul_le_mul_of_nonneg_left hs.1 hbp.le]
  have hE : M*t*Real.exp (γ*(t-1))/8 ≤ liEvenCrossActualClockSourceTerminalEnvelope M γ t s := by
    have hf := eeTerminal_floor hM.le hγ.le hspos hs.2
      (show t-1/2 ≤ t by linarith)
    have he : Real.exp (γ*(t-1)) ≤ Real.exp (γ*(t-1/2)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hpos : 0 ≤ M*t/8 := by positivity
    have hm := mul_le_mul_of_nonneg_left he hpos
    have hm' : M*t*Real.exp (γ*(t-1/2))/8 ≤
        M/2*(t-(t-1/2))*(t-1/2)*Real.exp (γ*(t-1/2)) := by
      nlinarith [mul_nonneg hM.le (Real.exp_pos (γ*(t-1/2))).le]
    have hsmall : M*t*Real.exp (γ*(t-1))/8 ≤
        M*t*Real.exp (γ*(t-1/2))/8 := by nlinarith [hm]
    exact hsmall.trans (hm'.trans hf)
  have hJmax : b*t/2 ≤ max (s*K1 (t-s)-K (t-s)) 0 := hJ.trans (le_max_left _ _)
  have hh := mul_le_mul hE hJmax (show 0 ≤ b*t/2 by positivity)
    (eeTerminal_nonneg hM.le hspos (by linarith [hs.2]))
  nlinarith [hh]

end EnvelopeEstimates

theorem liEvenCrossActualClockSourceEnvelope_eventual_budget_obstruction
    {γ : ℝ} (hγ : (1/300 : ℝ) ≤ γ) :
    ∀ᶠ t : ℝ in atTop, liEvenCrossActualClockSourceFirstZeroGuard t →
      liEvenCrossActualClockSourceCorrelationBudget t <
        liEvenCrossActualClockSourceNormMajorant A0 γ t := by
  have hγ0 : 0 < γ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/300) hγ
  have hratio := tendsto_liEvenCrossActualClockSourceEnvelope_ratio_atTop
    (xiShiftAbsoluteMass_pos 0) hγ0
  filter_upwards [hratio.eventually_gt_atTop (1 : ℝ)] with t ht
  intro hZ
  have hb := liEvenCrossActualClockSourceEnvelope_budget_bound hγ hZ
  have hv : 0 < liEvenCrossActualClockSourceEnvelopeBudget A0 γ t :=
    lt_of_lt_of_le hb.2.1 (hb.2.2.1.trans hb.2.2.2)
  exact lt_of_le_of_lt hb.2.2.2 ((one_lt_div hv).mp ht)

private theorem hgt_se_signed_test {p t : ℝ} (hp : 1 < p) (ht : 0 < t)
    (h : ℝ → ℝ) (hh : Measurable h)
    (hC : ∃ C : ℝ, ∀ u ∈ Ioc 0 t, |h u| ≤ C) :
    Integrable h (liClockThetaCompactMarkedGammaMeasure p true t) ∧
    Integrable h (liClockThetaCompactMarkedGammaMeasure p false t) ∧
    (∫ u, h u ∂liClockThetaCompactMarkedGammaMeasure p true t) -
      (∫ u, h u ∂liClockThetaCompactMarkedGammaMeasure p false t) =
        ∫ u in (0:ℝ)..t, h u * Dens u := by
  have hpos := liClockThetaCompactMarkedGammaMeasure_test hp ht true h hh hC
  have hneg := liClockThetaCompactMarkedGammaMeasure_test hp ht false h hh hC
  refine ⟨hpos.1, hneg.1, ?_⟩
  rw [hpos.2.2, hneg.2.2, ← MeasureTheory.integral_sub hpos.2.1 hneg.2.1,
    intervalIntegral.integral_of_le ht.le]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  change h u * liClockThetaMarkedJumpDensity true u - h u * liClockThetaMarkedJumpDensity false u = h u * Dens u
  rw [← mul_sub, liClockThetaMarkedJumpDensity_sub,
    indicator_of_mem (show u ∈ Ioi (0:ℝ) from hu.1)]
  rfl

theorem liClockThetaCompactMarkedGammaMeasure_signed_prefix
    {p T x : ℝ} (hp : 1 < p) (hT : 0 < T) (hx : 0 ≤ x) (hxT : x ≤ T) :
    (liClockThetaCompactMarkedGammaMeasure p true T).real (Ioc 0 x) -
      (liClockThetaCompactMarkedGammaMeasure p false T).real (Ioc 0 x) = D x := by
  let h : ℝ → ℝ := (Ioc 0 x).indicator 1
  have hh : Measurable h := measurable_const.indicator measurableSet_Ioc
  have hC : ∃ C : ℝ, ∀ u ∈ Ioc 0 T, |h u| ≤ C := by
    refine ⟨1, ?_⟩
    intro u _
    by_cases hu : u ∈ Ioc (0:ℝ) x <;> simp [h, hu]
  have htest := (hgt_se_signed_test hp hT h hh hC).2.2
  have heq : (fun u => h u * Dens u) = (Ioc 0 x).indicator Dens := by
    funext u
    by_cases hu : u ∈ Ioc (0:ℝ) x <;> simp [h, hu]
  calc
    _ = ∫ u in (0:ℝ)..T, h u * Dens u := by
      simpa only [h, MeasureTheory.integral_indicator_one measurableSet_Ioc] using htest
    _ = D x := by
      rw [intervalIntegral.integral_of_le hT.le, heq,
        MeasureTheory.setIntegral_indicator measurableSet_Ioc,
        inter_eq_right.mpr (Ioc_subset_Ioc le_rfl hxT)]
      exact (intervalIntegral.integral_of_le hx).symm

private theorem hgt_se_marked_cost_cont (t : ℝ) :
    Continuous (liEvenCrossActualClockHistoryMarkedCost t) := by
  change Continuous (fun u : ℝ => if u ≤ e t then e t*K (t-e t) else u*K (t-u))
  apply Continuous.if ?_ continuous_const
    (continuous_id.mul (hgt_ek_slope_smooth.continuous.comp (continuous_const.sub continuous_id)))
  intro u hu
  change u ∈ frontier (Iic (e t)) at hu
  have heq : u = e t := by simpa only [frontier_Iic, mem_singleton_iff] using hu
  subst u
  rfl

private theorem hgt_se_weight_deriv (t s : ℝ) :
    HasDerivAt (fun s : ℝ => s*K (t-s)) (K (t-s)-s*K1 (t-s)) s := by
  have hk : HasDerivAt (fun s : ℝ => K (t-s)) (-K1 (t-s)) s := by
    simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using
      (hgt_ek_slope_deriv (t-s)).comp s ((hasDerivAt_id s).const_sub t)
  convert (hasDerivAt_id s).mul hk using 1 <;>
    first | rfl | (dsimp only [id_eq]; ring)

private theorem hgt_se_marked_cost_density {t : ℝ} (ht : 0 < t) :
    Cout t = ∫ u in (0:ℝ)..t, liEvenCrossActualClockHistoryMarkedCost t u * Dens u := by
  have he0 := (liEvenCrossActualClockHistory_geometry ht).2.2.1
  have het : e t ≤ t := by linarith [(liEvenCrossActualClockHistory_geometry ht).2.2.2]
  have hcost := (hgt_se_marked_cost_cont t).mul continuous_liEvenCrossActualClockLogHistoryDensity
  have hw : Continuous (fun u : ℝ => u*K (t-u)) :=
    continuous_id.mul (hgt_ek_slope_smooth.continuous.comp (continuous_const.sub continuous_id))
  have hh : Continuous (fun u : ℝ => K (t-u)-u*K1 (t-u)) :=
    (hgt_ek_slope_smooth.continuous.comp (continuous_const.sub continuous_id)).sub
      (continuous_id.mul (hgt_ek_curvature_continuous.comp (continuous_const.sub continuous_id)))
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    contDiff_liEvenCrossActualClockLogHistory.continuous.continuousOn hw.continuousOn
    (fun u _ => hasDerivAt_liEvenCrossActualClockLogHistory u)
    (fun u _ => hgt_se_weight_deriv t u)
    (continuous_liEvenCrossActualClockLogHistoryDensity.intervalIntegrable (e t) t)
    (hh.intervalIntegrable (e t) t)
  rw [sub_self, liEvenCrossActualClockHistory_origin.1] at hip
  simp only [mul_zero, zero_sub] at hip
  have hcout : Cout t = -(∫ u in e t..t, D u * (K (t-u)-u*K1 (t-u))) := by
    rw [liEvenCrossActualClockHistoryOutsideCorrelation, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  have hprefix : (∫ u in (0:ℝ)..e t, liEvenCrossActualClockHistoryMarkedCost t u * Dens u) =
      (e t*K (t-e t))*D (e t) := by
    calc
      _ = ∫ u in (0:ℝ)..e t, (e t*K (t-e t))*Dens u := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : u ∈ Icc (0:ℝ) (e t) := by simpa only [uIcc_of_le he0.le] using hu
        change liEvenCrossActualClockHistoryMarkedCost t u * Dens u = (e t*K (t-e t))*Dens u
        rw [liEvenCrossActualClockHistoryMarkedCost, if_pos hu'.2]
      _ = _ := intervalIntegral.integral_const_mul _ _
  have houter : (∫ u in e t..t, liEvenCrossActualClockHistoryMarkedCost t u * Dens u) =
      ∫ u in e t..t, Dens u * (u*K (t-u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (e t) t := by simpa only [uIcc_of_le het] using hu
    have hpoint : liEvenCrossActualClockHistoryMarkedCost t u = u*K (t-u) := by
      by_cases hue : u ≤ e t
      · have heq : u = e t := le_antisymm hue hu'.1
        subst u
        simp [liEvenCrossActualClockHistoryMarkedCost]
      · simp [liEvenCrossActualClockHistoryMarkedCost, hue]
    change liEvenCrossActualClockHistoryMarkedCost t u * Dens u = Dens u * (u*K (t-u))
    rw [hpoint, mul_comm]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcost.intervalIntegrable (μ := volume) 0 (e t)) (hcost.intervalIntegrable (e t) t)
  simp only [Pi.mul_apply] at hsplit
  rw [hprefix, houter] at hsplit
  calc
    Cout t = (e t*K (t-e t))*D (e t) +
        ∫ u in e t..t, Dens u*(u*K (t-u)) := by
      rw [hcout]
      nlinarith [hip]
    _ = ∫ u in (0:ℝ)..t, liEvenCrossActualClockHistoryMarkedCost t u * Dens u := hsplit

theorem liEvenCrossActualClockHistoryOutsideCorrelation_eq_marked_cost
    {p t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    Integrable (liEvenCrossActualClockHistoryMarkedCost t)
      (liClockThetaCompactMarkedGammaMeasure p true t) ∧
    Integrable (liEvenCrossActualClockHistoryMarkedCost t)
      (liClockThetaCompactMarkedGammaMeasure p false t) ∧
    Cout t = (∫ u, liEvenCrossActualClockHistoryMarkedCost t u
        ∂liClockThetaCompactMarkedGammaMeasure p true t) -
      (∫ u, liEvenCrossActualClockHistoryMarkedCost t u
        ∂liClockThetaCompactMarkedGammaMeasure p false t) := by
  have hc := hgt_se_marked_cost_cont t
  have hcompact : IsCompact (Icc (0:ℝ) t) := isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hc.continuousOn
  have hb : ∃ C : ℝ, ∀ u ∈ Ioc 0 t, |liEvenCrossActualClockHistoryMarkedCost t u| ≤ C := by
    refine ⟨C, ?_⟩
    intro u hu
    simpa only [Real.norm_eq_abs] using hC u ⟨hu.1.le, hu.2⟩
  have htest := hgt_se_signed_test hp ht _ hc.measurable hb
  exact ⟨htest.1, htest.2.1, (hgt_se_marked_cost_density ht).trans htest.2.2.symm⟩

end
end RHTower
