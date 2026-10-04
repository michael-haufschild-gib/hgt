import GaloisForLFunctions.RHTower.ThetaFinitePairSturmCrossing
import GaloisForLFunctions.RHTower.ThetaTailPositiveBalancePrimitive

/-! The actual matched transport packet has a vanishing source-weighted tail.
The existing diagonal comparison controls the complete finite-pair balance;
no new integrability or asymptotic-expansion premise is needed. -/

noncomputable section
open Set Filter Topology
namespace RHTower.ThetaFiniteTransport

local notation "k" => thetaCuspFullSource
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "H" => thetaTailFirstMomentKernel
local notation "J" => H 0 0
local notation "s" => ThetaSturmCrossing.secant

theorem actualSource_hasDerivAt (t : ℝ) : HasDerivAt k (-p t*k t) t := by
  have he : deriv k t=-p t*k t := by
    have hl : iteratedDeriv 1 thetaCuspLogSource t=deriv k t/k t := by
      simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource t).deriv
    dsimp only [thetaCuspLogDecaySlope]
    rw [hl]
    field_simp [(thetaCuspFullSource_pos_all t).ne']
  rw [← he]
  exact thetaCuspSchwartzReal.hasDerivAt t

private theorem center_pos : 0 < J := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
  exact ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0

private theorem shifted_slope_antitone {x : ℝ} (hx : 0 < x) :
    AntitoneOn (fun t => p (t+x)/p t) (Ioi 0) := by
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt (fun u => p (u+x)/p u)
      ((c (t+x)*p t-p (t+x)*c t)/(p t)^2) t := by
    convert! ((hasDerivAt_thetaCuspLogDecaySlope (t+x)).comp t
      ((hasDerivAt_id t).add_const x)).div (hasDerivAt_thetaCuspLogDecaySlope t)
      (ThetaSturmCrossing.slope_pos ht).ne' using 1
    simp only [Function.comp_apply,id_eq]
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
  · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (by simpa only [interior_Ioi,mem_Ioi] using ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ioi,mem_Ioi] using ht
    rw [(hd t ht0).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have h := (div_le_div_iff₀ (ThetaSturmCrossing.slope_pos (add_pos ht0 hx))
      (ThetaSturmCrossing.slope_pos ht0)).mp
      (ThetaSturmCrossing.curvature_slope_anti ht0 (add_pos ht0 hx) (by linarith))
    nlinarith only [h]

private def slopeBound (x : ℝ) : ℝ := p (1+x)/(x*p 1)

private theorem slopeBound_pos {x : ℝ} (hx : 0 < x) : 0 < slopeBound x :=
  div_pos (ThetaSturmCrossing.slope_pos (by linarith))
    (mul_pos hx (ThetaSturmCrossing.slope_pos (by norm_num)))

private theorem secant_le_slope {x t : ℝ} (hx : 0 < x) (ht : 1 ≤ t) :
    s x t ≤ slopeBound x*p t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have h := shifted_slope_antitone hx (show (1:ℝ) ∈ Ioi 0 by norm_num) ht0 ht
  have hp := ThetaSturmCrossing.slope_pos ht0
  calc
    s x t ≤ p (t+x)/x :=
      div_le_div_of_nonneg_right (sub_le_self _ hp.le) hx.le
    _ = ((p (t+x)/p t)*p t)/x := by field_simp [hp.ne']
    _ ≤ ((p (1+x)/p 1)*p t)/x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h hp.le) hx.le
    _ = slopeBound x*p t := by unfold slopeBound; ring

private theorem balance_le_diagonal (x t : ℝ) : prefixBalance x t ≤ H 0 x*H t t := by
  rw [prefixBalance_eq_tail]
  exact sub_le_self _ (mul_nonneg center_pos.le (thetaTailFirstMomentKernel_nonneg _ _))

private theorem slope_diagonal_le {t : ℝ} (ht : 0 < t) : p t*H t t ≤ t*k t^2 := by
  have h := ThetaTailTwoPoint.diagonal_tail_lt_source_square ht
  rw [← ThetaTailTwoPoint.kernel_diag_eq_cut] at h
  have h' : p t*H t t/t < k t^2 := by
    simpa only [div_mul_eq_mul_div] using h
  have hh := (div_lt_iff₀ ht).mp h'
  nlinarith only [hh]

private theorem weightedSource_limit : Tendsto (fun t : ℝ => t*k t^2) atTop (𝓝 0) := by
  let f := SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t) thetaCuspSchwartzReal
  have hf (t : ℝ) : f t=t*k t := by
    have hg : (fun t : ℝ => t).HasTemperateGrowth := by fun_prop
    simp only [f,SchwartzMap.smulLeftCLM_apply_apply hg,smul_eq_mul,thetaCuspSchwartzReal_apply]
  have h1 : Tendsto (fun t : ℝ => t*k t) atTop (𝓝 0) := by
    exact (f.tendsto_cocompact.mono_left atTop_le_cocompact).congr' (Eventually.of_forall hf)
  have h0 : Tendsto k atTop (𝓝 0) := thetaCuspSchwartzReal.tendsto_cocompact.mono_left atTop_le_cocompact
  convert! h1.mul h0 using 1
  · funext t; ring
  · simp only [mul_zero]

/-- The complete secant-weighted balance vanishes at infinity. -/
theorem secant_prefixBalance_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t => s x t*prefixBalance x t) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_
    (show Tendsto (fun t => (slopeBound x*H 0 x)*(t*k t^2)) atTop (𝓝 0) by
      simpa only [mul_zero] using weightedSource_limit.const_mul (slopeBound x*H 0 x))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    exact mul_nonneg ((thetaCuspLogCurvature_pos t).trans (ThetaSturmCrossing.secant_gt_curvature hx ht0.le)).le
      (prefixBalance_pos hx ht0).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    calc
      s x t*prefixBalance x t ≤ (slopeBound x*p t)*prefixBalance x t :=
        mul_le_mul_of_nonneg_right (secant_le_slope hx ht) (prefixBalance_pos hx ht0).le
      _ ≤ (slopeBound x*p t)*(H 0 x*H t t) :=
        mul_le_mul_of_nonneg_left (balance_le_diagonal x t)
          (mul_pos (slopeBound_pos hx) (ThetaSturmCrossing.slope_pos ht0)).le
      _ = (slopeBound x*H 0 x)*(p t*H t t) := by ring
      _ ≤ (slopeBound x*H 0 x)*(t*k t^2) :=
        mul_le_mul_of_nonneg_left (slope_diagonal_le ht0)
          (mul_nonneg (slopeBound_pos hx).le (thetaTailFirstMomentKernel_nonneg _ _))

def matchedPacket (x t : ℝ) : ℝ := normalizedPacket x t+s x t*transportPrimitive x t
def weightedPacket (x t : ℝ) : ℝ := k t*k (t+x)*matchedPacket x t

theorem weightedPacket_eq {x : ℝ} (hx : 0 < x) (t : ℝ) :
    weightedPacket x t=(k t*k (t+x)-H 0 x/J*k t^2)/x+
      s x t*prefixBalance x t/(x*J) := by
  unfold weightedPacket matchedPacket normalizedPacket transportPrimitive
  rw [add_comm x t]
  field_simp [hx.ne',center_pos.ne',(thetaCuspFullSource_pos_all t).ne',
    (thetaCuspFullSource_pos_all (t+x)).ne']

/-- The actual source-weighted matched packet has zero endpoint value at infinity. -/
theorem weightedPacket_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (weightedPacket x) atTop (𝓝 0) := by
  have h0 : Tendsto k atTop (𝓝 0) := thetaCuspSchwartzReal.tendsto_cocompact.mono_left atTop_le_cocompact
  have hx0 : Tendsto (fun t => k (t+x)) atTop (𝓝 0) := by
    convert! h0.comp (tendsto_atTop_add_const_left atTop x tendsto_id) using 1
    funext t
    change k (t+x)=k (x+t)
    rw [add_comm t x]
  have h := (((h0.mul hx0).sub ((h0.pow 2).const_mul (H 0 x/J))).div_const x).add
    ((secant_prefixBalance_limit hx).div_const (x*J))
  simp only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero,zero_div,add_zero] at h
  exact h.congr' (Eventually.of_forall fun t => (weightedPacket_eq hx t).symm)

end RHTower.ThetaFiniteTransport
