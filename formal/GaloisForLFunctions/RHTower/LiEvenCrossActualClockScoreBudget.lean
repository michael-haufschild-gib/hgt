import GaloisForLFunctions.RHTower.LiEvenCrossActualClockScoreCorrelation

/-!
# First-zero score budget and the normalized outer-history order

Write `H_t(s) = K(t-s) - sK'(t-s)`, `ℓ = K(t)/(4K'(t))`, the near reserve
`A_near(t) = ∫₀^ℓ D(s)(H_t(s) - K(t)/2) ds`, the outer correlation `C_out(t)`, and
`V(t) = tK(t) + (K(t)/2)∫₀^ℓ D`.

* For every `t > 0` the factor-one history law gives `P(t) = V + A_near - C_out` exactly.
* At a guarded zero (`t > 20`, `D(t) = 0`, `D ≥ 0` on `[0,t]`) the left slope gives `P(t) ≤ 0`,
  and the early clock gives `A_near ≥ ζ_t = q A₀ K(t) min(ℓ/2, 20)³/48 > 0`.  With the uniform
  score ceiling `θ`, `θ I_U - 303(I_K + V) = 303(A_near - P(t)) + (I_R - (1-θ)I_U) ≥ 303 ζ_t`.
* The weight `sD(s)U(t-s)/I_U` on `[ℓ, t]` is a probability `Π_t`.  With `a(r) = 303K'(r)/U(r)`,
  `ρ_t = ∫ a(t-s) dΠ_t` and `β_t = 303(I_K + V)/I_U` satisfy `0 < β_t < ρ_t ≤ θ` and
  `ρ_t - β_t = 303(A_near - P(t))/I_U`; the outside budget `C_out ≤ V` is exactly `ρ_t ≤ β_t`.
* Terminal mass: `ρ_t ≤ ε + (θ - ε)Π_t(t - s < R)` once `a ≤ ε` beyond `R`, and
  `c Π_t(t - s < R) ≤ ρ_t` for `c ≤ a` on `[0, R]`.  Along guarded zeros, `ρ → 0` iff every
  fixed terminal mass tends to `0`, and then `β → 0` and `ζ/I_U → 0`.
-/

open MeasureTheory Set Filter Topology
open scoped Interval ENNReal
namespace RHTower
noncomputable section
local notation "B" => liEvenCrossActualClockBorelKernel
local notation "K" => deriv liEvenCrossActualClockBorelKernel
local notation "K1" => deriv (deriv liEvenCrossActualClockBorelKernel)
local notation "P" => liEvenCrossActualClockPrimitive
local notation "D" => liEvenCrossActualClockLogHistory
local notation "H" => liEvenCrossActualClockHistoryCoefficient
local notation "ell" => liEvenCrossActualClockHistoryScale
local notation "Cout" => liEvenCrossActualClockHistoryOutsideCorrelation
local notation "U" => liClockThetaScoreCostProfile
local notation "Rs" => liClockThetaScoreReserveProfile
local notation "IU" => liEvenCrossActualClockScoreCostIntegral
local notation "IR" => liEvenCrossActualClockScoreReserveIntegral
local notation "IK" => liEvenCrossActualClockScoreKernelIntegral
local notation "V" => liEvenCrossActualClockScoreHistoryBudget
local notation "A0" => xiShiftAbsoluteMass 0

/-- The near-history reserve `A_near(t) = ∫₀^ℓ D(s)(H_t(s) - K(t)/2) ds`. -/
def liEvenCrossActualClockHistoryNearReserve (t : ℝ) : ℝ :=
  ∫ s in 0..ell t, D s*(H t s - K t/2)

/-- The early-clock reserve `ζ_t = q A₀ K(t) min(ℓ/2, 20)³/48`, `q = 1051/2184`. -/
def liEvenCrossActualClockHistoryEarlyReserve (t : ℝ) : ℝ :=
  (1051/2184 : ℝ)*A0*K t*(min (ell t/2) 20)^3/48

/-- The source-derived uniform score ceiling `θ ∈ (0,1)`. -/
def liClockThetaScoreCeiling : ℝ := Classical.choose liClockThetaScoreProfiles_uniform_reserve

/-- The fixed-lag score slope ratio `a(r) = 303K'(r)/U(r)`. -/
def liClockThetaScoreSlopeRatio (r : ℝ) : ℝ := 303*K1 r/(U (r:ℂ)).re

/-- The normalized outer-history probability `dΠ_t = 1_{[ℓ,t]}(s) sD(s)U(t-s) ds / I_U`. -/
def liEvenCrossActualClockOuterHistoryMeasure (t : ℝ) : Measure ℝ :=
  (volume.restrict (Icc (ell t) t)).withDensity
    (fun s => ENNReal.ofReal (s*D s*(U ((t-s):ℂ)).re/IU t))

/-- The normalized score slope `ρ_t = ∫ a(t-s) dΠ_t(s)`. -/
def liEvenCrossActualClockOuterScoreRatio (t : ℝ) : ℝ :=
  ∫ s, liClockThetaScoreSlopeRatio (t-s) ∂liEvenCrossActualClockOuterHistoryMeasure t

/-- The normalized budget `β_t = 303(I_K + V)/I_U`. -/
def liEvenCrossActualClockOuterBudgetRatio (t : ℝ) : ℝ := 303*(IK t + V t)/IU t

local notation "Anear" => liEvenCrossActualClockHistoryNearReserve
local notation "zeta" => liEvenCrossActualClockHistoryEarlyReserve
local notation "thc" => liClockThetaScoreCeiling
local notation "a" => liClockThetaScoreSlopeRatio
local notation "Pi" => liEvenCrossActualClockOuterHistoryMeasure
local notation "rho" => liEvenCrossActualClockOuterScoreRatio
local notation "beta" => liEvenCrossActualClockOuterBudgetRatio

private theorem sb_K_cont : Continuous K :=
  contDiff_liEvenCrossActualClockBorelKernel.continuous_deriv (by simp)
private theorem sb_K1_cont : Continuous K1 := by
  have hc : ContDiff ℝ (2:ℕ∞) B :=
    contDiff_liEvenCrossActualClockBorelKernel.of_le (by exact_mod_cast (le_top : (2:ℕ∞) ≤ ⊤))
  exact (show ContDiff ℝ (1:ℕ∞) K from hc.deriv').continuous_deriv_one
private theorem sb_D_cont : Continuous D :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_liEvenCrossActualClockLogHistory t).continuousAt
private theorem sb_H_cont (t : ℝ) : Continuous (fun s => H t s) := by
  unfold liEvenCrossActualClockHistoryCoefficient
  exact (sb_K_cont.comp (continuous_const.sub continuous_id)).sub
    (continuous_id.mul (sb_K1_cont.comp (continuous_const.sub continuous_id)))
private theorem sb_U_cont : Continuous U := continuous_iff_continuousAt.mpr fun z =>
  (liClockThetaScoreProfiles_analyticAt z).2.2.2.1.continuousAt
private theorem sb_R_cont : Continuous Rs := continuous_iff_continuousAt.mpr fun z =>
  (liClockThetaScoreProfiles_analyticAt z).2.2.2.2.continuousAt
private theorem sb_lag_cont {f : ℂ → ℂ} (hf : Continuous f) (t : ℝ) :
    Continuous (fun s : ℝ => (f ((t-s):ℂ)).re) :=
  Complex.continuous_re.comp (hf.comp ((continuous_const (y := (t:ℂ))).sub
    Complex.continuous_ofReal))

private theorem sb_P_eq {t : ℝ} (ht : 0 < t) : P t = t*deriv D t := by
  rw [(hasDerivAt_liEvenCrossActualClockLogHistory t).deriv,
    liEvenCrossActualClockLogHistoryDensity]
  field_simp

private theorem sb_near_eq (t : ℝ) :
    Anear t = (∫ s in 0..ell t, D s*H t s) - K t/2*∫ s in 0..ell t, D s := by
  unfold liEvenCrossActualClockHistoryNearReserve
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
    (by exact (sb_D_cont.mul (sb_H_cont t)).intervalIntegrable _ _ :
      IntervalIntegrable (fun s => D s*H t s) volume 0 (ell t))
    (by exact (sb_D_cont.const_mul _).intervalIntegrable _ _ :
      IntervalIntegrable (fun s => K t/2*D s) volume 0 (ell t))]
  congr 1; funext s; ring

/-- **Exact budget identity (B1).**  For `t > 0`,
`P(t) = tK(t) + ∫₀ᵗ D(s)H_t(s) ds = V(t) + A_near(t) - C_out(t)`. -/
theorem liEvenCrossActualClockPrimitive_eq_budget_add_near_sub_outside {t : ℝ} (ht : 0 < t) :
    P t = t*K t + (∫ s in 0..t, D s*H t s) ∧ P t = V t + Anear t - Cout t := by
  have h1 : P t = t*K t + (∫ s in 0..t, D s*H t s) := by
    rw [sb_P_eq ht]; exact liEvenCrossActualClockLogHistory_slope_volterra ht.le
  refine ⟨h1, ?_⟩
  have hc : Continuous (fun s => D s*H t s) := sb_D_cont.mul (sb_H_cont t)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 (ell t)) (hc.intervalIntegrable (μ := volume) (ell t) t)
  have hout : Cout t = -∫ s in ell t..t, D s*H t s := by
    unfold liEvenCrossActualClockHistoryOutsideCorrelation
    rw [← intervalIntegral.integral_neg]
    congr 1; funext s; unfold liEvenCrossActualClockHistoryCoefficient; ring
  rw [h1, ← hsplit, sb_near_eq, hout]
  unfold liEvenCrossActualClockScoreHistoryBudget
  ring

/-- At a guarded zero the left slope is nonpositive: `D'(t) ≤ 0`, hence `P(t) ≤ 0`. -/
theorem liEvenCrossActualClockHistory_guarded_zero_slope {t : ℝ} (ht : 0 < t) (hz : D t = 0)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) : deriv D t ≤ 0 ∧ P t ≤ 0 := by
  have hderiv : deriv D t ≤ 0 := by
    have hlo : Ioi (-t) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by linarith)
    have hlo' : ∀ᶠ h : ℝ in 𝓝[<] (0 : ℝ), -t < h := nhdsWithin_le_nhds hlo
    have hleft : ∀ᶠ h : ℝ in 𝓝[<] (0 : ℝ), h < 0 := self_mem_nhdsWithin
    have hslope : ∀ᶠ h : ℝ in 𝓝[<] (0 : ℝ), h⁻¹ • (D (t+h)-D t) ≤ 0 := by
      filter_upwards [hlo', hleft] with h hlow hneg
      have hD := hHist (t+h) ⟨by linarith, by linarith⟩
      simpa only [smul_eq_mul, hz, sub_zero] using
        mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hneg.le) hD
    exact le_of_tendsto ((hasDerivAt_liEvenCrossActualClockLogHistory t).differentiableAt.hasDerivAt
      |>.tendsto_slope_zero_left) hslope
  refine ⟨hderiv, ?_⟩
  rw [sb_P_eq ht]
  exact mul_nonpos_of_nonneg_of_nonpos ht.le hderiv

/-- **Near reserve (B2).**  If `D ≥ 0` on `[0,t]`, `t > 0`, then
`A_near(t) ≥ (K(t)/4)∫₀^{ℓ/2} D ≥ ζ_t > 0`. -/
theorem liEvenCrossActualClockHistoryNearReserve_lower {t : ℝ} (ht : 0 < t)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    K t/4*(∫ s in 0..ell t/2, D s) ≤ Anear t ∧ zeta t ≤ Anear t ∧ 0 < zeta t := by
  have hl := liEvenCrossActualClockHistory_recent_lower ht hHist
  have hr := liEvenCrossActualClockHistory_recent_origin_reserve ht hHist
  dsimp only at hr
  have hK := liEvenCrossActualClockBorel_deriv_pos ht
  have h1 : K t/4*(∫ s in 0..ell t/2, D s) ≤ Anear t := by rw [sb_near_eq]; linarith
  have hA := xiShiftAbsoluteMass_pos 0
  have he := (liEvenCrossActualClockHistory_geometry ht).2.2.1
  have hr0 : 0 < min (ell t/2) 20 := lt_min (by linarith) (by norm_num)
  have hpos : 0 < zeta t := by
    unfold liEvenCrossActualClockHistoryEarlyReserve
    positivity
  refine ⟨h1, ?_, hpos⟩
  calc zeta t = K t/4*((1051/2184 : ℝ)*A0*(min (ell t/2) 20)^3/12) := by
        unfold liEvenCrossActualClockHistoryEarlyReserve; ring
    _ ≤ K t/4*(∫ s in 0..ell t/2, D s) := mul_le_mul_of_nonneg_left hr.1 (by positivity)
    _ ≤ Anear t := h1

/-- **First-zero barrier.**  At a guarded zero, `C_out - V = A_near - P(t) ≥ ζ_t > 0`. -/
theorem liEvenCrossActualClockHistory_guarded_zero_outside_excess {t : ℝ} (ht : 0 < t)
    (hz : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    Cout t - V t = Anear t - P t ∧ zeta t ≤ Cout t - V t ∧ 0 < zeta t := by
  have h1 := (liEvenCrossActualClockPrimitive_eq_budget_add_near_sub_outside ht).2
  have h2 := (liEvenCrossActualClockHistory_guarded_zero_slope ht hz hHist).2
  have h3 := liEvenCrossActualClockHistoryNearReserve_lower ht hHist
  refine ⟨by linarith, by linarith [h3.2.1], h3.2.2⟩

/-- The universal guarded-zero outside budget is equivalent to positivity of the history at
every positive clock. -/
theorem liEvenCrossActualClockHistory_first_zero_budget_iff_pos :
    (∀ t : ℝ, 20 < t → D t = 0 → (∀ s ∈ Icc 0 t, 0 ≤ D s) → Cout t ≤ V t) ↔
      ∀ t : ℝ, 0 < t → 0 < D t := by
  constructor
  · intro h
    exact liEvenCrossActualClockLogHistory_pos_of_first_zero_budget fun t ht hz hHist => by
      simpa [liEvenCrossActualClockScoreHistoryBudget] using h t ht hz hHist
  · intro h t ht hz _
    exact absurd hz (h t (by linarith)).ne'

/-- The ceiling `θ` lies in `(0,1)` and bounds the profiles at every real lag:
`(1-θ)U ≤ R_score` and `0 < 303K' ≤ θU`. -/
theorem liClockThetaScoreCeiling_spec :
    0 < thc ∧ thc < 1 ∧ ∀ r : ℝ, 0 < (U (r:ℂ)).re ∧
      (1-thc)*(U (r:ℂ)).re ≤ (Rs (r:ℂ)).re ∧ 0 < 303*K1 r ∧ 303*K1 r ≤ thc*(U (r:ℂ)).re := by
  obtain ⟨h0, h1, _, h⟩ := Classical.choose_spec liClockThetaScoreProfiles_uniform_reserve
  exact ⟨h0, h1, fun r => ⟨(h r).2.1, (h r).2.2.2.1, (h r).2.2.2.2.2.1, (h r).2.2.2.2.2.2⟩⟩

/-- The slope ratio is continuous, lies in `(0, θ]` at every real lag and tends to `0`. -/
theorem liClockThetaScoreSlopeRatio_spec :
    Continuous a ∧ (∀ r : ℝ, 0 < a r ∧ a r ≤ thc) ∧ Tendsto a atTop (𝓝 0) := by
  obtain ⟨_, _, h⟩ := liClockThetaScoreCeiling_spec
  refine ⟨?_, fun r => ⟨div_pos (h r).2.2.1 (h r).1, (div_le_iff₀ (h r).1).2 (h r).2.2.2⟩,
    liClockThetaScoreProfiles_sharp_reserve.1⟩
  exact (continuous_const.mul sb_K1_cont).div
    (Complex.continuous_re.comp (sb_U_cont.comp Complex.continuous_ofReal)) fun r => (h r).1.ne'

/-- On every compact lag window `[0, R]` the slope ratio has a positive lower bound. -/
theorem exists_liClockThetaScoreSlopeRatio_lower {R : ℝ} (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Icc 0 R, c ≤ a r := by
  obtain ⟨hc, hb, _⟩ := liClockThetaScoreSlopeRatio_spec
  obtain ⟨x, -, hx⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hR) hc.continuousOn
  exact ⟨a x, (hb x).1, fun r hr => hx hr⟩

private theorem sb_U_lag_pos (t s : ℝ) : 0 < (U ((t-s):ℂ)).re := by
  rw [← Complex.ofReal_sub]; exact (liClockThetaScoreCeiling_spec.2.2 (t-s)).1

private theorem sb_W_cont (t : ℝ) : Continuous (fun s => s*D s*(U ((t-s):ℂ)).re) :=
  (continuous_id.mul sb_D_cont).mul (sb_lag_cont sb_U_cont t)

private theorem sb_geom {t : ℝ} (ht : 20 < t) : 0 < ell t ∧ ell t ≤ t := by
  have h := liEvenCrossActualClockHistory_geometry (show 0 < t by linarith)
  exact ⟨h.2.2.1, by linarith [h.2.2.2]⟩

private theorem sb_W_nonneg {t : ℝ} (ht : 20 < t) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) {s : ℝ}
    (hs : s ∈ Icc (ell t) t) : 0 ≤ s*D s*(U ((t-s):ℂ)).re := by
  have hs0 : 0 ≤ s := (sb_geom ht).1.le.trans hs.1
  exact mul_nonneg (mul_nonneg hs0 (hHist s ⟨hs0, hs.2⟩)) (sb_U_lag_pos t s).le

private theorem sb_V_pos {t : ℝ} (ht : 20 < t) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) : 0 < V t := by
  have ht0 : 0 < t := by linarith
  have hK := liEvenCrossActualClockBorel_deriv_pos ht0
  have hg := sb_geom ht
  have hint : 0 ≤ ∫ s in 0..ell t, D s :=
    intervalIntegral.integral_nonneg hg.1.le fun s hs => hHist s ⟨hs.1, hs.2.trans hg.2⟩
  unfold liEvenCrossActualClockScoreHistoryBudget
  have := mul_pos ht0 hK
  have := mul_nonneg (show 0 ≤ K t/2 by positivity) hint
  linarith

private theorem sb_IU_pos {t : ℝ} (ht : 20 < t) (hz : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    0 < IU t := by
  have hx := liEvenCrossActualClockHistory_guarded_zero_outside_excess (by linarith) hz hHist
  have hV := sb_V_pos ht hHist
  have hc := liEvenCrossActualClockScoreHistory_cost_identity ht hz hHist
  have hp := liEvenCrossActualClockScoreHistory_positive_reserve ht hz hHist
  linarith [hx.2.1, hx.2.2, hp.2.1, hp.2.2.1]

private theorem sb_reserve_slack {t : ℝ} (ht : 20 < t) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    (1-thc)*IU t ≤ IR t := by
  have hg := sb_geom ht
  unfold liEvenCrossActualClockScoreCostIntegral liEvenCrossActualClockScoreReserveIntegral
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hg.2
    (((sb_W_cont t).const_mul _).intervalIntegrable _ _)
    (((continuous_id.mul sb_D_cont).mul (sb_lag_cont sb_R_cont t)).intervalIntegrable _ _)
    fun s hs => ?_
  have hw : 0 ≤ s*D s := by
    have hs0 : 0 ≤ s := hg.1.le.trans hs.1
    exact mul_nonneg hs0 (hHist s ⟨hs0, hs.2⟩)
  have hb := (liClockThetaScoreCeiling_spec.2.2 (t-s)).2.1
  rw [Complex.ofReal_sub] at hb
  nlinarith

/-- **Full budget identity (B3).**  At a guarded zero,
`θ I_U - 303(I_K + V) = 303(A_near - P(t)) + (I_R - (1-θ)I_U)`, the score slack is
nonnegative, and the left side is at least `303 ζ_t > 0`. -/
theorem liEvenCrossActualClockScoreHistory_budget_defect {t : ℝ} (ht : 20 < t) (hz : D t = 0)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    thc*IU t - 303*(IK t + V t) = 303*(Anear t - P t) + (IR t - (1-thc)*IU t) ∧
      0 ≤ IR t - (1-thc)*IU t ∧ 303*zeta t ≤ thc*IU t - 303*(IK t + V t) ∧ 0 < zeta t := by
  have hx := liEvenCrossActualClockHistory_guarded_zero_outside_excess (by linarith) hz hHist
  have hc := liEvenCrossActualClockScoreHistory_cost_identity ht hz hHist
  have hs := sb_reserve_slack ht hHist
  refine ⟨by linarith [hx.1], by linarith, by linarith [hx.1, hx.2.1], hx.2.2⟩

/-- The universal guarded-zero score budget `θ I_U ≤ 303(I_K + V)` is equivalent to positivity
of the history at every positive clock (both sides exclude guarded zeros). -/
theorem liEvenCrossActualClockScoreHistory_budget_iff_pos :
    (∀ t : ℝ, 20 < t → D t = 0 → (∀ s ∈ Icc 0 t, 0 ≤ D s) → thc*IU t ≤ 303*(IK t + V t)) ↔
      ∀ t : ℝ, 0 < t → 0 < D t := by
  constructor
  · intro h
    refine liEvenCrossActualClockHistory_first_zero_budget_iff_pos.1 fun t ht hz hHist => ?_
    have hd := liEvenCrossActualClockScoreHistory_budget_defect ht hz hHist
    have := h t ht hz hHist
    linarith [hd.2.2.1, hd.2.2.2]
  · intro h t ht hz _
    exact absurd hz (h t (by linarith)).ne'

private theorem sb_Pi_finite (t : ℝ) : IsFiniteMeasure (Pi t) :=
  isFiniteMeasure_withDensity_ofReal
    ((sb_W_cont t).div_const (IU t)).integrableOn_Icc.hasFiniteIntegral

private theorem sb_Pi_ae (t : ℝ) : ∀ᵐ s ∂Pi t, s ∈ Icc (ell t) t :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

/-- At a guarded zero every `Π_t`-integral is the normalized weighted integral over `[ℓ, t]`. -/
theorem integral_liEvenCrossActualClockOuterHistoryMeasure {t : ℝ} (ht : 20 < t) (hz : D t = 0)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) (g : ℝ → ℝ) :
    ∫ s, g s ∂Pi t = (∫ s in Icc (ell t) t, s*D s*(U ((t-s):ℂ)).re*g s)/IU t := by
  have hIU := sb_IU_pos ht hz hHist
  unfold liEvenCrossActualClockOuterHistoryMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((sb_W_cont t).div_const (IU t)).measurable.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_div]
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [ENNReal.toReal_ofReal (div_nonneg (sb_W_nonneg ht hHist hs) hIU.le), smul_eq_mul]
  ring

private theorem sb_Icc_eq {t : ℝ} (ht : 20 < t) {f : ℝ → ℝ} :
    (∫ s in Icc (ell t) t, f s) = ∫ s in ell t..t, f s := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (sb_geom ht).2]

private theorem sb_Pi_prob {t : ℝ} (ht : 20 < t) (hz : D t = 0)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) : IsProbabilityMeasure (Pi t) := by
  have hIU := sb_IU_pos ht hz hHist
  have h := integral_liEvenCrossActualClockOuterHistoryMeasure ht hz hHist (fun _ => 1)
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [sb_Icc_eq ht, show (∫ s in ell t..t, s*D s*(U ((t-s):ℂ)).re) = IU t from rfl,
    div_self hIU.ne'] at h
  exact ⟨(ENNReal.toReal_eq_one_iff _).1 h⟩

private theorem sb_rho_eq {t : ℝ} (ht : 20 < t) (hz : D t = 0)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) : rho t = 303*(Cout t + IK t)/IU t := by
  unfold liEvenCrossActualClockOuterScoreRatio
  rw [integral_liEvenCrossActualClockOuterHistoryMeasure ht hz hHist, sb_Icc_eq ht]
  congr 1
  have e : (∫ s in ell t..t, s*D s*(U ((t-s):ℂ)).re*a (t-s)) =
      ∫ s in ell t..t, 303*(s*D s*K1 (t-s)) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hU := (sb_U_lag_pos t s).ne'
    unfold liClockThetaScoreSlopeRatio
    rw [Complex.ofReal_sub]
    field_simp
  have i1 : IntervalIntegrable (fun s => D s*(s*K1 (t-s)-K (t-s))) volume (ell t) t :=
    (sb_D_cont.mul ((continuous_id.mul (sb_K1_cont.comp (continuous_const.sub continuous_id))).sub
      (sb_K_cont.comp (continuous_const.sub continuous_id)))).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s => D s*K (t-s)) volume (ell t) t :=
    (sb_D_cont.mul (sb_K_cont.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
  rw [e, intervalIntegral.integral_const_mul]
  unfold liEvenCrossActualClockHistoryOutsideCorrelation liEvenCrossActualClockScoreKernelIntegral
  rw [← intervalIntegral.integral_add i1 i2]
  congr 2; funext s; ring

/-- **Normalized outer-history order (B9).**  At a guarded zero, `I_U > 0`, `Π_t` is a
probability measure carried by `[ℓ, t]`, `ρ_t - β_t = 303(A_near - P(t))/I_U ≥ 303ζ_t/I_U`,
`0 < β_t < ρ_t ≤ θ`, and the outside budget `C_out ≤ V` holds iff `ρ_t ≤ β_t`. -/
theorem liEvenCrossActualClockOuterHistory_order {t : ℝ} (ht : 20 < t) (hz : D t = 0)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    0 < IU t ∧ IsProbabilityMeasure (Pi t) ∧ (∀ᵐ s ∂Pi t, s ∈ Icc (ell t) t) ∧
      rho t = 303*(Cout t + IK t)/IU t ∧
      rho t - beta t = 303*(Anear t - P t)/IU t ∧ 303*zeta t/IU t ≤ rho t - beta t ∧
      0 < beta t ∧ beta t < rho t ∧ rho t ≤ thc ∧ (Cout t ≤ V t ↔ rho t ≤ beta t) := by
  have hIU := sb_IU_pos ht hz hHist
  have hx := liEvenCrossActualClockHistory_guarded_zero_outside_excess (by linarith) hz hHist
  have hV := sb_V_pos ht hHist
  have hp := liEvenCrossActualClockScoreHistory_positive_reserve ht hz hHist
  have hρ := sb_rho_eq ht hz hHist
  have hdiff : rho t - beta t = 303*(Anear t - P t)/IU t := by
    rw [hρ, liEvenCrossActualClockOuterBudgetRatio, ← sub_div, ← hx.1]; ring
  have hβ : 0 < beta t := by
    unfold liEvenCrossActualClockOuterBudgetRatio
    have := hp.2.2.1
    exact div_pos (by linarith) hIU
  have hlow : 303*zeta t/IU t ≤ rho t - beta t := by
    rw [hdiff]; exact div_le_div_of_nonneg_right (by linarith [hx.1, hx.2.1]) hIU.le
  have hz0 : 0 < 303*zeta t/IU t := div_pos (by linarith [hx.2.2]) hIU
  have hθ : rho t ≤ thc := by
    rw [hρ, div_le_iff₀ hIU]
    have hg := sb_geom ht
    have hint : 303*(Cout t + IK t) = ∫ s in ell t..t, s*D s*(303*K1 (t-s)) := by
      have i1 : IntervalIntegrable (fun s => D s*(s*K1 (t-s)-K (t-s))) volume (ell t) t :=
        (sb_D_cont.mul ((continuous_id.mul (sb_K1_cont.comp (continuous_const.sub continuous_id))).sub
          (sb_K_cont.comp (continuous_const.sub continuous_id)))).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun s => D s*K (t-s)) volume (ell t) t :=
        (sb_D_cont.mul (sb_K_cont.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
      unfold liEvenCrossActualClockHistoryOutsideCorrelation
        liEvenCrossActualClockScoreKernelIntegral
      rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_const_mul]
      congr 1; funext s; ring
    rw [hint]
    unfold liEvenCrossActualClockScoreCostIntegral
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hg.2
      ((((continuous_id.mul sb_D_cont).mul (continuous_const.mul
        (sb_K1_cont.comp (continuous_const.sub continuous_id))))).intervalIntegrable _ _)
      (((sb_W_cont t).const_mul _).intervalIntegrable _ _) fun s hs => ?_
    have hw : 0 ≤ s*D s := by
      have hs0 : 0 ≤ s := hg.1.le.trans hs.1
      exact mul_nonneg hs0 (hHist s ⟨hs0, hs.2⟩)
    have hb := (liClockThetaScoreCeiling_spec.2.2 (t-s)).2.2.2
    rw [Complex.ofReal_sub] at hb
    nlinarith
  refine ⟨hIU, sb_Pi_prob ht hz hHist, sb_Pi_ae t, hρ, hdiff, hlow, hβ, by linarith, hθ, ?_⟩
  constructor
  · intro h
    have : rho t - beta t ≤ 0 := by
      rw [hdiff]; exact div_nonpos_of_nonpos_of_nonneg (by linarith [hx.1]) hIU.le
    linarith
  · intro h
    linarith [hx.2.1, hx.2.2, hlow, hz0]

private theorem sb_a_integrable {t : ℝ} :
    Integrable (fun s => a (t-s)) (Pi t) := by
  haveI := sb_Pi_finite t
  obtain ⟨hc, hb, _⟩ := liClockThetaScoreSlopeRatio_spec
  refine Integrable.of_bound (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    thc (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (hb _).1]
  exact (hb _).2

/-- **Terminal mass (B10).**  At a guarded zero, if `a ≤ ε < θ` at every lag `≥ R`, then
`ρ_t ≤ ε + (θ - ε)Π_t(t-s < R)` and `Π_t(t-s < R) ≥ (β_t + 303ζ_t/I_U - ε)/(θ - ε)`; if
`c ≤ a` on `[0, R]`, then `c Π_t(t-s < R) ≤ ρ_t`. -/
theorem liEvenCrossActualClockOuterHistory_terminal_mass {t : ℝ} (ht : 20 < t) (hz : D t = 0)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    (∀ ε R : ℝ, ε < thc → (∀ r, R ≤ r → a r ≤ ε) →
      rho t ≤ ε + (thc - ε)*(Pi t).real (Ioi (t-R)) ∧
      (beta t + 303*zeta t/IU t - ε)/(thc - ε) ≤ (Pi t).real (Ioi (t-R))) ∧
    (∀ c R : ℝ, (∀ r ∈ Icc 0 R, c ≤ a r) → c*(Pi t).real (Ioi (t-R)) ≤ rho t) := by
  haveI := sb_Pi_prob ht hz hHist
  obtain ⟨_, hb, _⟩ := liClockThetaScoreSlopeRatio_spec
  have hlow := (liEvenCrossActualClockOuterHistory_order ht hz hHist).2.2.2.2.2.1
  have hind : ∀ R : ℝ, Integrable ((Ioi (t-R)).indicator (1 : ℝ → ℝ)) (Pi t) := fun R =>
    (integrable_const (1:ℝ)).indicator measurableSet_Ioi
  have hmass : ∀ R : ℝ,
      ∫ s, (Ioi (t-R)).indicator (1 : ℝ → ℝ) s ∂Pi t = (Pi t).real (Ioi (t-R)) := fun R =>
    integral_indicator_one measurableSet_Ioi
  refine ⟨fun ε R hεθ hR => ?_, fun c R hc => ?_⟩
  · have hle : (fun s => a (t-s)) ≤ᵐ[Pi t]
        fun s => ε + (thc - ε)*(Ioi (t-R)).indicator (1 : ℝ → ℝ) s := by
      filter_upwards [sb_Pi_ae t] with s hs
      rw [Set.indicator_apply]
      split_ifs with h
      · simp only [Pi.one_apply, mul_one]; linarith [(hb (t-s)).2]
      · simp only [mul_zero, add_zero]
        exact hR (t-s) (by simp only [mem_Ioi, not_lt] at h; linarith)
    have hint : ∫ s, a (t-s) ∂Pi t ≤
        ∫ s, (ε + (thc - ε)*(Ioi (t-R)).indicator (1 : ℝ → ℝ) s) ∂Pi t :=
      integral_mono_ae sb_a_integrable
        ((integrable_const ε).add ((hind R).const_mul (thc-ε))) hle
    rw [integral_add (integrable_const ε) ((hind R).const_mul _), integral_const,
      integral_const_mul, hmass, probReal_univ, smul_eq_mul, one_mul] at hint
    have h1 : rho t ≤ ε + (thc - ε)*(Pi t).real (Ioi (t-R)) := hint
    refine ⟨h1, ?_⟩
    rw [div_le_iff₀ (by linarith)]
    linarith [mul_comm (thc - ε) ((Pi t).real (Ioi (t-R)))]
  · have hle : (fun s => c*(Ioi (t-R)).indicator (1 : ℝ → ℝ) s) ≤ᵐ[Pi t] fun s => a (t-s) := by
      filter_upwards [sb_Pi_ae t] with s hs
      rw [Set.indicator_apply]
      split_ifs with h
      · simp only [Pi.one_apply, mul_one]
        exact hc (t-s) ⟨by linarith [hs.2], by simp only [mem_Ioi] at h; linarith⟩
      · simp only [mul_zero]; exact (hb (t-s)).1.le
    have hint := integral_mono_ae ((hind R).const_mul c) sb_a_integrable hle
    rwa [integral_const_mul, hmass] at hint

/-- **Terminal-mass criterion (B11).**  Along any sequence of guarded zeros, `ρ → 0` iff every
fixed terminal mass `Π(t - s < R)` tends to `0`; then also `β → 0` and `ζ/I_U → 0`. -/
theorem liEvenCrossActualClockOuterHistory_sequence_criterion (τ : ℕ → ℝ)
    (hZ : ∀ n, 20 < τ n ∧ D (τ n) = 0 ∧ ∀ s ∈ Icc 0 (τ n), 0 ≤ D s) :
    (Tendsto (fun n => rho (τ n)) atTop (𝓝 0) ↔
      ∀ R : ℝ, 0 < R → Tendsto (fun n => (Pi (τ n)).real (Ioi (τ n - R))) atTop (𝓝 0)) ∧
    (Tendsto (fun n => rho (τ n)) atTop (𝓝 0) →
      Tendsto (fun n => beta (τ n)) atTop (𝓝 0) ∧
      Tendsto (fun n => zeta (τ n)/IU (τ n)) atTop (𝓝 0)) := by
  have hord : ∀ n, 0 < beta (τ n) ∧ beta (τ n) < rho (τ n) ∧
      303*zeta (τ n)/IU (τ n) ≤ rho (τ n) - beta (τ n) ∧ 0 < IU (τ n) ∧ 0 < zeta (τ n) := by
    intro n
    obtain ⟨h1, -, -, -, -, h6, h7, h8, -⟩ :=
      liEvenCrossActualClockOuterHistory_order (hZ n).1 (hZ n).2.1 (hZ n).2.2
    exact ⟨h7, h8, h6, h1,
      (liEvenCrossActualClockScoreHistory_budget_defect (hZ n).1 (hZ n).2.1 (hZ n).2.2).2.2.2⟩
  have hterm := fun n =>
    liEvenCrossActualClockOuterHistory_terminal_mass (hZ n).1 (hZ n).2.1 (hZ n).2.2
  obtain ⟨_, _, hlim⟩ := liClockThetaScoreSlopeRatio_spec
  have hθ := liClockThetaScoreCeiling_spec.1
  refine ⟨⟨fun h R hR => ?_, fun h => ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · obtain ⟨c, hc, hca⟩ := exists_liClockThetaScoreSlopeRatio_lower hR.le
    have hup : Tendsto (fun n => rho (τ n)/c) atTop (𝓝 0) := by simpa using h.div_const c
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => measureReal_nonneg) fun n => ?_
    rw [le_div_iff₀ hc, mul_comm]
    exact (hterm n).2 c R hca
  · rw [tendsto_order]
    refine ⟨fun x hx => Eventually.of_forall fun n => hx.trans ((hord n).1.trans (hord n).2.1),
      fun x hx => ?_⟩
    have hε : 0 < min (x/2) (thc/2) := lt_min (by linarith) (by linarith)
    have hεθ : min (x/2) (thc/2) < thc := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hεx : min (x/2) (thc/2) ≤ x/2 := min_le_left _ _
    obtain ⟨R0, hR0⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε))
    have hRa : ∀ r, max R0 1 ≤ r → a r ≤ min (x/2) (thc/2) := fun r hr =>
      (hR0 r ((le_max_left _ _).trans hr)).le
    have hm := (h (max R0 1) (lt_max_of_lt_right one_pos)).const_mul (thc - min (x/2) (thc/2))
    rw [mul_zero] at hm
    filter_upwards [hm.eventually (gt_mem_nhds (show (0:ℝ) < x/2 by linarith))] with n hn
    have := ((hterm n).1 _ _ hεθ hRa).1
    linarith
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun n => (hord n).1.le) fun n => (hord n).2.1.le
  · have hup : Tendsto (fun n => rho (τ n)/303) atTop (𝓝 0) := by simpa using h.div_const 303
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (div_pos (hord n).2.2.2.2 (hord n).2.2.2.1).le) fun n => ?_
    obtain ⟨h1, h2, h3, h4, -⟩ := hord n
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 303)]
    rw [mul_div_assoc] at h3
    linarith

end
end RHTower
