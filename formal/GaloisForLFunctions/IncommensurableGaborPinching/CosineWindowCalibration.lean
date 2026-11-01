import GaloisForLFunctions.IncommensurableGaborPinching.CosineWindowArbitraryBandwidth
import GaloisForLFunctions.RHTower.ZetaOffLineMomentMontgomeryTaylor

/-!
# Matched diagonal calibration for cosine windows above bandwidth one

The cosine shape is held at one while bandwidth varies. Its actual tapered moments
converge to the shape-one moments. The resulting diagonal rate improves the box-window
rate by at least `43λ/7500` for `λ ≥ 1`, leaving margin `79/1250` above three quarters
at bandwidth four thirds. This evaluates the window coefficient, not the signed prime surplus.
-/

noncomputable section

open Real Filter Topology MeasureTheory Zeta23 Zeta23.ThmD

namespace GaloisForLFunctions.IncommensurableGaborPinching

/-- Variance on the unit interval bounds the squared cosine mean by its second moment. -/
theorem aStar_sq_le_bStar (κ : ℝ) : aStar κ ^ 2 ≤ bStar κ := by
  let a := aStar κ
  have hv : Continuous (vStar κ) := by unfold vStar; fun_prop
  have h1 := hv.intervalIntegrable (μ := volume) (-(1 : ℝ) / 2) (1 / 2)
  have h2 : IntervalIntegrable (fun u => vStar κ u ^ 2) volume (-(1 : ℝ) / 2) (1 / 2) :=
    (by fun_prop : Continuous (fun u => vStar κ u ^ 2)).intervalIntegrable _ _
  have hl := h1.const_mul (2 * a)
  have hnonneg : 0 ≤ ∫ u in (-(1 : ℝ) / 2)..(1 / 2), (vStar κ u - a) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => sq_nonneg _)
  have heq : (fun u => (vStar κ u - a) ^ 2) =
      (fun u => (vStar κ u ^ 2 - (2 * a) * vStar κ u) + a ^ 2) := by
    funext u
    ring
  rw [heq, intervalIntegral.integral_add (h2.sub hl) intervalIntegrable_const,
    intervalIntegral.integral_sub h2 hl, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hnonneg
  change 0 ≤ bStar κ - (2 * a) * a + (1 / 2 - -(1 : ℝ) / 2) * a ^ 2 at hnonneg
  change a ^ 2 ≤ bStar κ
  nlinarith only [hnonneg]

/-- Limiting diagonal rate of a shape-one cosine window at bandwidth `lam`. -/
def shapeOneCosineRate (lam : ℝ) : ℝ :=
  2 - (bStar 1 + lam ^ 2 * jStar 1) / (lam * aStar 1 ^ 2)

private theorem shapeOne_moment_payment :
    bStar 1 + jStar 1 ≤ (3319 / 2500 : ℝ) * aStar 1 ^ 2 := by
  have ha : 0 < aStar 1 := lt_of_lt_of_le (by norm_num) (aStar_bounds (by norm_num) le_rfl).1
  have heq : (bStar 1 + jStar 1) / aStar 1 ^ 2 = 1 / cStar 1 := by
    rw [← cRatio_star (show (0 : ℝ) < 1 by norm_num) le_rfl]
    simp only [cRatio, one_mul, one_pow, one_div, inv_div]
  have hHD := RHTower.HD_one_ge
  unfold HD at hHD
  have hupper : (bStar 1 + jStar 1) / aStar 1 ^ 2 ≤ 3319 / 2500 := by
    rw [heq]
    linarith only [hHD]
  exact (div_le_iff₀ (sq_pos_of_pos ha)).mp hupper

/-- A fixed cosine shape improves the box diagonal rate throughout the trans-threshold range. -/
theorem shapeOneCosineRate_ge_box (lam : ℝ) (hlam : 1 ≤ lam) :
    (2 - 1 / lam - lam / 3) + 43 * lam / 7500 ≤ shapeOneCosineRate lam := by
  have hlam0 : 0 < lam := by linarith only [hlam]
  have ha : 0 < aStar 1 := lt_of_lt_of_le (by norm_num) (aStar_bounds (by norm_num) le_rfl).1
  have hsq : 0 ≤ lam ^ 2 - 1 := by nlinarith only [hlam]
  have hB := mul_le_mul_of_nonneg_left (aStar_sq_le_bStar 1) hsq
  have hBJ := mul_le_mul_of_nonneg_left shapeOne_moment_payment (sq_nonneg lam)
  have hpay : bStar 1 + lam ^ 2 * jStar 1 ≤
      (1 + lam ^ 2 / 3 - 43 * lam ^ 2 / 7500) * aStar 1 ^ 2 := by
    nlinarith only [hB, hBJ]
  have hquot : (bStar 1 + lam ^ 2 * jStar 1) / (lam * aStar 1 ^ 2) ≤
      1 / lam + lam / 3 - 43 * lam / 7500 := by
    rw [div_le_iff₀ (mul_pos hlam0 (sq_pos_of_pos ha))]
    have heq : (1 / lam + lam / 3 - 43 * lam / 7500) * (lam * aStar 1 ^ 2) =
        (1 + lam ^ 2 / 3 - 43 * lam ^ 2 / 7500) * aStar 1 ^ 2 := by
      field_simp
    rw [heq]
    exact hpay
  unfold shapeOneCosineRate
  linarith only [hquot]

/-- At bandwidth four thirds, the shape-one diagonal leaves margin `79/1250` above `3/4`. -/
theorem shapeOneCosineRate_fourThirds :
    3 / 4 + 79 / 1250 ≤ shapeOneCosineRate (4 / 3) := by
  have h := shapeOneCosineRate_ge_box (4 / 3) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The actual normalized first lag moment of the frozen cosine window. -/
def cosineWindowJ (P : Params) (κ T : ℝ) : ℝ :=
  2 / P.L T ^ 3 * ∫ y in (0 : ℝ)..(P.L T), (cosineParams P κ T).g T y * y

/-- Finite-height diagonal rate from the actual window mass, fourth moment, and lag moment. -/
def cosineWindowRate (P : Params) (κ T : ℝ) : ℝ :=
  2 - ((cosineParams P κ T).b T + P.lam1 T ^ 2 * cosineWindowJ P κ T) /
    (P.lam1 T * (cosineParams P κ T).a T ^ 2)

private theorem cosineWindow_a_tendsto {P : Params} (hϱ : TaperProfile P.ϱ)
    (hlam : 0 < P.lam) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hw : 1 ≤ P.w) :
    Tendsto (fun T => (cosineParams P κ T).a T) atTop (𝓝 (aStar κ)) := by
  apply tendsto_of_close (P := P) hlam (C := 4)
  filter_upwards [(Assembly.tendsto_L_atTop P hlam).eventually_ge_atTop (8 * P.w)] with T hT
  unfold Params.a
  rw [cosineParams_phi (by linarith : P.w ≠ 0)]
  exact aD_close hϱ hκ hκ1 hw hT

private theorem cosineWindow_b_tendsto {P : Params} (hϱ : TaperProfile P.ϱ)
    (hlam : 0 < P.lam) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hw : 1 ≤ P.w) :
    Tendsto (fun T => (cosineParams P κ T).b T) atTop (𝓝 (bStar κ)) := by
  apply tendsto_of_close (P := P) hlam (C := 4)
  filter_upwards [(Assembly.tendsto_L_atTop P hlam).eventually_ge_atTop (8 * P.w)] with T hT
  unfold Params.b
  rw [cosineParams_phi (by linarith : P.w ≠ 0)]
  exact bD_close hϱ hκ hκ1 hw hT

private theorem cosineWindow_J_tendsto {P : Params} (hϱ : TaperProfile P.ϱ)
    (hlam : 0 < P.lam) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hw : 1 ≤ P.w) :
    Tendsto (cosineWindowJ P κ) atTop (𝓝 (jStar κ)) := by
  apply tendsto_of_close (P := P) hlam (C := 16)
  filter_upwards [(Assembly.tendsto_L_atTop P hlam).eventually_ge_atTop (8 * P.w)] with T hT
  unfold cosineWindowJ Params.g
  rw [cosineParams_phi (by linarith : P.w ≠ 0)]
  exact jD_close hϱ hκ hκ1 hw hT

/-- The literal tapered-window coefficient converges with shape and bandwidth independent. -/
theorem cosineWindowRate_tendsto {P : Params} (hϱ : TaperProfile P.ϱ)
    (hlam : 0 < P.lam) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hw : 1 ≤ P.w) :
    Tendsto (cosineWindowRate P κ) atTop
      (𝓝 (2 - (bStar κ + P.lam ^ 2 * jStar κ) / (P.lam * aStar κ ^ 2))) := by
  have ha := cosineWindow_a_tendsto hϱ hlam hκ hκ1 hw
  have hb := cosineWindow_b_tendsto hϱ hlam hκ hκ1 hw
  have hJ := cosineWindow_J_tendsto hϱ hlam hκ hκ1 hw
  have hl := tendsto_lam1 hlam
  have hnum := hb.add ((hl.pow 2).mul hJ)
  have hden := hl.mul (ha.pow 2)
  have hap : 0 < aStar κ := lt_of_lt_of_le (by norm_num) (aStar_bounds hκ.le hκ1).1
  exact tendsto_const_nhds.sub (hnum.div hden (mul_pos hlam (sq_pos_of_pos hap)).ne')

/-- The canonical cosine window at bandwidth four thirds has the matched limiting rate. -/
theorem cosineWindowRate_fourThirds_tendsto :
    Tendsto (cosineWindowRate (paramsOf stdProfile (4 / 3)) 1) atTop
      (𝓝 (shapeOneCosineRate (4 / 3))) :=
  cosineWindowRate_tendsto taperProfile_stdProfile (by norm_num [paramsOf])
    (by norm_num) le_rfl (by norm_num [paramsOf])

/-- Every smaller margin than `79/1250` holds eventually for the actual finite-height coefficient. -/
theorem cosineWindowRate_fourThirds_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop, 3 / 4 + 79 / 1250 - ε ≤
      cosineWindowRate (paramsOf stdProfile (4 / 3)) 1 T := by
  exact cosineWindowRate_fourThirds_tendsto.eventually
    (eventually_ge_nhds (by linarith only [shapeOneCosineRate_fourThirds, hε]))

end GaloisForLFunctions.IncommensurableGaborPinching
