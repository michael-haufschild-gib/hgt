import GaloisForLFunctions.ExceptionalLayerTheory.TheLogarithmicCorrectionToGaussianObservation

/-!
# Comparing two Gaussian Mellin modes at high observation height

For two marked complex points the log magnitude ratio has a horizontal
term proportional to the difference of their real parts and a vertical
term π times their ordinate difference divided by four. The horizontal
term uses the shifted damping L + log(t/2). On a common vertical line
damping cancels exactly and distinct ordinates prevent cancellation of
the two complex modes at all sufficiently large heights.
-/

noncomputable section
open Complex Filter Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Horizontal and vertical contributions to the logarithmic mode ratio. -/
def gaussianPairLogRatio (ρ η : ℂ) (L t : ℝ) : ℝ :=
  (ρ.re-η.re)*(L+Real.log (t/2))/2+Real.pi*(ρ.im-η.im)/4

theorem gaussian_mode_eventually_positive (ρ : ℂ) (σ : ℝ) (L : ℝ → ℝ) :
    ∀ᶠ t : ℝ in atTop, 0<gaussianModeNorm ρ σ (L t) t := by
  have hc : 0<Real.sqrt (2*Real.pi)/2 := by positivity
  filter_upwards [(gaussian_mode_relative_asymptotic ρ σ L).eventually_const_lt hc] with t ht
  exact (div_pos_iff_of_pos_right (Real.exp_pos _)).mp ht

private theorem log_remainder (ρ : ℂ) (σ : ℝ) (L : ℝ → ℝ) :
    Tendsto (fun t => Real.log (gaussianModeNorm ρ σ (L t) t)-gaussianLogExcess ρ σ (L t) t)
      atTop (𝓝 (Real.log (Real.sqrt (2*Real.pi)/2))) := by
  have hc : 0<Real.sqrt (2*Real.pi)/2 := by positivity
  apply ((Real.continuousAt_log hc.ne').tendsto.comp (gaussian_mode_relative_asymptotic ρ σ L)).congr'
  filter_upwards [gaussian_mode_eventually_positive ρ σ L] with t ht
  exact (Real.log_div ht.ne' (Real.exp_ne_zero _)).trans (by rw [Real.log_exp])

private theorem shifted_log_height (b : ℝ) :
    Tendsto (fun t : ℝ => Real.log ((t-b)/2)-Real.log (t/2)) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x:=(1:ℝ))).sub
    ((tendsto_const_nhds (x:=b)).div_atTop (tendsto_id (α:=ℝ)))
  rw [sub_zero] at h
  have hl := (Real.continuousAt_log one_ne_zero).tendsto.comp h
  rw [Real.log_one] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_gt_atTop b] with t ht htb
  have hp : 0<(t-b)/2 := div_pos (sub_pos.mpr htb) (by norm_num)
  rw [←Real.log_div hp.ne' (div_pos ht (by norm_num : (0:ℝ)<2)).ne']
  change Real.log (1-b/t)=_
  congr 1
  field_simp [ht.ne']
  <;> ring

/-- The difference from the predicted log ratio tends to zero for
every damping schedule, including oscillating schedules. -/
theorem gaussian_pair_log_asymptotic (ρ η : ℂ) (σ : ℝ) (L : ℝ → ℝ) :
    Tendsto (fun t => Real.log (gaussianModeNorm ρ σ (L t) t)-
      Real.log (gaussianModeNorm η σ (L t) t)-gaussianPairLogRatio ρ η (L t) t)
      atTop (𝓝 0) := by
  have h := (((log_remainder ρ σ L).sub (log_remainder η σ L)).add
    ((shifted_log_height ρ.im).const_mul ((ρ.re-σ-1)/2))).sub
      ((shifted_log_height η.im).const_mul ((η.re-σ-1)/2))
  simp only [sub_self,mul_zero,add_zero,sub_zero] at h
  apply h.congr
  intro t
  unfold gaussianPairLogRatio gaussianLogExcess
  change (Real.log _-((ρ.re-σ)*L t-Real.pi*((t-ρ.im)/2)+(ρ.re-σ-1)*Real.log ((t-ρ.im)/2))/2-
    (Real.log _-((η.re-σ)*L t-Real.pi*((t-η.im)/2)+(η.re-σ-1)*Real.log ((t-η.im)/2))/2)+_) - _ = _
  ring

/-- Exact removal of damping on one vertical line, at every height
including totalized zero denominators. -/
theorem equal_real_gaussian_ratio_damping {ρ η : ℂ} (he : ρ.re=η.re) (σ L t : ℝ) :
    gaussianModeNorm ρ σ L t/gaussianModeNorm η σ L t =
      gaussianModeNorm ρ σ 0 t/gaussianModeNorm η σ 0 t := by
  rw [gaussian_mode_damping_factor ρ σ L,gaussian_mode_damping_factor η σ L,he,
    mul_div_mul_right _ _ (Real.exp_ne_zero _)]

/-- On one vertical line the ordinate difference alone specifies the
limiting ratio, for arbitrary and even adaptive damping. -/
theorem equal_real_gaussian_ratio_limit {ρ η : ℂ} (he : ρ.re=η.re) (σ : ℝ) (L : ℝ → ℝ) :
    Tendsto (fun t => gaussianModeNorm ρ σ (L t) t/gaussianModeNorm η σ (L t) t)
      atTop (𝓝 (Real.exp (Real.pi*(ρ.im-η.im)/4))) := by
  have h := (gaussian_pair_log_asymptotic ρ η σ L).add_const (Real.pi*(ρ.im-η.im)/4)
  simp only [gaussianPairLogRatio,he,sub_self,zero_mul,zero_div,zero_add,sub_add_cancel] at h
  apply h.rexp.congr'
  filter_upwards [gaussian_mode_eventually_positive ρ σ L,gaussian_mode_eventually_positive η σ L] with t hρ hη
  exact (Real.exp_sub ..).trans (by rw [Real.exp_log hρ,Real.exp_log hη])

/-- For two different ordinates at equal real part, a fixed positive
fraction of the upper mode survives any relative phase and damping.
Every fraction strictly below 1−exp(−π Δ/4) is eventually valid. -/
theorem distinct_ordinate_gaussian_modes_cannot_cancel {ρ η : ℂ} (he : ρ.re=η.re) (σ : ℝ)
    {k : ℝ} (hk : k<1-Real.exp (Real.pi*(η.im-ρ.im)/4)) :
    ∀ᶠ t : ℝ in atTop, ∀ L : ℝ, ∀ q : ℂ, ‖q‖=1 →
      k*gaussianModeNorm ρ σ L t <
        ‖gaussianMBKernel (Real.exp (-L)) (ρ-((σ:ℂ)+(t:ℂ)*I))+
          q*gaussianMBKernel (Real.exp (-L)) (η-((σ:ℂ)+(t:ℂ)*I))‖ := by
  have h := equal_real_gaussian_ratio_limit he.symm σ (fun _ => 0)
  filter_upwards [h.eventually_lt_const (by linarith only [hk] :
    Real.exp (Real.pi*(η.im-ρ.im)/4)<1-k),gaussian_mode_eventually_positive ρ σ (fun _ => 0)] with t ht hp L q hq
  have hpL : 0<gaussianModeNorm ρ σ L t := by
    rw [gaussian_mode_damping_factor ρ σ L t]
    exact mul_pos hp (Real.exp_pos _)
  rw [←equal_real_gaussian_ratio_damping he.symm σ L t] at ht
  have hsmall := (div_lt_iff₀ hpL).mp ht
  let F (z : ℂ) := gaussianMBKernel (Real.exp (-L)) (z-((σ:ℂ)+(t:ℂ)*I))
  have htri := norm_sub_le (F ρ+q*F η) (q*F η)
  rw [add_sub_cancel_right,norm_mul,hq,one_mul] at htri
  change k*‖F ρ‖ < ‖F ρ+q*F η‖
  change ‖F η‖ < (1-k)*‖F ρ‖ at hsmall
  linarith only [htri,hsmall]

#print axioms gaussian_pair_log_asymptotic
#print axioms equal_real_gaussian_ratio_limit
#print axioms distinct_ordinate_gaussian_modes_cannot_cancel
end GaloisForLFunctions.ExceptionalLayerTheory
