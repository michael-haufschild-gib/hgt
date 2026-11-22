import GaloisForLFunctions.HTGeometry.FiniteTorusPhaseEnsembleLaw
import GaloisForLFunctions.HTGeometry.AnalyticNullPreimage

/-! # Character cancellation over a shrinking field interval at a fixed date -/
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
noncomputable section

/-- The weighted character integral with weight a′ is an endpoint difference.
Freezing this weight at d leaves an error bounded by the variation of a′. -/
private theorem frozen_derivative_bound (a : ℝ→ℝ) {b w T d δ : ℝ} (hw : 0<w) (hT : 0<T)
    (ha : ∀ z ∈ Icc b (b+w), AnalyticAt ℝ a z)
    (hδ : ∀ z ∈ Icc b (b+w), |d-deriv a z| ≤ δ) :
    |d| * ‖∫ s in (0:ℝ)..1, Complex.exp (Complex.I*((T*a (b+w*s):ℝ):ℂ))‖ ≤ δ+2/(T*w) := by
  let z (s : ℝ) := b+w*s
  let F (s : ℝ) := Complex.exp (Complex.I*((T*a (z s):ℝ):ℂ))
  let L := Complex.I*((T*w:ℝ):ℂ)
  let D (s : ℝ) := ((deriv a (z s):ℝ):ℂ)
  have hz (s : ℝ) (hs : s∈uIcc (0:ℝ) 1) : z s∈Icc b (b+w) := by
    rw [uIcc_of_le zero_le_one] at hs
    exact ⟨le_add_of_nonneg_right (mul_nonneg hw.le hs.1),
      add_le_add_right (mul_le_of_le_one_right hw.le hs.2) b⟩
  have hzd (s : ℝ) : HasDerivAt z w s := by
    simpa only [z,id_eq,mul_one] using ((hasDerivAt_id s).const_mul w).const_add b
  have hF (s : ℝ) (hs : s∈uIcc (0:ℝ) 1) : HasDerivAt F (F s*(L*D s)) s := by
    have h := (((ha _ (hz s hs)).differentiableAt.hasDerivAt.comp s (hzd s)).const_mul T).ofReal_comp
    convert (h.const_mul Complex.I).cexp using 1 <;>
      simp only [F,L,D,Function.comp_apply,Complex.ofReal_mul] <;> ring
  have hFc : ContinuousOn F (uIcc (0:ℝ) 1) := fun s hs => (hF s hs).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (uIcc (0:ℝ) 1) := fun s hs =>
    (Complex.continuous_ofReal.continuousAt.comp
      ((ha _ (hz s hs)).deriv.continuousAt.comp (hzd s).continuousAt)).continuousWithinAt
  have hn (s : ℝ) : ‖F s‖=1 := by
    dsimp only [F]
    rw [mul_comm]
    apply Complex.norm_exp_ofReal_mul_I
  have hL : L≠0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hT hw).ne')
  have hprim (s : ℝ) (hs : s∈uIcc (0:ℝ) 1) : HasDerivAt (fun t => F t/L) (D s*F s) s := by
    have h := (hF s hs).div_const L
    rw [show F s*(L*D s)/L=D s*F s by field_simp [hL]] at h
    exact h
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hprim (hDc.mul hFc).intervalIntegrable
  have hEnd : ‖∫ s in (0:ℝ)..1, D s*F s‖ ≤ 2/(T*w) := by
    rw [hFTC,←sub_div,norm_div]
    have hLn : ‖L‖=T*w := by
      change ‖Complex.I*((T*w:ℝ):ℂ)‖=_
      rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (mul_pos hT hw)]
    rw [hLn]
    exact div_le_div_of_nonneg_right ((norm_sub_le _ _).trans_eq (by rw [hn,hn]; norm_num)) (mul_pos hT hw).le
  have hrest : ‖∫ s in (0:ℝ)..1, ((d:ℂ)-D s)*F s‖ ≤ δ := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1) (C:=δ)
      (f:=fun s => ((d:ℂ)-D s)*F s) fun s hs => by
        rw [norm_mul,hn,mul_one,show (d:ℂ)-D s=((d-deriv a (z s):ℝ):ℂ) by push_cast; rfl,
          Complex.norm_real,Real.norm_eq_abs]
        exact hδ _ (hz s (uIoc_subset_uIcc hs))
    simpa only [sub_zero,abs_one,mul_one] using h
  have he : (d:ℂ)*(∫ s in (0:ℝ)..1, F s) =
      (∫ s in (0:ℝ)..1, ((d:ℂ)-D s)*F s)+(∫ s in (0:ℝ)..1, D s*F s) := by
    rw [←intervalIntegral.integral_add (f := fun s => ((d:ℂ)-D s)*F s) (g := fun s => D s*F s)
      ((continuousOn_const.sub hDc).mul hFc).intervalIntegrable
      (hDc.mul hFc).intervalIntegrable,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  change |d| * ‖∫ s in (0:ℝ)..1, F s‖ ≤ _
  rw [←Real.norm_eq_abs,←Complex.norm_real,←norm_mul,he]
  exact (norm_add_le _ _).trans (add_le_add hrest hEnd)

/-- An analytic action with nonzero slope loses its nontrivial character at a
prescribed laboratory date throughout the regime w→0, Tw→∞. -/
theorem shrinking_field_character {a : ℝ→ℝ} {b : ℝ} (ha : AnalyticAt ℝ a b) (hd : deriv a b≠0)
    {w T : ℕ→ℝ} (hw : Tendsto w atTop (𝓝 0)) (hp : ∀ᶠ n in atTop, 0<w n)
    (hTw : Tendsto (fun n => T n*w n) atTop atTop) :
    Tendsto (fun n => ∫ s in (0:ℝ)..1,
      Complex.exp (Complex.I*((T n*a (b+w n*s):ℝ):ℂ))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let d := deriv a b
  let δ := |d| * ε/2
  have hd' : 0 < |d| := abs_pos.mpr hd
  have hδ : 0<δ := half_pos (mul_pos hd' hε)
  have hnear : ∀ᶠ z in 𝓝 b, AnalyticAt ℝ a z ∧ |d-deriv a z| ≤ δ := by
    filter_upwards [ha.eventually_analyticAt,ha.deriv.continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds d hδ)] with z hz he
    exact ⟨hz,by simpa only [Metric.mem_ball,Real.dist_eq,abs_sub_comm] using (Metric.mem_ball.mp he).le⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have ht := ((tendsto_const_nhds (x:=(2:ℝ))).mul (tendsto_inv_atTop_zero.comp hTw))
  rw [mul_zero] at ht
  filter_upwards [hp,hw.eventually_lt_const hr,ht.eventually_lt_const hδ,hTw.eventually_gt_atTop 0] with n hn hn' hsmall hpos
  have hz (z : ℝ) (h : z∈Icc b (b+w n)) : z∈Metric.ball b r := by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr h.1)]
    linarith only [h.2,hn']
  have he := frozen_derivative_bound a hn ((mul_pos_iff_of_pos_right hn).mp hpos)
    (fun z h => (hball (hz z h)).1) (fun z h => (hball (hz z h)).2)
  rw [dist_zero_right]
  apply (lt_of_mul_lt_mul_left (a:=|d|) _ hd'.le)
  change 2*(T n*w n)⁻¹<δ at hsmall
  rw [←div_eq_mul_inv] at hsmall
  linarith only [he,hsmall,show δ=|d| * ε/2 from rfl]

#print axioms shrinking_field_character
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
