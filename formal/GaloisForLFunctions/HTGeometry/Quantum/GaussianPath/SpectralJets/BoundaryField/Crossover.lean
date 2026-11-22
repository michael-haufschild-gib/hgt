import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.ProjectiveSlopes
import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity
import GaloisForLFunctions.HTGeometry.ArithmeticWindowPhase

/-! # Joint phase mixing at the inverse terminal-field scale -/
open Filter Topology MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section

/-- In a positive observation window the magnitude of a character is bounded by
two divided by the total change of its argument. -/
private theorem clock_character_bound {I : Type} [Fintype I] (m : I→ℤ) (f : I→ℝ)
    {T : ℝ} (hT : 0<T) (ha : finiteTorusCharacterDetuning m f≠0) :
    ‖∫ x, UnitAddTorus.mFourier m x ∂(clockPhaseWindowLaw f T : Measure _)‖ ≤
      2/(T*|finiteTorusCharacterDetuning m f|) := by
  let a := finiteTorusCharacterDetuning m f
  rw [integral_clockPhaseWindowLaw f hT,windowAverage,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hT]
  simp_rw [mFourier_finiteClockPhasePoint_expChar,expChar]
  have h (s : ℝ) : (((a*s:ℝ):ℂ)*Complex.I)=(s:ℂ)*(a:ℂ)*Complex.I := by push_cast; ring
  change T⁻¹*‖∫ s in (0:ℝ)..T, Complex.exp (((a*s:ℝ):ℂ)*Complex.I)‖≤2/(T*|a|)
  simp_rw [h]
  calc _ ≤ T⁻¹*(2/|a|) := mul_le_mul_of_nonneg_left
         (by simpa only [zero_add] using norm_integral_exp_window_le ha 0 T) (inv_nonneg.mpr hT.le)
       _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring

/-- If the frequency vanishes simply, the observation resolves it once
the time multiplied by the displacement tends to infinity. -/
private theorem scaled_action {a : ℝ→ℝ} {b v : ℝ} (ha : HasDerivAt a v b)
    (hs : a b=0 → v≠0) {T w : ℕ→ℝ} (hT : Tendsto T atTop atTop)
    (hw : Tendsto w atTop (𝓝 b)) (hwT : Tendsto (fun n => T n*|w n-b|) atTop atTop) :
    Tendsto (fun n => T n*|a (w n)|) atTop atTop := by
  by_cases h0 : a b=0
  · have hne : ∀ᶠ n in atTop, w n≠b := by
      filter_upwards [hwT.eventually_gt_atTop 0] with n hn h
      simp [h] at hn
    have hw' : Tendsto w atTop (𝓝[≠] b) := tendsto_nhdsWithin_iff.mpr ⟨hw,hne⟩
    have hr := ((hasDerivAt_iff_tendsto_slope.mp ha).comp hw').abs
    have hh := hwT.atTop_mul_pos (abs_pos.mpr (hs h0)) hr
    apply hh.congr'
    filter_upwards [hne] with n hn
    rw [Function.comp_apply,slope_def_field,h0,sub_zero,abs_div]
    field_simp [abs_ne_zero.mpr (sub_ne_zero.mpr hn)]
  · exact hT.atTop_mul_pos (abs_pos.mpr h0) ((ha.continuousAt.tendsto.comp hw).abs)

/-- For two spectra that coincide at the baseline, every surviving
resonance is broken to first order if the frequency derivatives are
rationally independent. This suffices even when quadratic terms accumulate
an unbounded phase. -/
private theorem moving_clock_haar {I : Type} [Fintype I] {f : ℝ→I→ℝ} {b : ℝ} {v : I→ℝ}
    (hd : ∀ i, HasDerivAt (fun t => f t i) (v i) b)
    (hf : RationallyIndependentFrequency (f b)) (hv : RationallyIndependentFrequency v)
    {T w : ℕ→ℝ} (hT : Tendsto T atTop atTop) (hw : Tendsto w atTop (𝓝 b))
    (hwT : Tendsto (fun n => T n*|w n-b|) atTop atTop) :
    Tendsto (fun n => clockPhaseWindowLaw (Sum.elim (f b) (f (w n))) (T n)) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure (I⊕I))) := by
  classical
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro m
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  by_cases hm : m=0
  · subst m
    simp [UnitAddTorus.mFourier_zero]
  rw [if_neg hm,tendsto_zero_iff_norm_tendsto_zero]
  let p (i : I) := m (.inl i)
  let q (i : I) := m (.inr i)
  let a (z : ℝ) := finiteTorusCharacterDetuning m (Sum.elim (f b) (f z))
  have he (z : ℝ) : a z=finiteTorusCharacterDetuning p (f b)+finiteTorusCharacterDetuning q (f z) := by
    simp only [a,finiteTorusCharacterDetuning,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,p,q]
  have had : HasDerivAt a (finiteTorusCharacterDetuning q v) b := by
    simp_rw [funext he,finiteTorusCharacterDetuning]
    exact (HasDerivAt.fun_sum fun i _ => (hd i).const_mul (q i:ℝ)).const_add _
  have hs (hz : a b=0) : finiteTorusCharacterDetuning q v≠0 := by
    intro hq
    have hq0 := hv q hq
    rw [he,hq0] at hz
    simp only [finiteTorusCharacterDetuning,Pi.zero_apply,Int.cast_zero,zero_mul,
      Finset.sum_const_zero,add_zero] at hz
    have hp0 := hf p hz
    apply hm
    funext j
    cases j with
    | inl i => exact congrFun hp0 i
    | inr i => exact congrFun hq0 i
  have hprod := scaled_action had hs hT hw hwT
  refine squeeze_zero' (g := fun n => 2*(T n*|a (w n)|)⁻¹) (.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [hT.eventually_gt_atTop 0,hprod.eventually_gt_atTop 0] with n ht hn
    have hne : a (w n)≠0 := by intro h; simp [h] at hn
    exact (clock_character_bound m _ ht hne).trans_eq (div_eq_mul_inv _ _)
  · simpa only [Function.comp_apply,mul_zero] using (tendsto_const_nhds (x:=(2:ℝ))).mul (tendsto_inv_atTop_zero.comp hprod)

/-- For each Gaussian prefix and all but countably many baselines, vanishing
terminal-field displacements give independent Haar phase registers throughout
the regime T|h|→∞, in the same positive laboratory window. -/
theorem gaussian_boundary_inverse_field_haar :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ B : Set ℝ, B.Countable ∧ ∀ b ∉ B,
      let E := orderedBoundaryEnergy ω k
      ∀ (r : Fin (k+3)→Bool) (T w : ℕ→ℝ), Tendsto T atTop atTop → Tendsto w atTop (𝓝 b) →
        Tendsto (fun n => T n*|w n-b|) atTop atTop →
        let f := fun z => projectiveFrequency (fun i => -E z i) r
        Tendsto (fun n => clockPhaseWindowLaw (Sum.elim (f b) (f (w n))) (T n)) atTop
          (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
  filter_upwards [gaussian_boundary_projective_slopes] with ω hω
  intro k
  obtain ⟨B,hB,hh⟩ := hω k
  refine ⟨B,hB,?_⟩
  intro b hb E r T w hT hw hwT f
  obtain ⟨hE,ha,hv⟩ := hh b hb
  let v := fun i => deriv (fun z => E z i) b
  apply moving_clock_haar (v:=projectiveFrequency (fun i => -v i) r) _
    (maximallyProjectiveEnergy_projectiveFrequency_independent _ (maximallyProjectiveEnergy_neg hE) r)
    (maximallyProjectiveEnergy_projectiveFrequency_independent _ (maximallyProjectiveEnergy_neg hv) r) hT hw hwT
  intro i
  exact (ha i.val).differentiableAt.hasDerivAt.neg.sub (ha r).differentiableAt.hasDerivAt.neg

#print axioms gaussian_boundary_inverse_field_haar
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
