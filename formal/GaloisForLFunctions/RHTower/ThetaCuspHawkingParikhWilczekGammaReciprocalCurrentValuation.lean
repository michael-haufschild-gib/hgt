import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaReciprocalCutoffExpansion

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

/-- The complete original current in the normalization used by its finite cutoff expansion. -/
def pwGammaMobiusReciprocalNormalizedCurrent (z : ℂ) (v : ℝ) : ℂ :=
  (Real.exp (-v):ℂ)*(pwGammaMobiusSameSourceCurrent z v/pwGammaRaySource v)

private theorem pwGammaCurrent_first_moment_limit (z : ℂ) (j : ℕ)
    (hsmall : ∀ i<j, pwGammaMobiusReciprocalEndpointMoment z i=0) :
    Tendsto (fun x : ℝ => (x:ℂ)^j*pwGammaMobiusReciprocalNormalizedCurrent z (1/x))
      atTop (𝓝 (pwGammaMobiusReciprocalEndpointMoment z j)) := by
  obtain ⟨C,hC,hb⟩ := pwGammaMobiusReciprocalResponse_finite_asymptotic_bound z (j+1)
  have hzero : Tendsto (fun x : ℝ => C*(1/x)) atTop (𝓝 0) := by
    have hi : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := by
      simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
    simpa only [mul_zero] using hi.const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hzero
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx2
  have hx : 0<x := by linarith
  have hv : 0<1/x := by positivity
  have hvhalf : 1/x≤1/2 := (div_le_iff₀ hx).mpr (by linarith)
  have ht := hb (1/x) hv hvhalf
  have hs : (∑ i∈Finset.range (j+1), ((1/x:ℝ):ℂ)^i*
      pwGammaMobiusReciprocalEndpointMoment z i) =
      ((1/x:ℝ):ℂ)^j*pwGammaMobiusReciprocalEndpointMoment z j := by
    rw [Finset.sum_range_succ]
    have hh : (∑ i∈Finset.range j, ((1/x:ℝ):ℂ)^i*
        pwGammaMobiusReciprocalEndpointMoment z i)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hsmall i (Finset.mem_range.mp hi), mul_zero]
    rw [hh, zero_add]
  rw [hs] at ht
  change ‖pwGammaMobiusReciprocalNormalizedCurrent z (1/x)-
    ((1/x:ℝ):ℂ)^j*pwGammaMobiusReciprocalEndpointMoment z j‖≤_ at ht
  have hp : (x:ℂ)^j*((1/x:ℝ):ℂ)^j=1 := by
    rw [← mul_pow]
    push_cast
    rw [mul_one_div_cancel (Complex.ofReal_ne_zero.mpr hx.ne'), one_pow]
  have he : (x:ℂ)^j*pwGammaMobiusReciprocalNormalizedCurrent z (1/x)-
      pwGammaMobiusReciprocalEndpointMoment z j =
      (x:ℂ)^j*(pwGammaMobiusReciprocalNormalizedCurrent z (1/x)-
        ((1/x:ℝ):ℂ)^j*pwGammaMobiusReciprocalEndpointMoment z j) := by
    rw [mul_sub, ← mul_assoc, hp, one_mul]
  rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.le]
  calc
    _ ≤ x^j*(C*(1/x)^(j+1)) := mul_le_mul_of_nonneg_left ht (pow_pos hx j).le
    _ = C*(1/x) := by
      rw [div_pow, pow_succ]
      field_simp
      ring

/-- The complete original current has a finite first nonzero asymptotic moment at every parameter. -/
theorem pwGammaMobiusReciprocalNormalizedCurrent_exists_valuation (z : ℂ) :
    ∃ j : ℕ, pwGammaMobiusReciprocalEndpointMoment z j≠0 ∧
      (∀ i<j, pwGammaMobiusReciprocalEndpointMoment z i=0) ∧
      Tendsto (fun x : ℝ => (x:ℂ)^j*pwGammaMobiusReciprocalNormalizedCurrent z (1/x))
        atTop (𝓝 (pwGammaMobiusReciprocalEndpointMoment z j)) := by
  obtain ⟨k,hk⟩ := (pwGammaMobiusReciprocalMoment_eventually_ne_zero z).exists
  have hex : ∃ j, pwGammaMobiusReciprocalEndpointMoment z j≠0 :=
    ⟨k+2, by rw [pwGammaMobiusReciprocalEndpointMoment_detector_eq]; exact hk⟩
  let j := Nat.find hex
  have hj : pwGammaMobiusReciprocalEndpointMoment z j≠0 := Nat.find_spec hex
  have hsmall : ∀ i<j, pwGammaMobiusReciprocalEndpointMoment z i=0 := by
    intro i hi
    exact not_ne_iff.mp (Nat.find_min hex hi)
  exact ⟨j,hj,hsmall,pwGammaCurrent_first_moment_limit z j hsmall⟩

theorem pwGammaMobiusReciprocalNormalizedCurrent_not_flat (z : ℂ) :
    ¬(∀ k : ℕ, Tendsto
      (fun x : ℝ => (x:ℂ)^k*pwGammaMobiusReciprocalNormalizedCurrent z (1/x)) atTop (𝓝 0)) := by
  intro h
  obtain ⟨j,hj,_,ht⟩ := pwGammaMobiusReciprocalNormalizedCurrent_exists_valuation z
  exact hj (tendsto_nhds_unique ht (h j))

/-- The previously forced unit-ground correction cannot make any member a scalar mode. -/
theorem pwGammaMobiusSkewSource_no_corrected_scalar (z : ℂ) :
    ¬∃ lam : ℂ, ∀ x : ℝ, 0<x →
      pwGammaMobiusSkewSource z x+(2*Real.log x:ℝ)*pwGammaRaySource x=
        lam*(pwGammaMobiusTilt z x-pwGammaRaySource x) := by
  rintro ⟨lam,heq⟩
  apply pwGammaMobiusReciprocalNormalizedCurrent_not_flat z
  intro k
  have hg := pwGammaMobiusSkewSource_ground_current_flat_required z lam heq k
  have hi : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have he : Tendsto (fun x : ℝ => (Real.exp (-(1/x)):ℂ)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, neg_zero, Real.exp_zero, Complex.ofReal_one] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (Real.continuous_exp.continuousAt.tendsto.comp hi.neg)
  have ht := hg.mul he
  simp only [zero_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  unfold pwGammaRayInverseReflection pwGammaMobiusReciprocalNormalizedCurrent
  simp only [one_div]
  field_simp [pwGammaRaySource_ne_zero]

end
end RHTower
