import GaloisForLFunctions.RHTower.Sieve.Buchstab.LaplaceMass
import GaloisForLFunctions.RHTower.Sieve.Buchstab.TransformAtZero

/-!
# The Buchstab Laplace identity and its limiting constant

The integrated delay equation turns the first Laplace moment into the
shifted transform. Its differential equation has a first integral given
by the prime retention quantile. Normalization at infinity identifies the
transform in Weingartner's Lemma 1 and the Abelian limit identifies the
constant in the real-variable factorial enclosures.
-/

namespace RHTower.Sieve.Buchstab
open Set MeasureTheory Filter Topology
noncomputable section

private def primitive (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, buchstab t

private theorem primitive_continuous : Continuous primitive :=
  intervalIntegral.continuous_primitive intervalIntegrable_buchstab 0

private theorem cut_at_one {f : ℝ → ℝ} (hz : ∀ t ∈ Ioo (0:ℝ) 1, f t = 0) :
    (∫ t in Ioi (0:ℝ), f t) = ∫ t in Ioi (1:ℝ), f t := by
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (Ioi_subset_Ioi zero_le_one)
  filter_upwards [volume.ae_ne (1:ℝ)] with t ht h
  exact hz t ⟨h.1,lt_of_le_of_ne (not_lt.mp h.2) ht⟩

private theorem shift_one (f : ℝ → ℝ) :
    (∫ t in Ioi (1:ℝ), f (t-1)) = ∫ t in Ioi (0:ℝ), f t := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self ((Ioi (0:ℝ)).indicator f) (-1)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    by_cases ht : 1 < t
    · rw [Set.indicator_of_mem ht,Set.indicator_of_mem (show 0 < t + -1 by linarith)]
      rfl
    · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem (show ¬0 < t + -1 by linarith)]

private theorem primitive_bounds {t : ℝ} (ht : 0 ≤ t) : primitive t ∈ Icc 0 t := by
  constructor
  · exact intervalIntegral.integral_nonneg ht fun x _ => (buchstab_mem_unit x).1
  · have h := intervalIntegral.integral_mono_on ht (intervalIntegrable_buchstab 0 t)
      (intervalIntegrable_const (c := (1:ℝ))) (fun x _ => (buchstab_mem_unit x).2)
    simpa [primitive] using h

private theorem primitive_integrable {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t => primitive t * Real.exp (-s*t)) (Ioi (0:ℝ)) := by
  refine (linearWeight_integrable hs).mono' (primitive_continuous.mul (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (primitive_bounds (le_of_lt ht)).1 (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right (primitive_bounds (le_of_lt ht)).2 (Real.exp_pos _).le

private theorem primitive_laplace (s : Ioi (0:ℝ)) :
    (∫ t in Ioi (0:ℝ), primitive t*Real.exp (-s.val*t)) = laplaceMass s / s.val := by
  have hs : 0 < s.val := s.property
  let g := fun t => primitive t*Real.exp (-s.val*t)
  let f := fun t => buchstab t*Real.exp (-s.val*t)
  have hg : IntegrableOn g (Ioi 1) := (primitive_integrable hs).mono_set (Ioi_subset_Ioi zero_le_one)
  have hf : IntegrableOn f (Ioi 1) := (laplace_integrable hs).mono_set (Ioi_subset_Ioi zero_le_one)
  have hd (t : ℝ) (ht : t ∈ Ioi 1) : HasDerivAt g (f t-s.val*g t) t := by
    have hc := (continuousOn_buchstab.mono Ioi_subset_Ici_self).continuousAt (Ioi_mem_nhds ht)
    have hp := intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_buchstab 0 t)
      measurable_buchstab.stronglyMeasurable.stronglyMeasurableAtFilter hc
    have he := ((hasDerivAt_id t).const_mul (-s.val)).exp
    exact (hp.mul he).congr_deriv (by dsimp [f,g,primitive]; ring)
  have hgi : IntegrableOn (fun t => f t-s.val*g t) (Ioi 1) := hf.sub (hg.const_mul _)
  have hl := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hd hgi hg
  have hc : Continuous g := primitive_continuous.mul (by fun_prop)
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousWithinAt hd hgi hl
  have hzero : g 1 = 0 := by
    dsimp [g,primitive]
    rw [integral_buchstab_initial ⟨zero_le_one,le_rfl⟩,zero_mul]
  rw [hzero,sub_zero,integral_sub hf (hg.const_mul _),integral_const_mul] at hh
  have hcF : laplaceMass s = ∫ t in Ioi (1:ℝ), f t := cut_at_one fun t ht => by
    simp [f,buchstab,not_le.mpr ht.2]
  rw [cut_at_one (f := g) (fun t ht => by simp [g,primitive,
    integral_buchstab_initial (show t ∈ Icc (0:ℝ) 1 from ⟨ht.1.le,ht.2.le⟩)]),hcF]
  apply (eq_div_iff hs.ne').mpr
  linarith only [hh, mul_comm (∫ t in Ioi (1:ℝ), g t) s.val]

/-- The first moment of the weighted profile satisfies an exact shift law. -/
theorem laplace_first_moment (s : Ioi (0:ℝ)) :
    (∫ t in Ioi (0:ℝ), t*buchstab t*Real.exp (-s.val*t)) =
      Real.exp (-s.val) * (1 + laplaceMass s) / s.val := by
  have hs : 0 < s.val := s.property
  let E := fun t : ℝ => Real.exp (-s.val*t)
  have hi : IntegrableOn (fun t => t*buchstab t*E t) (Ioi (0:ℝ)) := by
    refine (linearWeight_integrable hs).mono' (((measurable_id.mul measurable_buchstab).mul
      (by dsimp [E]; fun_prop)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with t ht
    have hb := buchstab_mem_unit t
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (le_of_lt ht) hb.1) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hb.2 (le_of_lt ht))
      (Real.exp_pos _).le
  have he : IntegrableOn E (Ioi 1) := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 1
  have hform (t : ℝ) (ht : 1 < t) : t*buchstab t*E t = E t + primitive (t-1)*E t := by
    rw [buchstab_weighted ⟨t,ht.le⟩,add_mul,one_mul]
    rfl
  have hshift : IntegrableOn (fun t => primitive (t-1)*E t) (Ioi 1) := by
    apply ((hi.mono_set (Ioi_subset_Ioi zero_le_one)).sub he).congr
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (1:ℝ)))] with t ht
    change t*buchstab t*E t-E t = _
    rw [hform t ht]
    ring
  rw [cut_at_one (fun t ht => by simp [buchstab, not_le.mpr ht.2])]
  change (∫ t in Ioi (1:ℝ), t*buchstab t*E t) = _
  rw [setIntegral_congr_fun measurableSet_Ioi hform,integral_add he hshift]
  have he1 : (∫ t in Ioi (1:ℝ), E t) = Real.exp (-s.val)/s.val := by
    change (∫ t in Ioi (1:ℝ), Real.exp (-s.val*t)) = _
    rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hs) 1]
    simp
  have hf (t : ℝ) : primitive (t-1)*E t = Real.exp (-s.val)*(primitive (t-1)*E (t-1)) := by
    have hx : E t = Real.exp (-s.val)*E (t-1) := by
      dsimp [E]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hx]
    ring
  rw [he1, show (fun t => primitive (t-1)*E t) =
    (fun t => Real.exp (-s.val)*(primitive (t-1)*E (t-1))) by funext t; exact hf t,
    integral_const_mul,shift_one (fun t => primitive t*E t),primitive_laplace]
  ring

/-- The positive-ray transform of Buchstab's function is exactly `exp(E₁(s))-1`. -/
theorem laplaceMass_eq_transform (s : Ioi (0:ℝ)) : laplaceMass s = transform s := by
  let H := fun x => (1+laplaceMass x)*apertureExtension x
  have hd (x : ℝ) (hx : 0 < x) : HasDerivAt H 0 x := by
    have h := hasDerivAt_laplaceMass ⟨x,hx⟩
    rw [integral_neg,laplace_first_moment ⟨x,hx⟩] at h
    apply ((h.const_add 1).mul (hasDerivAt_apertureExtension x)).congr_deriv
    dsimp [apertureExtension,apertureDensity]
    field_simp [hx.ne',show regular x ≠ 0 from (Real.exp_pos _).ne']
    <;> ring
  obtain ⟨c,hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) (fun x hx => (hd x hx).deriv)
  have hL : Tendsto H atTop (𝓝 1) := by
    have he : Tendsto apertureExtension atTop (𝓝 1) := tendsto_retentionQuantile_atTop.congr'
      (by filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; exact (apertureExtension_eq_retention ⟨x,hx⟩).symm)
    simpa [H] using (tendsto_laplaceMass_atTop.const_add 1).mul he
  have hc1 : c = 1 := tendsto_nhds_unique tendsto_const_nhds (hL.congr'
    (by filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; exact hc x hx))
  have h := hc s s.property
  change (1+laplaceMass s)*apertureExtension s = c at h
  rw [apertureExtension_eq_retention, hc1] at h
  have h' := retention_mul_transform s
  rw [mul_comm] at h'
  exact add_left_cancel (mul_right_cancel₀ (retentionQuantile_pos _).ne' (h.trans h'.symm))

/-- The common real-cell limit is the residue of the explicit transform. -/
theorem enclosureLimit_eq_exp_neg_euler : enclosureLimit = Real.exp (-Real.eulerMascheroniConstant) := by
  apply tendsto_nhds_unique tendsto_scaled_laplaceMass
  refine tendsto_mul_transform_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [laplaceMass_eq_transform ⟨s,hs⟩]

/-- Uniform factorial error about the identified Euler–Mascheroni limit. -/
theorem buchstab_euler_error (u : Ici (1:ℝ)) :
    |buchstab u.val - Real.exp (-Real.eulerMascheroniConstant)| ≤ 1 / ((⌊u.val-1⌋₊+2).factorial : ℝ) := by
  rw [← enclosureLimit_eq_exp_neg_euler]
  exact buchstab_factorial_error u

#print axioms laplace_first_moment
#print axioms laplaceMass_eq_transform
#print axioms enclosureLimit_eq_exp_neg_euler
#print axioms buchstab_euler_error

end
end RHTower.Sieve.Buchstab
