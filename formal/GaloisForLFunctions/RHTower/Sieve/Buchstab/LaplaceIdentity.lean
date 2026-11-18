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
    · simp only [Set.indicator_of_mem (show t ∈ Ioi (1:ℝ) from ht),
        Set.indicator_of_mem (show t + -1 ∈ Ioi (0:ℝ) from by change 0 < t + -1; linarith),
        sub_eq_add_neg]
    · simp only [Set.indicator_of_notMem (show t ∉ Ioi (1:ℝ) from ht),
        Set.indicator_of_notMem (show t + -1 ∉ Ioi (0:ℝ) from by change ¬0 < t + -1; linarith)]

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
    simp [buchstab,not_le.mpr ht.2]
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
    ring
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

private theorem factorial_exp_bound (a : ℝ) (n : ℕ) :
    1 / (n.factorial : ℝ) ≤ Real.exp (Real.exp a) * Real.exp (-a*n) := by
  have hs := NormedSpace.expSeries_div_hasSum_exp (Real.exp a)
  have h := hs.summable.le_tsum n (fun j _ => div_nonneg
    (pow_nonneg (Real.exp_pos a).le j) (Nat.cast_nonneg _))
  rw [hs.tsum_eq,← Real.exp_eq_exp_ℝ,← Real.exp_nat_mul] at h
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-a*n)).le
  have he : Real.exp ((n:ℝ)*a) * Real.exp (-a*n) = 1 := by
    rw [← Real.exp_add,show (n:ℝ)*a+-a*n = 0 by ring,Real.exp_zero]
  simpa only [div_mul_eq_mul_div,he] using hh

/-- The error in the real profile decays faster than each prescribed
exponential, with a uniform constant valid down to the cutoff. -/
theorem buchstab_exp_error (a : Ici (0:ℝ)) (u : Ici (1:ℝ)) :
    |buchstab u.val-enclosureLimit| ≤ Real.exp (Real.exp a.val)*Real.exp (-a.val*u.val) := by
  let n := ⌊u.val-1⌋₊+2
  have hu : u.val ≤ (n:ℝ) := by
    have h := Nat.lt_floor_add_one (u.val-1)
    dsimp [n]
    push_cast
    linarith
  exact (buchstab_factorial_error u).trans ((factorial_exp_bound a n).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hu (neg_nonpos.mpr a.property)))
      (Real.exp_pos _).le))

/-- Subtracting the limiting density leaves finite Laplace mass even with
an exponentially growing weight. -/
theorem integrable_buchstab_correction (z : ℝ) :
    IntegrableOn (fun t => (buchstab t-enclosureLimit)*Real.exp (z*t)) (Ioi (0:ℝ)) := by
  let a := |z|+1
  let M := Real.exp (Real.exp a)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h₀ : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0
  refine (h₀.const_mul M).mono' (((measurable_buchstab.sub measurable_const).mul
    (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with t ht
  have hc : |buchstab t-enclosureLimit| ≤ M*Real.exp (-a*t) := by
    by_cases hu : 1 ≤ t
    · exact buchstab_exp_error ⟨a,ha⟩ ⟨t,hu⟩
    · have hC := enclosureLimit_mem 0
      change 1/2 ≤ enclosureLimit ∧ enclosureLimit ≤ 1 at hC
      have hpos : 0 ≤ Real.exp a - a*t := by
        have h := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hu)) ha
        linarith [Real.add_one_le_exp a]
      rw [buchstab,if_neg hu,zero_sub,abs_neg,abs_of_nonneg (by linarith : 0 ≤ enclosureLimit)]
      apply hC.2.trans
      change 1 ≤ Real.exp (Real.exp a) * Real.exp (-a*t)
      rw [← Real.exp_add,Real.one_le_exp_iff]
      linarith
  have he : -a*t + z*t ≤ -t := by
    have hz : z ≤ |z| := le_abs_self _
    dsimp [a]
    nlinarith only [mul_le_mul_of_nonneg_right hz (le_of_lt ht)]
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ M*Real.exp (-a*t)*Real.exp (z*t) := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = M*Real.exp (-a*t+z*t) := by rw [Real.exp_add,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Real.exp_pos _).le

/-- The finite part of the transform is the ordinary signed area left
after subtracting the limiting density on the full positive ray. -/
theorem integral_buchstab_correction :
    (∫ t in Ioi (0:ℝ), buchstab t-enclosureLimit) = enclosureLimit - 1 := by
  have hc : IntegrableOn (fun t => buchstab t-enclosureLimit) (Ioi (0:ℝ)) := by
    simpa using integrable_buchstab_correction 0
  let f := fun (s t : ℝ) => (buchstab t-enclosureLimit)*Real.exp (-s*t)
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0:ℝ)))
    (l := 𝓝[>] (0:ℝ)) (F := f) (f := fun t => buchstab t-enclosureLimit)
    (fun t => |buchstab t-enclosureLimit|)
    (Eventually.of_forall fun s => ((measurable_buchstab.sub measurable_const).mul
      (by fun_prop)).aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with t ht
      change |(buchstab t-enclosureLimit)*Real.exp (-s*t)| ≤ _
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hs)) (le_of_lt ht))))
    hc.abs
    (Eventually.of_forall fun t => by
      have ht : Continuous (fun s : ℝ => (buchstab t-enclosureLimit)*Real.exp (-s*t)) := by fun_prop
      simpa [f] using (ht.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ))))
  apply tendsto_nhds_unique h
  rw [enclosureLimit_eq_exp_neg_euler]
  refine tendsto_transform_finitePart.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hp : 0 < s := hs
  have he : (∫ t in Ioi (0:ℝ), Real.exp (-s*t)) = s⁻¹ := by
    rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hp) 0]
    simp
  dsimp only [f]
  simp_rw [sub_mul]
  rw [integral_sub (laplace_integrable hp) ((integrableOn_exp_mul_Ioi
      (neg_lt_zero.mpr hp) 0).const_mul enclosureLimit),integral_const_mul,he]
  change _ = laplaceMass s - enclosureLimit * s⁻¹
  rw [laplaceMass_eq_transform ⟨s,hp⟩,enclosureLimit_eq_exp_neg_euler,div_eq_mul_inv]

#print axioms laplace_first_moment
#print axioms laplaceMass_eq_transform
#print axioms enclosureLimit_eq_exp_neg_euler
#print axioms buchstab_euler_error
#print axioms buchstab_exp_error
#print axioms integrable_buchstab_correction
#print axioms integral_buchstab_correction

end
end RHTower.Sieve.Buchstab
