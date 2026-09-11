import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaAdjointPairedContact

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

def pwGammaMobiusAdjointResponseKernel (z v : ℂ) (p : ℝ×ℝ) : ℂ :=
  (pwGammaReversibleDensity p.1:ℂ)*(pwGammaMobiusTilt v p.1/pwGammaRaySource p.1)*
    (starRingEnd ℂ) (pwGammaMobiusReciprocalResponse z (1/p.1) p.2)

theorem pwGammaMobiusTilt_measurable (z : ℂ) : Measurable (pwGammaMobiusTilt z) := by
  change Measurable (fun x => ∑' n, pwGammaMobiusGlobalAtom z n x)
  apply Measurable.tsum
  intro n
  unfold pwGammaMobiusGlobalAtom pwGammaRaySource GaloisForLFunctions.expShift
  fun_prop

theorem pwGammaMobiusAdjointResponseKernel_measurable (z v : ℂ) :
    Measurable (pwGammaMobiusAdjointResponseKernel z v) := by
  have hg (w : ℂ) : Measurable (fun x : ℝ => pwGammaMobiusTilt w x/pwGammaRaySource x) := by
    apply (pwGammaMobiusTilt_measurable w).div
    unfold pwGammaRaySource GaloisForLFunctions.expShift
    fun_prop
  have ht : Measurable (pwGammaMobiusReciprocalTail z) := by
    unfold pwGammaMobiusReciprocalTail
    exact (hg z |>.comp (by fun_prop : Measurable (fun x : ℝ => 1/x))).sub measurable_const
  unfold pwGammaMobiusAdjointResponseKernel pwGammaMobiusReciprocalResponse
  have hw : Measurable (fun p : ℝ×ℝ => (pwGammaReversibleDensity p.1:ℂ)) := by
    unfold pwGammaReversibleDensity
    fun_prop
  exact (hw.mul ((hg v).comp measurable_fst)).mul
    (Complex.continuous_conj.measurable.comp (((by fun_prop : Measurable (fun p : ℝ×ℝ =>
      (Real.exp (-p.2):ℂ))).mul
      ((ht.comp (by fun_prop : Measurable (fun p : ℝ×ℝ => 1/p.1+p.2))).sub
        (ht.comp (by fun_prop : Measurable (fun p : ℝ×ℝ => 1/p.1))))).div (by fun_prop)))

private theorem pwGammaResponse_density_bound (k : ℕ) {x : ℝ} (hx : 0<x) :
    pwGammaReversibleDensity x/x^k ≤ ((k+2).factorial:ℝ)*x*Real.exp (-x) := by
  have hp := Real.pow_div_factorial_le_exp x⁻¹ (inv_pos.mpr hx).le (k+2)
  have hf : (0:ℝ)<(k+2).factorial := by positivity
  have hb : (x⁻¹)^(k+2)*Real.exp (-x⁻¹) ≤ ((k+2).factorial:ℝ) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr
      (by simpa only [mul_comm] using (div_le_iff₀ hf).mp hp)
  calc
    _ = (x*Real.exp (-x))*((x⁻¹)^(k+2)*Real.exp (-x⁻¹)) := by
      unfold pwGammaReversibleDensity
      rw [sub_eq_add_neg, Real.exp_add, pow_add, inv_pow]
      field_simp
    _ ≤ (x*Real.exp (-x))*((k+2).factorial:ℝ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

private theorem pwGammaResponse_source_bound (z : ℂ) :
    ∃p:ℕ, ∃C:ℝ, 0≤C ∧ ∀x:ℝ, 0<x →
      ‖pwGammaMobiusTilt z x/pwGammaRaySource x‖≤(1+C)*(1+1/x)^p := by
  obtain ⟨p,C,hC,hb⟩ := pwGammaMobiusReciprocalTail_polynomial_bound z
  refine ⟨p,C,hC,fun x hx => ?_⟩
  have ht := hb (1/x) (by positivity)
  have he : pwGammaMobiusTilt z x/pwGammaRaySource x = pwGammaMobiusReciprocalTail z (1/x)+1 := by
    simp only [pwGammaMobiusReciprocalTail, one_div, inv_inv, sub_add_cancel]
  have h1 : (1:ℝ) ≤ (1+1/x)^p := one_le_pow₀ (by linarith [show (0:ℝ)≤1/x by positivity])
  have hp : (1/x)^p ≤ (1+1/x)^p := pow_le_pow_left₀ (by positivity) (by linarith) p
  rw [he]
  calc
    _ ≤ ‖pwGammaMobiusReciprocalTail z (1/x)‖+‖(1:ℂ)‖ := norm_add_le _ _
    _ ≤ C*(1/x)^p+1 := add_le_add ht (by simp)
    _ ≤ C*(1+1/x)^p+(1+1/x)^p := add_le_add (mul_le_mul_of_nonneg_left hp hC) h1
    _ = _ := by ring

private theorem pwGammaResponse_shifted_density_bound (k : ℕ) {x : ℝ} (hx : 0<x) :
    pwGammaReversibleDensity x*(1+1/x)^k ≤
      ((2:ℝ)^(k-1)*(((2:ℕ).factorial:ℝ)+((k+2).factorial:ℝ)))*x*Real.exp (-x) := by
  have ha := add_pow_le (show (0:ℝ)≤1 by positivity) (show (0:ℝ)≤1/x by positivity) k
  have hw := (pwGammaReversibleDensity_pos hx).le
  calc
    _ ≤ pwGammaReversibleDensity x*((2:ℝ)^(k-1)*(1^k+(1/x)^k)) :=
      mul_le_mul_of_nonneg_left ha hw
    _ = (2:ℝ)^(k-1)*(pwGammaReversibleDensity x/x^0+pwGammaReversibleDensity x/x^k) := by
      rw [div_pow, one_pow, pow_zero]
      ring
    _ ≤ (2:ℝ)^(k-1)*(((2:ℕ).factorial:ℝ)*x*Real.exp (-x)+
        ((k+2).factorial:ℝ)*x*Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left (add_le_add (pwGammaResponse_density_bound 0 hx)
        (pwGammaResponse_density_bound k hx)) (by positivity)
    _ = _ := by ring

theorem pwGammaMobiusAdjointResponseKernel_bound (z v : ℂ) :
    ∃r:ℕ, ∃C:ℝ, 0≤C ∧ ∀x h:ℝ, 0<x → 0<h →
      ‖pwGammaMobiusAdjointResponseKernel z v (x,h)‖ ≤
        C*x*Real.exp (-x)*(Real.exp (-h)*(1+h)^r) := by
  obtain ⟨p,A,hA,ha⟩ := pwGammaResponse_source_bound v
  obtain ⟨N,hN⟩ := exists_nat_ge ‖z‖
  let r := N+2
  let K : ℝ := ((r+2).factorial:ℝ)*(∑' n, pwGammaMobiusReciprocalInverseWeight z (r+1) n)
  have hK : 0≤K := by
    apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro n
    unfold pwGammaMobiusReciprocalInverseWeight
    positivity
  let D : ℝ := (2:ℝ)^(p+r-1)*(((2:ℕ).factorial:ℝ)+((p+r+2).factorial:ℝ))
  have hD : 0≤D := by positivity
  refine ⟨r,(1+A)*K*D,by positivity,fun x h hx hh => ?_⟩
  have hw := (pwGammaReversibleDensity_pos hx).le
  have ht := pwGammaMobiusReciprocalResponse_weight_bound hN (le_refl (N+2))
    (show 0<1/x by positivity) hh
  change ‖pwGammaMobiusReciprocalResponse z (1/x) h‖ ≤ K*Real.exp (-h)*(1/x+h)^r at ht
  have hs : (1/x+h)^r ≤ (1+1/x)^r*(1+h)^r := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [mul_nonneg (show (0:ℝ)≤1/x by positivity) hh.le]
  have ht' := ht.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  unfold pwGammaMobiusAdjointResponseKernel
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hw,Complex.norm_conj]
  calc
    _ ≤ pwGammaReversibleDensity x*((1+A)*(1+1/x)^p)*
        (K*Real.exp (-h)*((1+1/x)^r*(1+h)^r)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (ha x hx) hw) ht' (norm_nonneg _) (by positivity)
    _ = ((1+A)*K*(Real.exp (-h)*(1+h)^r))*
        (pwGammaReversibleDensity x*(1+1/x)^(p+r)) := by rw [pow_add]; ring
    _ ≤ ((1+A)*K*(Real.exp (-h)*(1+h)^r))*(D*x*Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left (pwGammaResponse_shifted_density_bound (p+r) hx) (by positivity)
    _ = _ := by ring


theorem pwGammaMobiusAdjointResponseKernel_integrable (z v : ℂ) :
    Integrable (pwGammaMobiusAdjointResponseKernel z v)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  obtain ⟨r,C,hC,hb⟩ := pwGammaMobiusAdjointResponseKernel_bound z v
  have hx : IntegrableOn (fun x : ℝ => C*x*Real.exp (-x)) (Ioi 0) := by
    change Integrable (fun x : ℝ => C*x*Real.exp (-x)) (volume.restrict (Ioi (0:ℝ)))
    have hp := Real.GammaIntegral_convergent (s := (1:ℕ)+1) (by positivity)
    simpa only [add_sub_cancel_right, Real.rpow_natCast, pow_one, mul_assoc, mul_comm, mul_left_comm] using hp.const_mul C
  apply (hx.mul_prod (pwGammaFlatShiftedMoment_integrable r)).mono'
    (pwGammaMobiusAdjointResponseKernel_measurable z v).aestronglyMeasurable
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  exact hb p.1 p.2 hp.1 hp.2

/-- The two original backward cutoff regions share one absolutely integrable kernel. -/
def pwGammaMobiusAdjointResponseCutoff (z v : ℂ) (a : ℝ → ℝ) (d : ℝ) (p : ℝ×ℝ) : ℂ :=
  if d<p.1 ∧ a p.1<p.2 then pwGammaMobiusAdjointResponseKernel z v p else 0

private theorem pwGammaResponse_cutoff_measurable (z v : ℂ) {a : ℝ → ℝ}
    (ha : Measurable a) (d : ℝ) :
    Measurable (pwGammaMobiusAdjointResponseCutoff z v a d) := by
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt (ha.comp measurable_fst) measurable_snd)
  · exact pwGammaMobiusAdjointResponseKernel_measurable z v
  · exact measurable_const

private theorem pwGammaResponse_cutoff_norm (z v : ℂ) (a : ℝ → ℝ) (d : ℝ) (p : ℝ×ℝ) :
    ‖pwGammaMobiusAdjointResponseCutoff z v a d p‖ ≤ ‖pwGammaMobiusAdjointResponseKernel z v p‖ := by
  unfold pwGammaMobiusAdjointResponseCutoff
  split_ifs
  · exact le_refl _
  · simpa only [norm_zero] using norm_nonneg (pwGammaMobiusAdjointResponseKernel z v p)

private theorem pwGammaResponse_cutoff_integrable (z v : ℂ) {a : ℝ → ℝ}
    (ha : Measurable a) (d : ℝ) :
    Integrable (pwGammaMobiusAdjointResponseCutoff z v a d)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  exact (pwGammaMobiusAdjointResponseKernel_integrable z v).mono
    (pwGammaResponse_cutoff_measurable z v ha d).aestronglyMeasurable
    (Eventually.of_forall (pwGammaResponse_cutoff_norm z v a d))

private theorem pwGammaResponse_cutoff_tendsto (z v : ℂ) (a : ℝ → ℝ → ℝ)
    (ha : ∀d, Measurable (a d))
    (ha0 : ∀x:ℝ, 0<x → Tendsto (fun d => a d x) (𝓝[>] (0:ℝ)) (𝓝 0)) :
    Tendsto (fun d => ∫p, pwGammaMobiusAdjointResponseCutoff z v (a d) d p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))
      (𝓝[>] (0:ℝ)) (𝓝 (∫p, pwGammaMobiusAdjointResponseKernel z v p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun p => ‖pwGammaMobiusAdjointResponseKernel z v p‖)
    (Eventually.of_forall fun d => (pwGammaResponse_cutoff_measurable z v (ha d) d).aestronglyMeasurable)
    (Eventually.of_forall fun d => Eventually.of_forall (pwGammaResponse_cutoff_norm z v (a d) d))
    (pwGammaMobiusAdjointResponseKernel_integrable z v).norm
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  have hd : Tendsto (fun d : ℝ => d) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [hd.eventually (gt_mem_nhds (show 0<p.1 from hp.1)),
    (ha0 p.1 hp.1).eventually (gt_mem_nhds (show 0<p.2 from hp.2))] with d hd1 hd2
  exact (if_pos (show d<p.1 ∧ a d p.1<p.2 from ⟨hd1,hd2⟩)).symm

theorem pwGammaMobiusAdjointResponseCutoff_native_tendsto (z v : ℂ) :
    Tendsto (fun d => ∫p, pwGammaMobiusAdjointResponseCutoff z v (fun _ => d) d p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))
      (𝓝[>] (0:ℝ)) (𝓝 (∫p, pwGammaMobiusAdjointResponseKernel z v p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))) := by
  exact pwGammaResponse_cutoff_tendsto z v (fun d _ => d) (fun _ => measurable_const)
    (fun _ _ => tendsto_id.mono_left nhdsWithin_le_nhds)

theorem pwGammaMobiusAdjointResponseCutoff_reciprocal_tendsto (z v : ℂ) :
    Tendsto (fun d => ∫p, pwGammaMobiusAdjointResponseCutoff z v
      (fun x => pwGammaAdjointCutoffLower x d) d p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))
      (𝓝[>] (0:ℝ)) (𝓝 (∫p, pwGammaMobiusAdjointResponseKernel z v p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))))) := by
  apply pwGammaResponse_cutoff_tendsto
  · intro d
    unfold pwGammaAdjointCutoffLower
    fun_prop
  · intro x hx
    exact pwGammaAdjointCutoffLower_tendsto hx


theorem pwGammaMobiusAdjointResponseKernel_section_integrable (z v : ℂ) {x : ℝ} (hx : 0<x) :
    IntegrableOn (fun h => pwGammaMobiusAdjointResponseKernel z v (x,h)) (Ioi 0) := by
  obtain ⟨r,C,hC,hb⟩ := pwGammaMobiusAdjointResponseKernel_bound z v
  apply ((pwGammaFlatShiftedMoment_integrable r).const_mul (C*x*Real.exp (-x))).mono'
    ((pwGammaMobiusAdjointResponseKernel_measurable z v).comp
      (by fun_prop : Measurable (fun h : ℝ => (x,h)))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact hb x h hx hh

private theorem pwGammaResponse_cutoff_section (z v : ℂ) (a : ℝ → ℝ) {d x : ℝ}
    (ha : d<x → 0≤a x) :
    (∫h in Ioi (0:ℝ), pwGammaMobiusAdjointResponseCutoff z v a d (x,h)) =
      (Ioi d).indicator (fun x => ∫h in Ioi (a x), pwGammaMobiusAdjointResponseKernel z v (x,h)) x := by
  by_cases hx : d<x
  · rw [indicator_of_mem (show x∈Ioi d from hx)]
    have he : (fun h => pwGammaMobiusAdjointResponseCutoff z v a d (x,h)) =
        (Ioi (a x)).indicator (fun h => pwGammaMobiusAdjointResponseKernel z v (x,h)) := by
      funext h
      simp only [pwGammaMobiusAdjointResponseCutoff, hx, true_and, Set.indicator, mem_Ioi]
    rw [he, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (ha hx))]
  · rw [indicator_of_notMem (show x∉Ioi d from hx)]
    simp only [pwGammaMobiusAdjointResponseCutoff, hx, false_and, if_false, integral_zero]

private theorem pwGammaResponse_cutoff_iterated (z v : ℂ) {a : ℝ → ℝ} (ha : Measurable a)
    {d : ℝ} (hd : 0≤d) (ha0 : ∀x, d<x → 0≤a x) :
    (∫p, pwGammaMobiusAdjointResponseCutoff z v a d p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) =
      ∫x in Ioi d, ∫h in Ioi (a x), pwGammaMobiusAdjointResponseKernel z v (x,h) := by
  rw [integral_prod _ (pwGammaResponse_cutoff_integrable z v ha d)]
  simp_rw [pwGammaResponse_cutoff_section z v a (ha0 _)]
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi hd)]

private theorem pwGammaResponse_cutoff_outer_integrable (z v : ℂ) {a : ℝ → ℝ} (ha : Measurable a)
    {d : ℝ} (hd : 0≤d) (ha0 : ∀x, d<x → 0≤a x) :
    IntegrableOn (fun x => ∫h in Ioi (a x), pwGammaMobiusAdjointResponseKernel z v (x,h)) (Ioi d) := by
  have hi : IntegrableOn (fun x => ∫h in Ioi (0:ℝ),
      pwGammaMobiusAdjointResponseCutoff z v a d (x,h)) (Ioi (0:ℝ)) :=
    (pwGammaResponse_cutoff_integrable z v ha d).integral_prod_left
  apply (hi.mono_set (Ioi_subset_Ioi hd)).congr_fun _ measurableSet_Ioi
  intro x hx
  dsimp only
  rw [pwGammaResponse_cutoff_section z v a (ha0 x), indicator_of_mem hx]

theorem pwGammaMobiusAdjointResponseKernel_cutoff_admission (z v : ℂ) {d : ℝ} (hd : 0<d) :
    IntegrableOn (fun x => ∫h in Ioi d, pwGammaMobiusAdjointResponseKernel z v (x,h)) (Ioi d) ∧
    IntegrableOn (fun x => ∫h in Ioi (pwGammaAdjointCutoffLower x d),
      pwGammaMobiusAdjointResponseKernel z v (x,h)) (Ioi d) := by
  constructor
  · exact pwGammaResponse_cutoff_outer_integrable z v measurable_const hd.le (fun _ _ => hd.le)
  · apply pwGammaResponse_cutoff_outer_integrable z v (by unfold pwGammaAdjointCutoffLower; fun_prop) hd.le
    intro x hx
    exact (pwGammaAdjointCutoffLower_pos (hd.trans hx) hd hx).le

theorem pwGammaMobiusAdjointResponseKernel_mismatch_eq (z v : ℂ) {d : ℝ} (hd : 0<d) :
    (∫x in Ioi d, ∫h in (pwGammaAdjointCutoffLower x d)..d,
      pwGammaMobiusAdjointResponseKernel z v (x,h)) =
    (∫p, pwGammaMobiusAdjointResponseCutoff z v (fun x => pwGammaAdjointCutoffLower x d) d p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) -
    (∫p, pwGammaMobiusAdjointResponseCutoff z v (fun _ => d) d p
      ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) := by
  have ha0 : ∀x, d<x → 0≤pwGammaAdjointCutoffLower x d :=
    fun x hx => (pwGammaAdjointCutoffLower_pos (hd.trans hx) hd hx).le
  rw [pwGammaResponse_cutoff_iterated z v (by unfold pwGammaAdjointCutoffLower; fun_prop) hd.le ha0,
    pwGammaResponse_cutoff_iterated z v measurable_const hd.le (fun _ _ => hd.le)]
  obtain ⟨hn,hr⟩ := pwGammaMobiusAdjointResponseKernel_cutoff_admission z v hd
  rw [← integral_sub hr hn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hi := pwGammaMobiusAdjointResponseKernel_section_integrable z v (hd.trans hx)
  exact (intervalIntegral.integral_Ioi_sub_Ioi'
    (hi.mono_set (Ioi_subset_Ioi (ha0 x hx))) (hi.mono_set (Ioi_subset_Ioi hd.le))).symm

theorem pwGammaMobiusAdjointResponseKernel_mismatch_integrable (z v : ℂ) {d : ℝ} (hd : 0<d) :
    IntegrableOn (fun x => ∫h in (pwGammaAdjointCutoffLower x d)..d,
      pwGammaMobiusAdjointResponseKernel z v (x,h)) (Ioi d) := by
  obtain ⟨hn,hr⟩ := pwGammaMobiusAdjointResponseKernel_cutoff_admission z v hd
  apply (hr.sub hn).congr_fun _ measurableSet_Ioi
  intro x hx
  have hi := pwGammaMobiusAdjointResponseKernel_section_integrable z v (hd.trans hx)
  exact intervalIntegral.integral_Ioi_sub_Ioi'
    (hi.mono_set (Ioi_subset_Ioi (pwGammaAdjointCutoffLower_pos (hd.trans hx) hd hx).le))
    (hi.mono_set (Ioi_subset_Ioi hd.le))

theorem pwGammaMobiusAdjointResponseKernel_mismatch_tendsto (z v : ℂ) :
    Tendsto (fun d => ∫x in Ioi d, ∫h in (pwGammaAdjointCutoffLower x d)..d,
      pwGammaMobiusAdjointResponseKernel z v (x,h)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have ht := (pwGammaMobiusAdjointResponseCutoff_reciprocal_tendsto z v).sub
    (pwGammaMobiusAdjointResponseCutoff_native_tendsto z v)
  simp only [sub_self] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (pwGammaMobiusAdjointResponseKernel_mismatch_eq z v hd).symm

theorem pwGammaMobiusAdjointResponseKernel_native_tendsto (z v : ℂ) :
    Tendsto (fun d => ∫x in Ioi d, ∫h in Ioi d,
      pwGammaMobiusAdjointResponseKernel z v (x,h)) (𝓝[>] (0:ℝ))
      (𝓝 (∫x in Ioi (0:ℝ), ∫h in Ioi (0:ℝ), pwGammaMobiusAdjointResponseKernel z v (x,h))) := by
  have ht := pwGammaMobiusAdjointResponseCutoff_native_tendsto z v
  rw [integral_prod _ (pwGammaMobiusAdjointResponseKernel_integrable z v)] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact pwGammaResponse_cutoff_iterated z v measurable_const (show 0≤d from le_of_lt hd)
    (fun _ _ => le_of_lt hd)


theorem pwGammaMobiusAdjointResponseKernel_interval_eq (z v : ℂ) (x a b : ℝ) :
    (∫h in a..b, pwGammaMobiusAdjointResponseKernel z v (x,h)) =
      (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
        (starRingEnd ℂ) (∫h in a..b, pwGammaMobiusReciprocalResponse z (1/x) h) := by
  unfold pwGammaMobiusAdjointResponseKernel
  dsimp only
  rw [intervalIntegral.integral_const_mul]
  congr 1
  simp only [intervalIntegral, integral_conj, map_sub]

theorem pwGammaMobiusAdjointResponseKernel_ray_eq (z v : ℂ) (x a : ℝ) :
    (∫h in Ioi a, pwGammaMobiusAdjointResponseKernel z v (x,h)) =
      (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
        (starRingEnd ℂ) (∫h in Ioi a, pwGammaMobiusReciprocalResponse z (1/x) h) := by
  unfold pwGammaMobiusAdjointResponseKernel
  dsimp only
  rw [integral_const_mul, integral_conj]

/-- The original source mismatch has an admitted outer integral at every positive cutoff. -/
theorem pwGammaMobiusAdjoint_original_mismatch_integrable (z v : ℂ) {d : ℝ} (hd : 0<d) :
    IntegrableOn (fun x => (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
      (starRingEnd ℂ) (∫h in (pwGammaAdjointCutoffLower x d)..d,
        pwGammaMobiusReciprocalResponse z (1/x) h)) (Ioi d) := by
  apply (pwGammaMobiusAdjointResponseKernel_mismatch_integrable z v hd).congr_fun _ measurableSet_Ioi
  intro x _
  exact pwGammaMobiusAdjointResponseKernel_interval_eq z v x _ _

/-- The complete changing-source mismatch vanishes, including the whole moving layer. -/
theorem pwGammaMobiusAdjoint_original_mismatch_tendsto (z v : ℂ) :
    Tendsto (fun d => ∫x in Ioi d,
      (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
        (starRingEnd ℂ) (∫h in (pwGammaAdjointCutoffLower x d)..d,
          pwGammaMobiusReciprocalResponse z (1/x) h)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  simpa only [pwGammaMobiusAdjointResponseKernel_interval_eq] using
    pwGammaMobiusAdjointResponseKernel_mismatch_tendsto z v

/-- Both native cutoffs pass together on the original source, retaining the initial omitted region. -/
theorem pwGammaMobiusAdjoint_original_native_tendsto (z v : ℂ) :
    Tendsto (fun d => ∫x in Ioi d,
      (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
        (starRingEnd ℂ) (∫h in Ioi d, pwGammaMobiusReciprocalResponse z (1/x) h))
      (𝓝[>] (0:ℝ)) (𝓝 (∫x in Ioi (0:ℝ),
      (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
        (starRingEnd ℂ) (∫h in Ioi (0:ℝ), pwGammaMobiusReciprocalResponse z (1/x) h))) := by
  simpa only [pwGammaMobiusAdjointResponseKernel_ray_eq] using
    pwGammaMobiusAdjointResponseKernel_native_tendsto z v

theorem pwGammaMobiusAdjoint_original_native_integrable (z v : ℂ) {d : ℝ} (hd : 0<d) :
    IntegrableOn (fun x => (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
      (starRingEnd ℂ) (∫h in Ioi d, pwGammaMobiusReciprocalResponse z (1/x) h)) (Ioi d) := by
  apply (pwGammaMobiusAdjointResponseKernel_cutoff_admission z v hd).1.congr_fun _ measurableSet_Ioi
  intro x _
  exact pwGammaMobiusAdjointResponseKernel_ray_eq z v x d

theorem pwGammaMobiusAdjoint_original_response_integrable (z v : ℂ) :
    IntegrableOn (fun x => (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
      (starRingEnd ℂ) (∫h in Ioi (0:ℝ), pwGammaMobiusReciprocalResponse z (1/x) h)) (Ioi 0) := by
  have hi : IntegrableOn (fun x => ∫h in Ioi (0:ℝ),
      pwGammaMobiusAdjointResponseKernel z v (x,h)) (Ioi (0:ℝ)) :=
    (pwGammaMobiusAdjointResponseKernel_integrable z v).integral_prod_left
  apply hi.congr_fun _ measurableSet_Ioi
  intro x _
  exact pwGammaMobiusAdjointResponseKernel_ray_eq z v x 0

end
end RHTower
