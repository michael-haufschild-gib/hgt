import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalTemporalCorner

/-! Admitted physical horizon mass tails and their original first moments. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalRestoredTemporalContacts
noncomputable section
set_option autoImplicit false

def tailMass (A : ℝ→ℂ) (a : ℝ) : ℂ := ∫ p in Ioi a,A p
def tailCorner (A : ℝ→ℂ) (a : ℝ) : ℂ := ∫ p in Ioi a,tailMass A p

/-- A separately admitted triangular kernel identifies the tail of a horizon
mass with its original shifted first moment. -/
theorem tail_corner_moment (A : ℝ→ℂ) (hA : IntegrableOn A (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*A p) (Ioi (0:ℝ)))
    (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (tailMass A) (Ioi a) ∧
      tailCorner A a=∫ p in Ioi a,((p-a:ℝ):ℂ)*A p := by
  let μ := volume.restrict (Ioi a)
  let S := {v : ℝ×ℝ | v.1<v.2}
  let F := S.indicator (fun v : ℝ×ℝ => A v.2)
  have hAa := hA.mono_set (Ioi_subset_Ioi ha)
  have hMa := hM.mono_set (Ioi_subset_Ioi ha)
  have hS : MeasurableSet S := measurableSet_lt measurable_fst measurable_snd
  have hF : AEStronglyMeasurable F (μ.prod μ) := hAa.aestronglyMeasurable.comp_snd.indicator hS
  have hleft (p : ℝ) : (∫ x in Ioi a,F (x,p))=((max (p-a) 0:ℝ):ℂ)*A p := by
    change (∫ x in Ioi a,(Iio p).indicator (fun _ => A p) x)=_
    rw [setIntegral_indicator measurableSet_Iio]
    change (∫ x in Ioo a p,A p)=_
    rw [setIntegral_const,Real.volume_real_Ioo,Complex.real_smul]
  have hnorm (p : ℝ) : (∫ x in Ioi a,‖F (x,p)‖)=max (p-a) 0*‖A p‖ := by
    have he : (fun x => ‖F (x,p)‖)=(Iio p).indicator (fun _ => ‖A p‖) := by
      funext x
      by_cases h : x<p <;> simp [F,S,h]
    rw [he,setIntegral_indicator measurableSet_Iio]
    change (∫ x in Ioo a p,‖A p‖)=_
    rw [setIntegral_const,Real.volume_real_Ioo,smul_eq_mul]
  have hrow (p : ℝ) : Integrable (fun x => F (x,p)) μ := by
    change IntegrableOn ((Iio p).indicator (fun _ => A p)) (Ioi a)
    rw [integrableOn_indicator_iff measurableSet_Iio]
    rw [Set.inter_comm]
    change IntegrableOn (fun _ : ℝ => A p) (Ioo a p)
    exact integrableOn_const (by simp [Real.volume_Ioo])
  have hpm : IntegrableOn (fun p : ℝ => p*‖A p‖) (Ioi a) := by
    apply hMa.norm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (ha.trans_lt hp)]
  have hwgt : IntegrableOn (fun p : ℝ => (p-a)*‖A p‖) (Ioi a) := by
    apply (hpm.sub (hAa.norm.const_mul a)).congr
    exact ae_of_all _ (fun p => by change p*‖A p‖-a*‖A p‖=(p-a)*‖A p‖;ring)
  have hnormInt : Integrable (fun p => ∫ x,‖F (x,p)‖ ∂μ) μ := by
    apply hwgt.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    rw [hnorm,max_eq_left (sub_nonneg.mpr hp.le)]
  have hFi : Integrable F (μ.prod μ) := (integrable_prod_iff' hF).mpr
    ⟨ae_of_all _ hrow,hnormInt⟩
  have hright (x : ℝ) (hx : a<x) : (∫ p in Ioi a,F (x,p))=tailMass A x := by
    change (∫ p in Ioi a,(Ioi x).indicator A p)=_
    rw [setIntegral_indicator measurableSet_Ioi]
    have he : Ioi a ∩ Ioi x=Ioi x := by
      ext p
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hx.trans h,h⟩
    rw [he]
    rfl
  refine ⟨hFi.integral_prod_left.congr ?_,?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hright x hx
  · calc
      tailCorner A a = ∫ x,∫ p,F (x,p) ∂μ ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact (hright x hx).symm
      _ = ∫ v,F v ∂(μ.prod μ) := (integral_prod F hFi).symm
      _ = ∫ p,∫ x,F (x,p) ∂μ ∂μ := integral_prod_symm F hFi
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
        rw [hleft,max_eq_left (sub_nonneg.mpr hp.le)]

def momentCorner (A : ℝ→ℂ) (a : ℝ) : ℂ :=
  ∫ p in Ioi (0:ℝ),((max (p-a) 0:ℝ):ℂ)*A p

private theorem moment_corner_eq (A : ℝ→ℂ) (a : ℝ) (ha : 0 ≤ a) :
    momentCorner A a=∫ p in Ioi a,((p-a:ℝ):ℂ)*A p := by
  have he : (fun p : ℝ => ((max (p-a) 0:ℝ):ℂ)*A p)=
      (Ioi a).indicator (fun p => ((p-a:ℝ):ℂ)*A p) := by
    funext p
    by_cases hp : a<p
    · simp [hp,max_eq_left (sub_nonneg.mpr hp.le)]
    · simp [hp,max_eq_right (sub_nonpos.mpr (le_of_not_gt hp))]
  unfold momentCorner
  rw [he,setIntegral_indicator measurableSet_Ioi]
  have hi : Ioi (0:ℝ) ∩ Ioi a=Ioi a := by
    ext p
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨ha.trans_lt h,h⟩
  rw [hi]

private theorem first_norm_integrable (A : ℝ→ℂ)
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*A p) (Ioi (0:ℝ))) :
    IntegrableOn (fun p : ℝ => p*‖A p‖) (Ioi (0:ℝ)) := by
  apply hM.norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  have hp' : (0:ℝ)<p := hp
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp']

private theorem moment_integrand_bound (A : ℝ→ℂ) (a p : ℝ) (ha : 0 ≤ a) (hp : 0<p) :
    ‖((max (p-a) 0:ℝ):ℂ)*A p‖ ≤ p*‖A p‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
  exact mul_le_mul_of_nonneg_right (max_le (by linarith) hp.le) (norm_nonneg _)

theorem moment_corner_integrable (A : ℝ→ℂ) (hA : IntegrableOn A (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*A p) (Ioi (0:ℝ)))
    (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun p : ℝ => ((max (p-a) 0:ℝ):ℂ)*A p) (Ioi (0:ℝ)) := by
  apply (first_norm_integrable A hM).mono'
    (((show Continuous (fun p : ℝ => ((max (p-a) 0:ℝ):ℂ)) by fun_prop).aestronglyMeasurable).mul
      hA.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact moment_integrand_bound A a p ha hp

/-- The original corner tails vanish at the terminal endpoint using exactly
the admitted first moment, with no pointwise decay hypothesis. -/
theorem tail_corner_terminal (A : ℝ→ℂ) (hA : IntegrableOn A (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*A p) (Ioi (0:ℝ))) :
    Tendsto (tailCorner A) atTop (𝓝 0) := by
  have hm : Tendsto (momentCorner A) atTop (𝓝 0) := by
    have hzero : (∫ p in Ioi (0:ℝ),(0:ℂ))=0 := by simp
    rw [← hzero]
    apply tendsto_integral_filter_of_dominated_convergence (fun p : ℝ => p*‖A p‖)
    · filter_upwards [] with a
      exact ((show Continuous (fun p : ℝ => ((max (p-a) 0:ℝ):ℂ)) by fun_prop).aestronglyMeasurable).mul
        hA.aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with a ha
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      exact moment_integrand_bound A a p ha hp
    · exact first_norm_integrable A hM
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop p] with a ha
      simp only [max_eq_right (sub_nonpos.mpr ha),Complex.ofReal_zero,zero_mul]
  apply hm.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with a ha
  exact (moment_corner_eq A a ha).trans (tail_corner_moment A hA hM a ha).2.symm

/-- The same admitted tail corner has the original zero-onset first moment
as its limit; no finite onset is replaced before the clock subtraction. -/
theorem tail_corner_onset (A : ℝ→ℂ) (hA : IntegrableOn A (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*A p) (Ioi (0:ℝ))) :
    Tendsto (tailCorner A) (𝓝[>] (0:ℝ)) (𝓝 (tailCorner A 0)) := by
  have hm : Tendsto (momentCorner A) (𝓝[>] (0:ℝ))
      (𝓝 (∫ p in Ioi (0:ℝ),(p:ℂ)*A p)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p : ℝ => p*‖A p‖)
    · filter_upwards [] with a
      exact ((show Continuous (fun p : ℝ => ((max (p-a) 0:ℝ):ℂ)) by fun_prop).aestronglyMeasurable).mul
        hA.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with a ha
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      exact moment_integrand_bound A a p ha.le hp
    · exact first_norm_integrable A hM
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      have hp' : (0:ℝ)<p := hp
      have hc : Continuous (fun a : ℝ => ((max (p-a) 0:ℝ):ℂ)*A p) := by fun_prop
      have ht : Tendsto (fun a : ℝ => ((max (p-a) 0:ℝ):ℂ)*A p) (𝓝 (0:ℝ))
          (𝓝 (((max (p-0) 0:ℝ):ℂ)*A p)) := hc.continuousAt.tendsto
      simpa only [sub_zero,max_eq_left hp'.le] using! ht.mono_left nhdsWithin_le_nhds
  have hzero : tailCorner A 0=∫ p in Ioi (0:ℝ),(p:ℂ)*A p := by
    simpa only [sub_zero] using (tail_corner_moment A hA hM 0 le_rfl).2
  rw [hzero]
  apply hm.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (moment_corner_eq A a ha.le).trans (tail_corner_moment A hA hM a ha.le).2.symm

open D4BMModularCore D4BMJointSource D4BMOriginalTemporalCorner D4BMOriginalCornerForcing

private theorem physical_moments (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : 3/2<w.re) :
    IntegrableOn (leadingDensity q br amp w) (Ioi (0:ℝ)) ∧
      IntegrableOn (fun p : ℝ => (p:ℂ)*leadingDensity q br amp w p) (Ioi (0:ℝ)) := by
  have hq := (xi_divisor_support_re_mem_open_unit q.1).1
  have hwr : (D4BMOriginalCirclePeriod.readerExponent q).re<w.re := by
    norm_num [D4BMOriginalCirclePeriod.readerExponent]
    linarith
  exact ⟨by simpa only [pow_zero,one_mul] using leading_moment_integrable q br amp w 0 hwr,
    by simpa only [pow_one] using leading_moment_integrable q br amp w 1 hwr⟩

/-- The admitted mass-tail corner of the original full horizon density,
with its unchanged coordinate logarithm, equals the prescribed canonical corner. -/
theorem physical_mass_tail_canonical_corner (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) (hwi : w.im≠0) :
    IntegrableOn (tailMass (leadingDensity q br amp w)) (Ioi (0:ℝ)) ∧
      -tailCorner (leadingDensity q br amp w) 0-
        (Real.log 2:ℂ)*tailMass (leadingDensity q br amp w) 0=physicalCornerCandidate q br amp w := by
  obtain ⟨hA,hM⟩ := physical_moments q br amp w hw
  obtain ⟨hi,he⟩ := tail_corner_moment (leadingDensity q br amp w) hA hM 0 le_rfl
  refine ⟨hi,?_⟩
  rw [he]
  simpa only [sub_zero,tailMass] using original_corner_moment_eq_candidate q br amp w hw hwi


end
end RHTower.D4BMOriginalRestoredTemporalContacts
