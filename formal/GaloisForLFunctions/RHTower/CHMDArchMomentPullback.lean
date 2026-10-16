import GaloisForLFunctions.RHTower.CHMDStationaryGenerators
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

/-!
# Bounded endpoint pullbacks for the first archimedean jump moment

The measure `t d archMeasure` admits both endpoint evaluations of every mass-L2
source. Closed graph then makes these literal pullbacks bounded. This is the
factorization space for spatial cutoff commutators on the maximal generator.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar

def archMomentWeight (e : ℝ × ℝ) : ℝ := e.1 * archWeight e

def archMomentMeasure : Measure (ℝ × ℝ) :=
  archBase.withDensity (fun e => ENNReal.ofReal (archMomentWeight e))

theorem measurable_archMomentWeight : Measurable archMomentWeight :=
  measurable_fst.mul measurable_archWeight

theorem archBase_fst_pos : ∀ᵐ e ∂archBase, 0 < e.1 :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)

theorem archMomentWeight_nonneg : ∀ᵐ e ∂archBase, 0 ≤ archMomentWeight e := by
  filter_upwards [archBase_fst_pos, archWeight_nonneg_ae] with e ht hw
  exact mul_nonneg ht.le hw

theorem nonsingular_archMoment_left :
    Measure.QuasiMeasurePreserving left archMomentMeasure massMeasure :=
  (Measure.quasiMeasurePreserving_snd.mono_left
    (withDensity_absolutelyContinuous archBase _)).mono_right volume_absolutelyContinuous_mass

theorem nonsingular_archMoment_right :
    Measure.QuasiMeasurePreserving right archMomentMeasure massMeasure := by
  have h := Measure.quasiMeasurePreserving_snd.comp
    (measurePreserving_prod_add (volume.restrict (Ioi (0 : ℝ))) volume).quasiMeasurePreserving
  have h' : Measure.QuasiMeasurePreserving right archBase volume := by
    change Measure.QuasiMeasurePreserving (fun e : ℝ × ℝ => e.2 + e.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) volume
    simpa only [right, Function.comp_def, add_comm] using h
  exact (h'.mono_left (withDensity_absolutelyContinuous archBase _)).mono_right
    volume_absolutelyContinuous_mass

theorem memLp_archMoment_left (v : MassSpace) :
    MemLp (v ∘ left) 2 archMomentMeasure := by
  have hv := (Lp.stronglyMeasurable v).measurable
  have hs := integrable_theta_mul_sq hv (Lp.memLp v)
  obtain ⟨C, hC, hb, _⟩ := theta_global_and_exponential_bound
  apply (memLp_two_iff_integrable_sq
    (hv.comp measurable_snd).aestronglyMeasurable).mpr
  rw [archMomentMeasure, integrable_weighted_iff archBase
    measurable_archMomentWeight archMomentWeight_nonneg]
  have hi := (integrableOn_mul_archLevyDensity.mul_prod hs).const_mul C
  refine hi.mono' ((measurable_archMomentWeight.mul
    ((hv.comp measurable_snd).pow_const 2)).aestronglyMeasurable) ?_
  filter_upwards [archBase_fst_pos] with e ht
  have hpos := mul_nonneg (mul_nonneg ht.le (archLevyDensity_pos ht).le)
    (mul_nonneg (riemannKernelReal_pos e.2).le (sq_nonneg (v e.2)))
  have h := mul_le_mul_of_nonneg_right (hb (e.2 + e.1)) hpos
  change ‖archMomentWeight e * v (left e) ^ 2‖ ≤ _
  have hw : 0 ≤ archMomentWeight e := by
    have hk := (archLevyDensity_pos ht).le
    have hθl := (riemannKernelReal_pos e.2).le
    have hθr := (riemannKernelReal_pos (e.2 + e.1)).le
    dsimp [archMomentWeight, archWeight]
    positivity
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  dsimp [archMomentWeight, archWeight, left] at *
  nlinarith only [h]

theorem memLp_archMoment_right (v : MassSpace) :
    MemLp (v ∘ right) 2 archMomentMeasure := by
  have hv := (Lp.stronglyMeasurable v).measurable
  have hs := integrable_theta_mul_sq hv (Lp.memLp v)
  obtain ⟨C, hC, hb, _⟩ := theta_global_and_exponential_bound
  apply (memLp_two_iff_integrable_sq
    (hv.comp (measurable_snd.add measurable_fst)).aestronglyMeasurable).mpr
  rw [archMomentMeasure, integrable_weighted_iff archBase
    measurable_archMomentWeight archMomentWeight_nonneg]
  have hi : Integrable (fun e : ℝ × ℝ => C * (e.1 * archLevyDensity e.1 *
      (riemannKernelReal (e.2 + e.1) * v (e.2 + e.1) ^ 2))) archBase := by
    have h := (measurePreserving_prod_add (volume.restrict (Ioi (0 : ℝ))) volume).integrable_comp_of_integrable
      ((integrableOn_mul_archLevyDensity.mul_prod hs).const_mul C)
    change Integrable _ ((volume.restrict (Ioi (0 : ℝ))).prod volume)
    simpa only [Function.comp_def, add_comm] using h
  refine hi.mono' ((measurable_archMomentWeight.mul
    ((hv.comp (measurable_snd.add measurable_fst)).pow_const 2)).aestronglyMeasurable) ?_
  filter_upwards [archBase_fst_pos] with e ht
  have hpos := mul_nonneg (mul_nonneg ht.le (archLevyDensity_pos ht).le)
    (mul_nonneg (riemannKernelReal_pos (e.2 + e.1)).le (sq_nonneg (v (e.2 + e.1))))
  have h := mul_le_mul_of_nonneg_right (hb e.2) hpos
  change ‖archMomentWeight e * v (right e) ^ 2‖ ≤ _
  have hw : 0 ≤ archMomentWeight e := by
    have hk := (archLevyDensity_pos ht).le
    have hθl := (riemannKernelReal_pos e.2).le
    have hθr := (riemannKernelReal_pos (e.2 + e.1)).le
    dsimp [archMomentWeight, archWeight]
    positivity
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  dsimp [archMomentWeight, archWeight, right] at *
  nlinarith only [h]

section Pullback
variable (a : ℝ × ℝ → ℝ) (η : Measure (ℝ × ℝ))
  (ha : Measure.QuasiMeasurePreserving a η massMeasure)
  (hm : ∀ v : MassSpace, MemLp (v ∘ a) 2 η)

def admittedPullbackLM : MassSpace →ₗ[ℝ] Lp ℝ 2 η where
  toFun v := (hm v).toLp (v ∘ a)
  map_add' v w := by
    apply Lp.ext
    filter_upwards [(hm (v + w)).coeFn_toLp, (hm v).coeFn_toLp, (hm w).coeFn_toLp,
      Lp.coeFn_add ((hm v).toLp _) ((hm w).toLp _), ha.ae (Lp.coeFn_add v w)]
      with e h1 h2 h3 h4 h5
    simp only [Function.comp_apply, Pi.add_apply] at *
    rw [h1, h4, h2, h3, h5]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [(hm (c • v)).coeFn_toLp, (hm v).coeFn_toLp,
      Lp.coeFn_smul c ((hm v).toLp _), ha.ae (Lp.coeFn_smul c v)] with e h1 h2 h3 h4
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at *
    change (hm (c • v)).toLp _ e = (c • (hm v).toLp _) e
    rw [h1, h3, h2, h4]

theorem admittedPullbackLM_ae (v : MassSpace) :
    admittedPullbackLM a η ha hm v =ᵐ[η] v ∘ a := (hm v).coeFn_toLp

theorem continuous_admittedPullbackLM : Continuous (admittedPullbackLM a η ha hm) := by
  apply LinearMap.continuous_of_isClosed_graph
  have heq : ((admittedPullbackLM a η ha hm).graph : Set (MassSpace × Lp ℝ 2 η)) =
      {p | p.2 =ᵐ[η] p.1 ∘ a} := by
    ext p
    change p.2 = admittedPullbackLM a η ha hm p.1 ↔ p.2 =ᵐ[η] p.1 ∘ a
    constructor
    · intro h
      rw [h]
      exact admittedPullbackLM_ae a η ha hm p.1
    · intro h
      exact Lp.ext (h.trans (admittedPullbackLM_ae a η ha hm p.1).symm)
  rw [heq]
  apply isSeqClosed_iff_isClosed.mp
  intro u p hu hp
  obtain ⟨ns, hns, hs⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ((continuous_fst.tendsto p).comp hp)).exists_seq_tendsto_ae
  obtain ⟨ms, hms, he⟩ := (tendstoInMeasure_of_tendsto_Lp
    (((continuous_snd.tendsto p).comp hp).comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hg : ∀ᵐ e ∂η, ∀ n : ℕ, (u (ns (ms n))).2 e = (u (ns (ms n))).1 (a e) :=
    ae_all_iff.mpr fun n => hu (ns (ms n))
  filter_upwards [ha.ae hs, he, hg] with e h1 h2 h3
  exact tendsto_nhds_unique h2 ((h1.comp hms.tendsto_atTop).congr fun n => (h3 n).symm)

def admittedPullback : MassSpace →L[ℝ] Lp ℝ 2 η :=
  ⟨admittedPullbackLM a η ha hm, continuous_admittedPullbackLM a η ha hm⟩

theorem admittedPullback_ae (v : MassSpace) :
    admittedPullback a η ha hm v =ᵐ[η] v ∘ a := admittedPullbackLM_ae a η ha hm v

end Pullback

def archMomentLeft : MassSpace →L[ℝ] Lp ℝ 2 archMomentMeasure :=
  admittedPullback left archMomentMeasure nonsingular_archMoment_left memLp_archMoment_left

def archMomentRight : MassSpace →L[ℝ] Lp ℝ 2 archMomentMeasure :=
  admittedPullback right archMomentMeasure nonsingular_archMoment_right memLp_archMoment_right

theorem archMomentLeft_ae (v : MassSpace) : archMomentLeft v =ᵐ[archMomentMeasure] v ∘ left :=
  admittedPullback_ae _ _ _ _ v

theorem archMomentRight_ae (v : MassSpace) : archMomentRight v =ᵐ[archMomentMeasure] v ∘ right :=
  admittedPullback_ae _ _ _ _ v

end RHTower.CHMDDoobGraph
