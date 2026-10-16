import GaloisForLFunctions.RHTower.CHMDStationaryConvolutionRepresentative

/-!
# Spatial localization of the ordinary stationary generator

The first Levy moment makes both endpoint pullbacks bounded. Their adjoints
give the exact cutoff commutator, valid on the whole closed form domain.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar

def stationaryMomentWeight (e : ℝ × ℝ) : ℝ := e.1 * archLevyDensity e.1
def stationaryMomentMeasure : Measure (ℝ × ℝ) :=
  archBase.withDensity (fun e => ENNReal.ofReal (stationaryMomentWeight e))

theorem measurable_stationaryMomentWeight : Measurable stationaryMomentWeight :=
  measurable_fst.mul (measurable_archLevyDensity.comp measurable_fst)

theorem stationaryMomentWeight_nonneg : ∀ᵐ e ∂archBase, 0 ≤ stationaryMomentWeight e :=
  archBase_fst_pos.mono fun _ he => mul_nonneg he.le (archLevyDensity_pos he).le

theorem integral_stationaryMoment (f : ℝ × ℝ → ℝ) :
    (∫ e, f e ∂stationaryMomentMeasure) = ∫ e, e.1 * f e ∂stationaryMeasure := by
  rw [stationaryMomentMeasure, integral_weighted archBase measurable_stationaryMomentWeight
    stationaryMomentWeight_nonneg, stationaryMeasure,
    integral_weighted archBase
      (show Measurable (fun e : ℝ × ℝ => archLevyDensity e.1) from measurable_archLevyDensity.comp measurable_fst)
      (archBase_fst_pos.mono fun e he => (archLevyDensity_pos he).le)]
  apply integral_congr_ae
  exact Eventually.of_forall fun e => by dsimp [stationaryMomentWeight]; ring

theorem integrable_stationaryMoment_iff (f : ℝ × ℝ → ℝ) :
    Integrable f stationaryMomentMeasure ↔ Integrable (fun e => e.1 * f e) stationaryMeasure := by
  rw [stationaryMomentMeasure, integrable_weighted_iff archBase measurable_stationaryMomentWeight
    stationaryMomentWeight_nonneg, stationaryMeasure,
    integrable_weighted_iff archBase
      (show Measurable (fun e : ℝ × ℝ => archLevyDensity e.1) from measurable_archLevyDensity.comp measurable_fst)
      (archBase_fst_pos.mono fun e he => (archLevyDensity_pos he).le)]
  apply integrable_congr
  exact Eventually.of_forall fun e => by dsimp [stationaryMomentWeight]; ring

theorem nonsingular_stationaryMoment_left :
    Measure.QuasiMeasurePreserving left stationaryMomentMeasure (volume : Measure ℝ) :=
  Measure.quasiMeasurePreserving_snd.mono_left (withDensity_absolutelyContinuous archBase _)

theorem nonsingular_stationaryMoment_right :
    Measure.QuasiMeasurePreserving right stationaryMomentMeasure (volume : Measure ℝ) := by
  have h := Measure.quasiMeasurePreserving_snd.comp
    (measurePreserving_prod_add (volume.restrict (Ioi (0 : ℝ))) volume).quasiMeasurePreserving
  have h' : Measure.QuasiMeasurePreserving right archBase volume := by
    change Measure.QuasiMeasurePreserving (fun e : ℝ × ℝ => e.2 + e.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) volume
    simpa only [Function.comp_def, add_comm] using h
  exact h'.mono_left (withDensity_absolutelyContinuous archBase _)

theorem memLp_stationaryMoment_left (v : StationaryVolumeSpace) :
    MemLp (v ∘ left) 2 stationaryMomentMeasure := by
  apply (memLp_two_iff_integrable_sq
    ((Lp.stronglyMeasurable v).measurable.comp measurable_snd).aestronglyMeasurable).mpr
  rw [stationaryMomentMeasure, integrable_weighted_iff archBase
      measurable_stationaryMomentWeight stationaryMomentWeight_nonneg]
  exact integrableOn_mul_archLevyDensity.mul_prod (Lp.memLp v).integrable_sq

theorem memLp_stationaryMoment_right (v : StationaryVolumeSpace) :
    MemLp (v ∘ right) 2 stationaryMomentMeasure := by
  apply (memLp_two_iff_integrable_sq
    ((Lp.stronglyMeasurable v).measurable.comp (measurable_snd.add measurable_fst)).aestronglyMeasurable).mpr
  rw [stationaryMomentMeasure, integrable_weighted_iff archBase
      measurable_stationaryMomentWeight stationaryMomentWeight_nonneg]
  have h := (measurePreserving_prod_add (volume.restrict (Ioi (0 : ℝ))) volume).integrable_comp_of_integrable
    (integrableOn_mul_archLevyDensity.mul_prod (Lp.memLp v).integrable_sq)
  simpa only [archBase, Function.comp_def, stationaryMomentWeight, right, Pi.add_apply, add_comm] using h

def stationaryMomentLeft : StationaryVolumeSpace →L[ℝ] Lp ℝ 2 stationaryMomentMeasure :=
  admittedPullback left stationaryMomentMeasure nonsingular_stationaryMoment_left memLp_stationaryMoment_left
def stationaryMomentRight : StationaryVolumeSpace →L[ℝ] Lp ℝ 2 stationaryMomentMeasure :=
  admittedPullback right stationaryMomentMeasure nonsingular_stationaryMoment_right memLp_stationaryMoment_right

theorem stationaryMomentLeft_ae (u : StationaryVolumeSpace) :
    stationaryMomentLeft u =ᵐ[stationaryMomentMeasure] u ∘ left :=
  admittedPullback_ae _ _ _ _ u
theorem stationaryMomentRight_ae (u : StationaryVolumeSpace) :
    stationaryMomentRight u =ᵐ[stationaryMomentMeasure] u ∘ right :=
  admittedPullback_ae _ _ _ _ u

def volumeCutoff (n : ℕ) : StationaryVolumeSpace →L[ℝ] StationaryVolumeSpace :=
  lpBoundedMulCLM (cutoff_contDiff n).continuous.measurable (by norm_num) (cutoff_norm_le_one n)

theorem volumeCutoff_ae (n : ℕ) (u : StationaryVolumeSpace) :
    volumeCutoff n u =ᵐ[volume] fun x => cutoff n x * u x := lpBoundedMulCLM_coeFn _ _ _ u

theorem volumeCutoff_symmetric (n : ℕ) (u v : StationaryVolumeSpace) :
    ⟪volumeCutoff n u, v⟫_ℝ = ⟪u, volumeCutoff n v⟫_ℝ :=
  lpBoundedMulCLM_inner_real _ _ _ (fun _ => rfl) u v

def stationarySlopeOperator (n : ℕ) : Lp ℝ 2 stationaryMomentMeasure →L[ℝ] Lp ℝ 2 stationaryMomentMeasure :=
  lpBoundedMulCLM (measurable_cutoffSlope n) cutoffLipschitz.coe_nonneg (cutoffSlope_bound n)

theorem stationarySlopeOperator_ae (n : ℕ) (u : Lp ℝ 2 stationaryMomentMeasure) :
    stationarySlopeOperator n u =ᵐ[stationaryMomentMeasure] fun e => cutoffSlope n e * u e :=
  lpBoundedMulCLM_coeFn _ _ _ u

theorem memLp_volumeCutoff_correction (n : ℕ) (u : StationaryVolumeSpace) :
    MemLp (fun e => (cutoff n (left e) - cutoff n (right e)) * u (right e)) 2 stationaryMeasure := by
  have hu := (Lp.stronglyMeasurable u).measurable
  have hc := (cutoff_contDiff n).continuous.measurable
  have hm : Measurable (fun e : ℝ × ℝ =>
      (cutoff n (left e) - cutoff n (right e)) * u (right e)) :=
    ((hc.comp measurable_snd).sub (hc.comp (measurable_snd.add measurable_fst))).mul
      (hu.comp (measurable_snd.add measurable_fst))
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hi := (integrable_stationaryMoment_iff _).mp (memLp_stationaryMoment_right u).integrable_sq
  refine (hi.const_mul (cutoffLipschitz : ℝ)).mono' (hm.pow_const 2).aestronglyMeasurable ?_
  have ht : ∀ᵐ e ∂stationaryMeasure, 0 < e.1 :=
    (withDensity_absolutelyContinuous archBase _).ae_le archBase_fst_pos
  filter_upwards [ht] with e he
  rw [Real.norm_of_nonneg (sq_nonneg _), mul_pow]
  exact (mul_le_mul_of_nonneg_right (cutoff_difference_sq_le n he) (sq_nonneg (u (right e)))).trans_eq
    (by dsimp; ring)

theorem memLp_volumeCutoff_difference (n : ℕ) (p : StationaryVolumeGraph) :
    MemLp (difference (fun x => cutoff n x * p.val.fst x)) 2 stationaryMeasure := by
  have h0 := memLp_mul_of_bound (μ := stationaryMeasure) (p := 2)
    ((cutoff_contDiff n).continuous.measurable.comp measurable_snd)
    (by norm_num : (0 : ℝ) ≤ 1) (fun e => cutoff_norm_le_one n (left e)) p.val.snd
  have hp : p.val.snd =ᵐ[stationaryMeasure] difference p.val.fst := p.property
  have h1 := h0.ae_eq (hp.mono fun e he => congrArg (fun y => cutoff n (left e) * y) he)
  refine (h1.add (memLp_volumeCutoff_correction n p.val.fst)).ae_eq ?_
  exact Eventually.of_forall fun e => by dsimp [difference]; ring

def volumeGraphCutoff (n : ℕ) (p : StationaryVolumeGraph) : StationaryVolumeGraph :=
  ofFunction volume stationaryMeasure left right
    nonsingular_stationary_volume_left nonsingular_stationary_volume_right
    (fun x => cutoff n x * p.val.fst x)
    (memLp_mul_of_bound (cutoff_contDiff n).continuous.measurable
      (by norm_num) (cutoff_norm_le_one n) p.val.fst) (memLp_volumeCutoff_difference n p)

theorem volumeGraphCutoff_source (n : ℕ) (p : StationaryVolumeGraph) :
    volumeSourceMap (volumeGraphCutoff n p) = volumeCutoff n (volumeSourceMap p) := rfl

def volumeCutoffCommutator (n : ℕ) : StationaryVolumeSpace →L[ℝ] StationaryVolumeSpace :=
  stationaryMomentLeft.adjoint.comp ((stationarySlopeOperator n).comp stationaryMomentRight) -
    stationaryMomentRight.adjoint.comp ((stationarySlopeOperator n).comp stationaryMomentLeft)

theorem volumeCutoffCommutator_inner (n : ℕ) (u v : StationaryVolumeSpace) :
    ⟪volumeCutoffCommutator n u, v⟫_ℝ =
      ∫ e, cutoffSlope n e * (u (right e) * v (left e) - u (left e) * v (right e))
        ∂stationaryMomentMeasure := by
  change ⟪stationaryMomentLeft.adjoint (stationarySlopeOperator n (stationaryMomentRight u)) -
    stationaryMomentRight.adjoint (stationarySlopeOperator n (stationaryMomentLeft u)), v⟫_ℝ = _
  rw [inner_sub_left, stationaryMomentLeft.adjoint_inner_left,
    stationaryMomentRight.adjoint_inner_left, cutoff_inner_realLp, cutoff_inner_realLp,
    ← integral_sub (cutoff_integrable_mul _ _) (cutoff_integrable_mul _ _)]
  apply integral_congr_ae
  filter_upwards [stationarySlopeOperator_ae n (stationaryMomentRight u),
    stationarySlopeOperator_ae n (stationaryMomentLeft u), stationaryMomentRight_ae u,
    stationaryMomentLeft_ae u, stationaryMomentLeft_ae v, stationaryMomentRight_ae v] with e h1 h2 h3 h4 h5 h6
  simp only [Function.comp_apply] at *
  rw [h1, h2, h3, h4, h5, h6]
  ring

theorem volumeGraphCutoff_edge_pairing (n : ℕ) (p q : StationaryVolumeGraph) :
    ⟪(volumeGraphCutoff n p).val.snd, q.val.snd⟫_ℝ -
      ⟪p.val.snd, (volumeGraphCutoff n q).val.snd⟫_ℝ =
        ⟪volumeCutoffCommutator n (volumeSourceMap p), volumeSourceMap q⟫_ℝ := by
  rw [cutoff_inner_realLp, cutoff_inner_realLp,
    ← integral_sub (cutoff_integrable_mul _ _) (cutoff_integrable_mul _ _),
    volumeCutoffCommutator_inner, integral_stationaryMoment]
  have ht : ∀ᵐ e ∂stationaryMeasure, 0 < e.1 :=
    (withDensity_absolutelyContinuous archBase _).ae_le archBase_fst_pos
  apply integral_congr_ae
  filter_upwards [(memLp_volumeCutoff_difference n p).coeFn_toLp,
    (memLp_volumeCutoff_difference n q).coeFn_toLp, p.property, q.property, ht]
    with e hp hq hpe hqe he
  change (volumeGraphCutoff n p).val.snd e * q.val.snd e -
    p.val.snd e * (volumeGraphCutoff n q).val.snd e =
      e.1 * (cutoffSlope n e *
        (p.val.fst (right e) * q.val.fst (left e) - p.val.fst (left e) * q.val.fst (right e)))
  change (volumeGraphCutoff n p).val.snd e = difference (fun x => cutoff n x * p.val.fst x) e at hp
  change (volumeGraphCutoff n q).val.snd e = difference (fun x => cutoff n x * q.val.fst x) e at hq
  rw [hp, hq, hpe, hqe]
  dsimp only [difference, cutoffSlope]
  field_simp [he.ne']
  ring

end RHTower.CHMDDoobGraph
