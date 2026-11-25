import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.OrderedLaw

/-! # Conditional probability that all occupied modes fall below an energy cut -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount

open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

private theorem intensity_ne_zero {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) :
    intensity hc hcd.le a ≠ 0 := by
  apply (FiniteMeasure.mass_nonzero_iff _).mp
  intro H
  have he := intensity_mass hc hcd.le a
  rw [H,NNReal.coe_zero] at he
  exact (mass_pos hc hcd a).ne he

/-- Restricting the intensity to a shorter energy band preserves its density. -/
theorem intensity_cut {c b d : ℝ} (hc : 0 < c) (hcb : c ≤ b) (hbd : b ≤ d) (a : ℝ) :
    (intensity hc (hcb.trans hbd) a : Measure ℝ).restrict (Iic b) = intensity hc hcb a := by
  change ((volume.restrict (Ioc c d)).withDensity _).restrict _ = (volume.restrict (Ioc c b)).withDensity _
  rw [restrict_withDensity measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic,Iic_inter_Ioc_of_le hbd]

theorem draw_cut {c b d : ℝ} (hc : 0 < c) (hcb : c ≤ b) (hbd : b ≤ d) (hcd : c < d) (a : ℝ) :
    ((draw hc hcd.le a (Iic b)):ℝ) = VacuumCalibration.mass c b a / VacuumCalibration.mass c d a := by
  have h := congrArg (fun μ : Measure ℝ => μ univ) (intensity_cut hc hcb hbd a)
  rw [Measure.restrict_apply_univ] at h
  have he : intensity hc hcd.le a (Iic b) = (intensity hc hcb a).mass := by
    apply ENNReal.coe_injective
    simpa only [FiniteMeasure.mass,FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using h
  rw [draw,FiniteMeasure.normalize_eq_of_nonzero _ (intensity_ne_zero hc hcd a),he,
    NNReal.coe_mul,NNReal.coe_inv,intensity_mass,intensity_mass,div_eq_inv_mul]

private theorem draw_open_closed {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a b : ℝ) :
    draw hc hcd.le a (Iio b) = draw hc hcd.le a (Iic b) := by
  rw [draw,FiniteMeasure.normalize_eq_of_nonzero _ (intensity_ne_zero hc hcd a),
    FiniteMeasure.normalize_eq_of_nonzero _ (intensity_ne_zero hc hcd a)]
  congr 1
  apply ENNReal.coe_injective
  simp only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change (volume.restrict (Ioc c d)).withDensity _ (Iio b) = (volume.restrict (Ioc c d)).withDensity _ (Iic b)
  exact measure_congr Iio_ae_eq_Iic

/-- Event that every observed mode belongs to the same set. -/
def allIn (k : ℕ) (B : Set ℝ) : Set (Fin k → ℝ) := univ.pi fun _ => B

/-- Reordering cannot change membership of every coordinate in the same set. -/
theorem orderStatistics_allIn (k : ℕ) (μ : ProbabilityMeasure ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    orderStatistics k μ (allIn k B) = (μ B)^k := by
  have hs : sortedTuple ⁻¹' allIn k B = allIn k B := by
    ext v
    change (∀ i ∈ (univ : Set (Fin k)), v (Tuple.sort v i) ∈ B) ↔ ∀ i ∈ (univ : Set (Fin k)), v i ∈ B
    simp only [Set.mem_univ,forall_const]
    constructor
    · intro h i
      obtain ⟨j,rfl⟩ := (Tuple.sort v).surjective i
      exact h j
    · exact fun h i => h _
  have hm : MeasurableSet (allIn k B) := MeasurableSet.univ_pi fun _ => hB
  rw [orderStatistics,ProbabilityMeasure.map_apply _ _ hm,hs]
  change ProbabilityMeasure.pi (fun _ : Fin k => μ) _ = _
  simp only [allIn,ProbabilityMeasure.pi_pi,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- The complete conditional distribution function of the largest observed energy, including the empty tuple. -/
theorem all_below_limit {c b d : ℝ} (hc : 0 < c) (hcb : c ≤ b) (hbd : b ≤ d)
    (hcd : c < d) (a : ℝ) (k : ℕ) :
    Tendsto (fun h => (conditional c d a h k (allIn k (Iic b)):ℝ)) criticalApproach
      (𝓝 ((VacuumCalibration.mass c b a / VacuumCalibration.mass c d a)^k)) := by
  let μ := orderStatistics k (draw hc hcd.le a)
  let C := allIn k (Iic b)
  let O := allIn k (Iio b)
  have hC : IsClosed C := isClosed_set_pi fun _ _ => isClosed_Iic
  have hO : IsOpen O := isOpen_set_pi (Set.toFinite _) fun _ _ => isOpen_Iio
  have hOC : O ⊆ C := by
    intro v hv i hi
    change v i ≤ b
    exact (show v i < b from hv i hi).le
  have he : μ O = μ C := by
    change orderStatistics _ _ _ = orderStatistics _ _ _
    rw [orderStatistics_allIn _ _ measurableSet_Iio,orderStatistics_allIn _ _ measurableSet_Iic,draw_open_closed hc hcd a b]
  have hh : (μ : Measure _) (frontier C) = 0 := by
    have hi := interior_maximal hOC hO
    apply measure_mono_null (show frontier C ⊆ C \ O by
      rw [frontier,hC.closure_eq]
      exact fun _ hz => ⟨hz.1,fun ho => hz.2 (hi ho)⟩)
    rw [measure_sdiff hOC hO.measurableSet.nullMeasurableSet (measure_ne_top _ _),
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      he,tsub_self]
  have hnull : μ (frontier C) = 0 := by
    apply ENNReal.coe_injective
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hh,ENNReal.coe_zero]
  have H := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto (E := C) (conditional_limit hc hcd a k) hnull
  have T := (NNReal.continuous_coe.tendsto _).comp H
  change Tendsto _ _ (𝓝 ((orderStatistics k (draw hc hcd.le a) (allIn k (Iic b)):ℝ≥0):ℝ)) at T
  rwa [orderStatistics_allIn _ _ measurableSet_Iic,NNReal.coe_pow,draw_cut hc hcb hbd hcd] at T

/-- At isometric damping, the conditional maximum has the log-uniform order-statistic law. -/
theorem critical_all_below_limit {c b d : ℝ} (hc : 0 < c) (hcb : c ≤ b) (hbd : b ≤ d)
    (hcd : c < d) (k : ℕ) :
    Tendsto (fun h => (conditional c d 0 h k (allIn k (Iic b)):ℝ)) criticalApproach
      (𝓝 ((Real.log (b/c)/Real.log (d/c))^k)) := by
  have hm {t : ℝ} (ht : 0 < t) : VacuumCalibration.mass c t 0 = Real.log (t/c) := by
    simp only [VacuumCalibration.mass,neg_zero,zero_mul,Real.exp_zero,integral_one_div_of_pos hc ht]
  simpa only [hm (hc.trans_le hcb),hm (hc.trans hcd)] using all_below_limit hc hcb hbd hcd 0 k

#print axioms critical_all_below_limit
#print axioms intensity_cut
#print axioms draw_cut
#print axioms orderStatistics_allIn
#print axioms all_below_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount
