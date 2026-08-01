import GaloisForLFunctions.RHTower.PrimeArchObservableCarrierQuantization
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Measure.Support

/-!
# No continuous theta reporter for the Route D Xi carrier

The canonically mass-calibrated theta-cusp source has full measure-theoretic support on `(0, ∞)`
and exactly the required zeroth moment, whereas the canonical Xi moment law is carried by a compact
countable set of positive thermal nodes accumulating at zero.  Consequently, a reporter continuous
on `(0, ∞)` cannot realize that law: continuity and full source support trap its connected image
inside the countable carrier, so the reporter is constant, while the canonical law has more than
one positive atom.

This is an unconditional regularity boundary for Route D.  It does not obstruct arbitrary
measurable step reporters; it isolates the discontinuous plateau quotient that a genuine
prime--archimedean construction must produce rather than import from the target law.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace RHTower

noncomputable section

/-- The enumerated positive Xi thermal nodes converge to zero. -/
theorem tendsto_xiThermalNode_enumeration_zero :
    Tendsto (fun j : ℕ => xiThermalNode (xiThermalEnumeration j))
      atTop (nhds 0) := by
  simpa only [Nat.zero_add, pow_one] using
    (hasSum_xiThermalEnumeration_positiveMoment 0).summable.tendsto_atTop_zero

/-- Compact carrier containing zero and every enumerated positive Xi thermal node. -/
def xiThermalCompactNodeSet : Set ℝ :=
  insert 0 (range fun j : ℕ => xiThermalNode (xiThermalEnumeration j))

theorem xiThermalCompactNodeSet_countable :
    xiThermalCompactNodeSet.Countable := by
  exact (Set.countable_range
    (fun j : ℕ => xiThermalNode (xiThermalEnumeration j))).insert 0

theorem xiThermalCompactNodeSet_isCompact :
    IsCompact xiThermalCompactNodeSet := by
  exact tendsto_xiThermalNode_enumeration_zero.isCompact_insert_range

theorem xiThermalCompactNodeSet_isClosed :
    IsClosed xiThermalCompactNodeSet :=
  xiThermalCompactNodeSet_isCompact.isClosed

/-- The canonical compact Xi moment measure is almost everywhere carried by the thermal node set. -/
theorem ae_primeArchXiCompactMomentMeasure_mem_xiThermalCompactNodeSet :
    ∀ᵐ x : ℝ ∂primeArchXiCompactMomentMeasure,
      x ∈ xiThermalCompactNodeSet := by
  rw [primeArchXiCompactMomentMeasure, Measure.ae_sum_iff]
  intro j
  apply Measure.ae_smul_measure
  unfold xiThermalCompactNodeSet
  exact (mem_ae_dirac_iff xiThermalCompactNodeSet_isClosed.measurableSet).mpr
    (mem_insert_iff.mpr (Or.inr ⟨j, rfl⟩))

theorem primeArchXiCompactMomentMeasure_compl_xiThermalCompactNodeSet_eq_zero :
    primeArchXiCompactMomentMeasure xiThermalCompactNodeSetᶜ = 0 := by
  exact mem_ae_iff.mp
    ae_primeArchXiCompactMomentMeasure_mem_xiThermalCompactNodeSet

private theorem measurable_thetaCuspContinuousDensity :
    Measurable (fun x : ℝ => ENNReal.ofReal
      (thetaCuspContinuousSourceScale * (2 * thetaCuspFullSource x))) := by
  exact ENNReal.measurable_ofReal.comp
    continuous_thetaCuspContinuousSourceDensity.measurable

/-- Strict positivity of the theta density makes restricted Lebesgue measure absolutely
continuous with respect to the theta-cusp source, the converse of the existing easy direction. -/
theorem volume_restrict_Ioi_absolutelyContinuous_thetaCuspContinuousSourceMeasure :
    (volume.restrict (Ioi 0) : Measure ℝ) ≪
      thetaCuspContinuousSourceMeasure := by
  unfold thetaCuspContinuousSourceMeasure
  apply withDensity_absolutelyContinuous'
  · exact measurable_thetaCuspContinuousDensity.aemeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (mul_pos thetaCuspContinuousSourceScale_pos
        (mul_pos (by norm_num) (thetaCuspFullSource_pos_of_pos hx)))

theorem ae_thetaCuspContinuousSourceMeasure_mem_Ioi :
    ∀ᵐ x : ℝ ∂thetaCuspContinuousSourceMeasure, x ∈ Ioi 0 := by
  unfold thetaCuspContinuousSourceMeasure
  rw [ae_withDensity_iff measurable_thetaCuspContinuousDensity]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact fun _ => hx

/-- Every open set meeting `(0, ∞)` has positive theta-cusp source mass. -/
theorem thetaCuspContinuousSourceMeasure_pos_of_isOpen_inter_Ioi_nonempty
    {U : Set ℝ} (hU : IsOpen U) (hne : (U ∩ Ioi 0).Nonempty) :
    0 < thetaCuspContinuousSourceMeasure U := by
  have hvol : 0 < volume (U ∩ Ioi 0) :=
    (hU.inter isOpen_Ioi).measure_pos volume hne
  have hbase : 0 < (volume.restrict (Ioi 0) : Measure ℝ) U := by
    rw [Measure.restrict_apply hU.measurableSet]
    exact hvol
  apply lt_of_not_ge
  intro hle
  have hzero : thetaCuspContinuousSourceMeasure U = 0 := bot_unique hle
  exact (ne_of_gt hbase)
    (volume_restrict_Ioi_absolutelyContinuous_thetaCuspContinuousSourceMeasure hzero)

/-- A countable preconnected subset of the real line is a singleton. -/
theorem countable_isPreconnected_subsingleton_real {s : Set ℝ}
    (hc : s.Countable) (hp : IsPreconnected s) : s.Subsingleton := by
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · have hI : (Icc x y).Countable := hc.mono (hp.Icc_subset hx hy)
    exact le_antisymm hxy (Cardinal.Real.Icc_countable_iff.mp hI)
  · have hI : (Icc y x).Countable := hc.mono (hp.Icc_subset hy hx)
    exact le_antisymm (Cardinal.Real.Icc_countable_iff.mp hI) hyx

/-- Full theta support and exact pushforward rigidity force every value of a continuous reporter
on `(0, ∞)` into the compact countable Xi carrier. -/
theorem IsPrimeArchObservableWitness.image_Ioi_subset_xiThermalCompactNodeSet
    {node : ℝ → ℝ}
    (h : IsPrimeArchObservableWitness thetaCuspContinuousSourceMeasure node)
    (hcont : ContinuousOn node (Ioi 0)) :
    node '' Ioi 0 ⊆ xiThermalCompactNodeSet := by
  rintro y ⟨x, hx, rfl⟩
  by_contra hxK
  let U := Ioi 0 ∩ node ⁻¹' xiThermalCompactNodeSetᶜ
  have hUopen : IsOpen U :=
    hcont.isOpen_inter_preimage isOpen_Ioi
      xiThermalCompactNodeSet_isClosed.isOpen_compl
  have hxU : x ∈ U := by
    exact ⟨hx, hxK⟩
  have hpos : 0 < thetaCuspContinuousSourceMeasure U :=
    thetaCuspContinuousSourceMeasure_pos_of_isOpen_inter_Ioi_nonempty
      hUopen ⟨x, hxU, hx⟩
  have hprezero :
      thetaCuspContinuousSourceMeasure
          (node ⁻¹' xiThermalCompactNodeSetᶜ) = 0 := by
    have hmap := congrArg (fun mu : Measure ℝ => mu xiThermalCompactNodeSetᶜ)
      h.pushforward_eq_primeArchXiCompactMomentMeasure
    rw [HTGeometry.observablePushforwardMeasure,
      Measure.map_apply h.1
        xiThermalCompactNodeSet_isClosed.isOpen_compl.measurableSet,
      primeArchXiCompactMomentMeasure_compl_xiThermalCompactNodeSet_eq_zero]
      at hmap
    exact hmap
  exact (ne_of_gt hpos) (measure_mono_null inter_subset_right hprezero)

/-- A successful reporter continuous on `(0, ∞)` would have singleton image there. -/
theorem IsPrimeArchObservableWitness.image_Ioi_subsingleton
    {node : ℝ → ℝ}
    (h : IsPrimeArchObservableWitness thetaCuspContinuousSourceMeasure node)
    (hcont : ContinuousOn node (Ioi 0)) :
    (node '' Ioi 0).Subsingleton := by
  apply countable_isPreconnected_subsingleton_real
  · exact xiThermalCompactNodeSet_countable.mono
      (h.image_Ioi_subset_xiThermalCompactNodeSet hcont)
  · exact isPreconnected_Ioi.image node hcont

theorem IsPrimeArchObservableWitness.eq_on_Ioi_of_continuousOn
    {node : ℝ → ℝ}
    (h : IsPrimeArchObservableWitness thetaCuspContinuousSourceMeasure node)
    (hcont : ContinuousOn node (Ioi 0))
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    node x = node y := by
  exact h.image_Ioi_subsingleton hcont ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

/-- The positive thermal-node enumeration is not constant: its summable values tend to zero. -/
theorem exists_xiThermalNode_enumeration_ne (c : ℝ) :
    ∃ j : ℕ, xiThermalNode (xiThermalEnumeration j) ≠ c := by
  by_contra! h
  have heq :
      (fun j : ℕ => xiThermalNode (xiThermalEnumeration j)) = fun _ => c :=
    funext h
  have ht := tendsto_xiThermalNode_enumeration_zero
  rw [heq] at ht
  have hc : c = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  exact (xiThermalNode_pos (xiThermalEnumeration 0)).ne' ((h 0).trans hc)

/-- **Continuous theta-reporter no-go.** No reporter continuous on the positive theta half-line
can realize every normalized prime--archimedean moment. -/
theorem not_isPrimeArchObservableWitness_thetaCusp_of_continuousOn_Ioi
    {node : ℝ → ℝ} (hcont : ContinuousOn node (Ioi 0)) :
    ¬ IsPrimeArchObservableWitness thetaCuspContinuousSourceMeasure node := by
  intro h
  obtain ⟨j, hj⟩ := exists_xiThermalNode_enumeration_ne (node 1)
  have hfib := h.measure_levelSet_xiThermalNode_pos j
  have hinter :
      0 < thetaCuspContinuousSourceMeasure
        (Ioi 0 ∩ node ⁻¹' {xiThermalNode (xiThermalEnumeration j)}) := by
    rw [Measure.measure_inter_eq_of_ae
      ae_thetaCuspContinuousSourceMeasure_mem_Ioi]
    exact hfib
  obtain ⟨x, hxIoi, hxfiber⟩ := nonempty_of_measure_ne_zero hinter.ne'
  simp only [mem_preimage, mem_singleton_iff] at hxfiber
  have hconst := h.eq_on_Ioi_of_continuousOn hcont hxIoi zero_lt_one
  exact hj (hxfiber.symm.trans hconst)

end

end RHTower
