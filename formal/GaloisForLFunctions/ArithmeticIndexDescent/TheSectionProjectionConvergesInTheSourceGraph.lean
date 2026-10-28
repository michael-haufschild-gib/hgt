import GaloisForLFunctions.ArithmeticIndexDescent.TheGraphNormIsControlledBySectionEnergy
import GaloisForLFunctions.ArithmeticIndexDescent.TheSectionProjectionHasACanonicalLimit
import GaloisForLFunctions.RHTower.CHMDBirmanSchwingerBound

/-!
# The canonical arithmetic projection is an actual complete source vector

The full source graph norm is controlled by arithmetic section energy on the
fixed old window. Pythagorean increments therefore make the finite projections
Cauchy in the actual complete graph. Their limit lies in the closure of the old
source space and realizes the previously constructed removal energy and every
mixed removal pairing in the original complete Weil form.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics

private theorem graphWeilPair_eq_three_diagonals (p q : SourceGraph) :
    weilBilin p q = (weilForm p + weilForm q - weilForm (p - q)) / 2 := by
  simp only [weilForm_eq_weilBilin, weilBilin_sub_left, weilBilin_sub_right]
  rw [weilBilin_comm q p]
  ring

/-- The literal test lift preserves every mixed full Weil reading. -/
theorem weilBilin_realTestGraphLift (f g : realTests) :
    weilBilin (realTestGraphLift f) (realTestGraphLift g) = realWeilForm f g := by
  rw [graphWeilPair_eq_three_diagonals, ← realTestGraphLift_sub]
  simp only [weilForm_realTestGraphLift, map_sub, LinearMap.sub_apply]
  rw [realWeilForm_symm g f]
  ring

private theorem continuous_graphWeilPair :
    Continuous (fun p : SourceGraph × SourceGraph => weilBilin p.1 p.2) := by
  have he : (fun p : SourceGraph × SourceGraph => weilBilin p.1 p.2) =
      fun p => (weilForm p.1 + weilForm p.2 - weilForm (p.1 - p.2)) / 2 :=
    funext fun p => graphWeilPair_eq_three_diagonals p.1 p.2
  rw [he]
  exact (((continuous_weilForm.comp continuous_fst).add
    (continuous_weilForm.comp continuous_snd)).sub
      (continuous_weilForm.comp (continuous_fst.sub continuous_snd))).div_const 2

private theorem continuous_graphWeilPair_fixed (p : SourceGraph) :
    Continuous (fun q : SourceGraph => weilBilin q p) := by
  have hpair : Continuous (fun q : SourceGraph => (q, p)) :=
    (continuous_id : Continuous (fun q : SourceGraph => q)).prodMk continuous_const
  have hcomp := continuous_graphWeilPair.comp hpair
  simpa only [Function.comp_def] using hcomp

variable {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
  (hw : w ≤ fullSectionRatio * atomSpacing N)

include hN hw0 hw

/-- The closed old source carrier retains a quantitative positive Weil floor
in the actual graph norm. -/
theorem exists_closedSection_graphNorm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ p : SourceGraph,
      p ∈ closure (Set.range (fun q : arithmeticSectionTests N w => realTestGraphLift q.1)) →
      ‖p‖ ^ 2 ≤ C * weilForm p := by
  obtain ⟨C, hC, hbound⟩ := exists_arithmeticSection_graphNorm_bound hN hw0 hw
  refine ⟨C, hC, ?_⟩
  have hc : IsClosed {p : SourceGraph | ‖p‖ ^ 2 ≤ C * weilForm p} :=
    isClosed_le (continuous_norm.pow 2) (continuous_weilForm.const_mul C)
  have hr : Set.range (fun q : arithmeticSectionTests N w => realTestGraphLift q.1) ⊆
      {p : SourceGraph | ‖p‖ ^ 2 ≤ C * weilForm p} := by
    rintro _ ⟨q, rfl⟩
    change ‖realTestGraphLift q.1‖ ^ 2 ≤ C * weilForm (realTestGraphLift q.1)
    rw [weilForm_realTestGraphLift]
    exact hbound q
  exact fun p hp => closure_minimal hr hc hp

/-- The finite source projections are Cauchy in their actual Weil energy. -/
theorem finiteSectionProjection_weil_energy_cauchy (g : realTests) {ε : ℝ} (hε : 0 < ε) :
    ∃ S₀ : Finset (arithmeticSectionTests N w),
      ∀ S T : Finset (arithmeticSectionTests N w), S₀ ⊆ S → S₀ ⊆ T →
        realWeilForm
          (finiteSectionProjection hN hw0 hw S g - finiteSectionProjection hN hw0 hw T g)
          (finiteSectionProjection hN hw0 hw S g - finiteSectionProjection hN hw0 hw T g) < ε := by
  obtain ⟨S₀, hS₀⟩ := exists_lt_of_lt_ciSup
    (show sectionCompletionEnergy hN hw0 hw g - ε / 4 <
      ⨆ S : Finset (arithmeticSectionTests N w), finiteSectionEnergy hN hw0 hw S g by
        change sectionCompletionEnergy hN hw0 hw g - ε / 4 <
          sectionCompletionEnergy hN hw0 hw g
        linarith only [hε])
  refine ⟨S₀, ?_⟩
  intro S T hS hT
  let p := finiteSectionProjection hN hw0 hw S g
  let q := finiteSectionProjection hN hw0 hw T g
  let r := finiteSectionProjection hN hw0 hw S₀ g
  have hp := finiteSectionProjection_mem hN hw0 hw S g
  have hq := finiteSectionProjection_mem hN hw0 hw T g
  have hr := finiteSectionProjection_mem hN hw0 hw S₀ g
  have ha := (arithmeticSectionTests N w).sub_mem hp hr
  have hb := (arithmeticSectionTests N w).sub_mem hq hr
  have hfloor := integral_sq_le_weilPair_arithmeticSection hN hw0 hw
    ⟨(p - r) + (q - r), (arithmeticSectionTests N w).add_mem ha hb⟩
  have hnonneg : 0 ≤ realWeilForm ((p - r) + (q - r)) ((p - r) + (q - r)) :=
    (integral_nonneg fun u => sq_nonneg (((p - r) + (q - r)).1 u)).trans hfloor
  have hpar : realWeilForm (p - q) (p - q) +
      realWeilForm ((p - r) + (q - r)) ((p - r) + (q - r)) =
      2 * realWeilForm (p - r) (p - r) + 2 * realWeilForm (q - r) (q - r) := by
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply]
    ring
  have hpinc := finiteSectionProjection_increment hN hw0 hw hS g
  have hqinc := finiteSectionProjection_increment hN hw0 hw hT g
  have hpbound := finiteSectionEnergy_le_completion hN hw0 hw S g
  have hqbound := finiteSectionEnergy_le_completion hN hw0 hw T g
  change realWeilForm (p - r) (p - r) = _ at hpinc
  change realWeilForm (q - r) (q - r) = _ at hqinc
  change realWeilForm (p - q) (p - q) < ε
  linarith only [hnonneg, hpar, hpinc, hqinc, hpbound, hqbound, hS₀]

/-- The whole finite-subset net converges in graph norm, not merely square mass. -/
theorem finiteSectionGraphProjection_cauchy (g : realTests) :
    CauchySeq (fun S : Finset (arithmeticSectionTests N w) =>
      realTestGraphLift (finiteSectionProjection hN hw0 hw S g)) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_arithmeticSection_graphNorm_bound hN hw0 hw
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨S₀, hS₀⟩ := finiteSectionProjection_weil_energy_cauchy hN hw0 hw g
    (ε := ε ^ 2 / C) (by positivity)
  refine ⟨S₀, ?_⟩
  intro S hS T hT
  let p := finiteSectionProjection hN hw0 hw S g
  let q := finiteSectionProjection hN hw0 hw T g
  have hpq := (arithmeticSectionTests N w).sub_mem
    (finiteSectionProjection_mem hN hw0 hw S g) (finiteSectionProjection_mem hN hw0 hw T g)
  have hn := hbound ⟨p - q, hpq⟩
  have he := mul_lt_mul_of_pos_left (hS₀ S T hS hT) hC
  have hc : C * (ε ^ 2 / C) = ε ^ 2 := by field_simp [ne_of_gt hC]
  rw [hc] at he
  change C * realWeilForm (p - q) (p - q) < ε ^ 2 at he
  rw [dist_eq_norm, ← realTestGraphLift_sub]
  change ‖realTestGraphLift (p - q)‖ < ε
  change ‖realTestGraphLift (p - q)‖ ^ 2 ≤ C * realWeilForm (p - q) (p - q) at hn
  nlinarith only [hn, he, hε]

/-- An actual complete source vector realizes the canonical section projection. -/
theorem exists_sectionGraphProjection (g : realTests) :
    ∃ p : SourceGraph,
      Tendsto (fun S : Finset (arithmeticSectionTests N w) =>
        realTestGraphLift (finiteSectionProjection hN hw0 hw S g)) atTop (𝓝 p) :=
  cauchySeq_tendsto_of_complete (finiteSectionGraphProjection_cauchy hN hw0 hw g)

/-- The canonical old-section projection, as a vector in the original complete source graph. -/
def sectionGraphProjection (g : realTests) : SourceGraph :=
  Classical.choose (exists_sectionGraphProjection hN hw0 hw g)

theorem tendsto_sectionGraphProjection (g : realTests) :
    Tendsto (fun S : Finset (arithmeticSectionTests N w) =>
      realTestGraphLift (finiteSectionProjection hN hw0 hw S g)) atTop
        (𝓝 (sectionGraphProjection hN hw0 hw g)) :=
  Classical.choose_spec (exists_sectionGraphProjection hN hw0 hw g)

/-- Completion remains in the closure of the literal arithmetic source space. -/
theorem sectionGraphProjection_mem_closure (g : realTests) :
    sectionGraphProjection hN hw0 hw g ∈
      closure (Set.range (fun p : arithmeticSectionTests N w => realTestGraphLift p.1)) := by
  apply isClosed_closure.mem_of_tendsto (tendsto_sectionGraphProjection hN hw0 hw g)
  exact Eventually.of_forall fun S => subset_closure
    ⟨⟨finiteSectionProjection hN hw0 hw S g,
      finiteSectionProjection_mem hN hw0 hw S g⟩, rfl⟩

/-- Its original full Weil energy is exactly the completed removal energy. -/
theorem weilForm_sectionGraphProjection (g : realTests) :
    weilForm (sectionGraphProjection hN hw0 hw g) = sectionCompletionEnergy hN hw0 hw g := by
  have ht := (continuous_weilForm.tendsto (sectionGraphProjection hN hw0 hw g)).comp
    (tendsto_sectionGraphProjection hN hw0 hw g)
  have ht' : Tendsto (fun S : Finset (arithmeticSectionTests N w) =>
      finiteSectionEnergy hN hw0 hw S g) atTop
      (𝓝 (weilForm (sectionGraphProjection hN hw0 hw g))) := by
    simpa only [Function.comp_def, weilForm_realTestGraphLift, finiteSectionEnergy] using ht
  exact tendsto_nhds_unique ht' (tendsto_finiteSectionEnergy hN hw0 hw g)

/-- Every mixed completed removal entry is the literal Weil pairing of graph limits. -/
theorem weilBilin_sectionGraphProjection (g h : realTests) :
    weilBilin (sectionGraphProjection hN hw0 hw g) (sectionGraphProjection hN hw0 hw h) =
      sectionCompletionPair hN hw0 hw g h := by
  have ht := (continuous_graphWeilPair.tendsto
    (sectionGraphProjection hN hw0 hw g, sectionGraphProjection hN hw0 hw h)).comp
      ((tendsto_sectionGraphProjection hN hw0 hw g).prodMk_nhds
        (tendsto_sectionGraphProjection hN hw0 hw h))
  have ht' : Tendsto (fun S : Finset (arithmeticSectionTests N w) =>
      realWeilForm (finiteSectionProjection hN hw0 hw S g)
        (finiteSectionProjection hN hw0 hw S h)) atTop
      (𝓝 (weilBilin (sectionGraphProjection hN hw0 hw g)
        (sectionGraphProjection hN hw0 hw h))) := by
    simpa only [Function.comp_def, weilBilin_realTestGraphLift] using ht
  exact tendsto_nhds_unique ht' (tendsto_finiteSectionProjection_pair hN hw0 hw g h)

/-- The signed complement is an actual vector of the original complete source graph. -/
def sectionGraphResidual (g : realTests) : SourceGraph :=
  realTestGraphLift g - sectionGraphProjection hN hw0 hw g

theorem tendsto_sectionGraphResidual (g : realTests) :
    Tendsto (fun S : Finset (arithmeticSectionTests N w) =>
      realTestGraphLift (g - finiteSectionProjection hN hw0 hw S g)) atTop
        (𝓝 (sectionGraphResidual hN hw0 hw g)) := by
  have hc : Tendsto (fun _ : Finset (arithmeticSectionTests N w) => realTestGraphLift g)
      atTop (𝓝 (realTestGraphLift g)) := tendsto_const_nhds
  simpa only [realTestGraphLift_sub, sectionGraphResidual] using
    hc.sub (tendsto_sectionGraphProjection hN hw0 hw g)

/-- The completed signed residual is exactly the original Weil pairing on actual
graph residuals; no replacement pairing or smoothness of the limit is imposed. -/
theorem weilBilin_sectionGraphResidual (g h : realTests) :
    weilBilin (sectionGraphResidual hN hw0 hw g) (sectionGraphResidual hN hw0 hw h) =
      completedSectionResidualForm hN hw0 hw g h := by
  have ht := (continuous_graphWeilPair.tendsto
    (sectionGraphResidual hN hw0 hw g, sectionGraphResidual hN hw0 hw h)).comp
      ((tendsto_sectionGraphResidual hN hw0 hw g).prodMk_nhds
        (tendsto_sectionGraphResidual hN hw0 hw h))
  have ht' : Tendsto (fun S : Finset (arithmeticSectionTests N w) =>
      realWeilForm (g - finiteSectionProjection hN hw0 hw S g)
        (h - finiteSectionProjection hN hw0 hw S h)) atTop
      (𝓝 (weilBilin (sectionGraphResidual hN hw0 hw g)
        (sectionGraphResidual hN hw0 hw h))) := by
    simpa only [Function.comp_def, weilBilin_realTestGraphLift] using ht
  exact tendsto_nhds_unique ht' (tendsto_finiteSectionProjection_residual_pair hN hw0 hw g h)

/-- Every old section is orthogonal to the actual graph residual. -/
theorem sectionGraphResidual_orthogonal_section (p : arithmeticSectionTests N w) (g : realTests) :
    weilBilin (realTestGraphLift p.1) (sectionGraphResidual hN hw0 hw g) = 0 := by
  classical
  have hc : Tendsto (fun _ : Finset (arithmeticSectionTests N w) => realTestGraphLift p.1)
      atTop (𝓝 (realTestGraphLift p.1)) := tendsto_const_nhds
  have ht := (continuous_graphWeilPair.tendsto
    (realTestGraphLift p.1, sectionGraphResidual hN hw0 hw g)).comp
      (hc.prodMk_nhds (tendsto_sectionGraphResidual hN hw0 hw g))
  have hevent : (fun S : Finset (arithmeticSectionTests N w) =>
      weilBilin (realTestGraphLift p.1)
        (realTestGraphLift (g - finiteSectionProjection hN hw0 hw S g))) =ᶠ[atTop]
      fun _ => (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop ({p} : Finset (arithmeticSectionTests N w))] with S hS
    have hp : p ∈ S := Finset.singleton_subset_iff.mp hS
    rw [weilBilin_realTestGraphLift]
    exact (arithmeticSectionProjection_spec hN hw0 hw (fun q : S => q.1) g).2 ⟨p, hp⟩
  exact tendsto_nhds_unique ht (Filter.Tendsto.congr' hevent.symm tendsto_const_nhds)

/-- Orthogonality extends to the closure of the entire old source space. -/
theorem sectionGraphResidual_orthogonal_closure {p : SourceGraph}
    (hp : p ∈ closure (Set.range
      (fun q : arithmeticSectionTests N w => realTestGraphLift q.1))) (g : realTests) :
    weilBilin p (sectionGraphResidual hN hw0 hw g) = 0 := by
  have hc := continuous_graphWeilPair_fixed (sectionGraphResidual hN hw0 hw g)
  have hz := isClosed_eq hc (continuous_const : Continuous (fun _ : SourceGraph => (0 : ℝ)))
  apply closure_minimal (t := {q : SourceGraph |
    weilBilin q (sectionGraphResidual hN hw0 hw g) = 0}) ?_ hz hp
  rintro _ ⟨q, rfl⟩
  exact sectionGraphResidual_orthogonal_section hN hw0 hw q g

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_sectionGraphProjection
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.weilForm_sectionGraphProjection
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.weilBilin_sectionGraphProjection
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.weilBilin_sectionGraphResidual
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.sectionGraphResidual_orthogonal_closure
