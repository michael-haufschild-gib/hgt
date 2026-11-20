import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass
import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PairedRows

/-! # Density of prescribed two-site coefficient boxes along the Gaussian path -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section
abbrev PathPauliBlockLabel := Fin 2 × PathPauliDirections

/-- The two consecutive site rows in block k include both bonds incident on site 2k+1. -/
def pathPauliBlock (ω : PathPauliDisorder) (k : ℕ) (i : PathPauliBlockLabel) : ℝ :=
  ω (2*k+i.1.val,i.2)

private abbrev BlockField := PathPauliBlockLabel → ℝ
private def blockLaw : Measure BlockField := Measure.infinitePi fun _ => gaussianReal 0 1
private instance : IsProbabilityMeasure blockLaw := by unfold blockLaw; infer_instance
private def blockSeqLaw : Measure (ℕ → BlockField) := Measure.infinitePi fun _ => blockLaw

private theorem measurePreserving_pathPauliBlock :
    MeasurePreserving pathPauliBlock pathPauliDisorderLaw blockSeqLaw := by
  exact measurePreserving_paired_rows _

/-- Any nondegenerate coefficient box in a two-row block occurs with positive
limiting frequency along almost every single infinite Gaussian sample. -/
theorem gaussian_pauli_block_positive_density (lo hi : PathPauliBlockLabel → ℝ)
    (hbox : ∀ i, lo i < hi i) :
    ∃ p : ℝ, 0 < p ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ m : ℕ in atTop,
      p*m ≤ ((Finset.range m).filter (fun j => ∀ i, pathPauliBlock ω j i ∈ Icc (lo i) (hi i))).card := by
  classical
  let B : Set BlockField := univ.pi fun i => Icc (lo i) (hi i)
  have hB : MeasurableSet B := MeasurableSet.pi (Set.to_countable _) fun _ _ => measurableSet_Icc
  have hp : 0 < blockLaw B := by
    simp only [blockLaw,Measure.infinitePi_eq_pi,B,Measure.pi_pi]
    rw [pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (gaussianReal_Icc_pos (hbox i)).ne'
  let f := B.indicator (fun _ : BlockField => (1:ℝ))
  have hf : Measurable f := measurable_const.indicator hB
  have hint : Integrable f blockLaw := (integrable_const 1).indicator hB
  let X (j : ℕ) (ω : ℕ → BlockField) := f (ω j)
  have hid (j : ℕ) : IdentDistrib (X j) f blockSeqLaw blockLaw := by
    have hm := measurePreserving_eval_infinitePi (fun _ : ℕ => blockLaw) j
    have h : IdentDistrib (Function.eval j) id blockSeqLaw blockLaw :=
      ⟨hm.measurable.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact hm.map_eq⟩
    exact h.comp hf
  have hind : iIndepFun X blockSeqLaw := iIndepFun_infinitePi (P := fun _ => blockLaw) (fun _ => hf)
  have hs := strong_law_ae_real X ((hid 0).integrable_iff.mpr hint)
    (fun _ _ h => hind.indepFun h) (fun j => (hid j).trans (hid 0).symm)
  rw [(hid 0).integral_eq,show (∫ x, f x ∂blockLaw) = blockLaw.real B by
    simp [f,integral_indicator hB,Measure.real]] at hs
  have hpos : 0 < blockLaw.real B := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  refine ⟨blockLaw.real B/2,by positivity,?_⟩
  filter_upwards [measurePreserving_pathPauliBlock.quasiMeasurePreserving.ae hs] with ω hω
  filter_upwards [hω.eventually_const_lt (show blockLaw.real B/2 < blockLaw.real B by linarith),
    eventually_ge_atTop 1] with m hm hmpos
  have hcard : (∑ j ∈ Finset.range m, X j (pathPauliBlock ω)) =
      (((Finset.range m).filter (fun j => ∀ i, pathPauliBlock ω j i ∈ Icc (lo i) (hi i))).card : ℝ) := by
    have hmem (x : BlockField) : x ∈ B ↔ ∀ i, x i ∈ Icc (lo i) (hi i) := Set.mem_univ_pi
    simp only [X,f,Set.indicator_apply,hmem,Finset.sum_boole]
  rw [hcard] at hm
  exact ((lt_div_iff₀ (show 0 < (m:ℝ) by exact_mod_cast (by omega : 0 < m))).mp hm).le

#print axioms gaussian_pauli_block_positive_density
end
end GaloisForLFunctions.HTGeometry
