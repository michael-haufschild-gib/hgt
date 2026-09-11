import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyMeanSquare
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyCoefficient
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FunProp
open Complex Set
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section CompletedBessel
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem packet_coefficient [DecidableEq I] (v : I → E) (g : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, g i (v j) = if i = j then 1 else 0)
    (t : Finset I) (c : I → ℂ) (i : I) :
    g i (∑ j ∈ t, c j • v j) = if i ∈ t then c i else 0 := by
  classical
  simp only [map_sum, map_smul, smul_eq_mul, hd, mul_ite, mul_one, mul_zero]
  simp

private theorem supported_nonnegative_sum_le [DecidableEq I] (f : I → ℝ)
    (hf : ∀ i, 0 ≤ f i) (t : Finset I) (hz : ∀ i ∉ t, f i = 0) (s : Finset I) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ t, f i := by
  calc
    ∑ i ∈ s, f i ≤ ∑ i ∈ s ∪ t, f i :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun i hi hni => hf i)
    _ = ∑ i ∈ t, f i :=
      (Finset.sum_subset Finset.subset_union_right (fun i hi hni => hz i hni)).symm

private theorem selected_packet_bound [DecidableEq I] (v : I → E) (g : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, g i (v j) = if i = j then 1 else 0)
    (hb : ∀ (t : Finset I) (c : I → ℂ),
      ∑ i ∈ t, ‖c i‖ ^ 2 ≤ ‖∑ i ∈ t, c i • v i‖ ^ 2)
    (t : Finset I) (c : I → ℂ) (s : Finset I) :
    ∑ i ∈ s, ‖g i (∑ j ∈ t, c j • v j)‖ ^ 2 ≤ ‖∑ j ∈ t, c j • v j‖ ^ 2 := by
  classical
  let w := ∑ j ∈ t, c j • v j
  have he : ∀ i, g i w = if i ∈ t then c i else 0 := packet_coefficient v g hd t c
  have hz : ∀ i ∉ t, ‖g i w‖ ^ 2 = 0 := by
    intro i hi
    rw [he, if_neg hi, norm_zero]
    ring
  calc
    ∑ i ∈ s, ‖g i w‖ ^ 2 ≤ ∑ i ∈ t, ‖g i w‖ ^ 2 :=
      supported_nonnegative_sum_le (fun i => ‖g i w‖ ^ 2) (fun i => sq_nonneg _) t hz s
    _ = ∑ i ∈ t, ‖c i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [he, if_pos hi]
    _ ≤ ‖w‖ ^ 2 := hb t c

private theorem finite_core_bessel [DecidableEq I] (v : I → E) (g : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, g i (v j) = if i = j then 1 else 0)
    (hb : ∀ (t : Finset I) (c : I → ℂ),
      ∑ i ∈ t, ‖c i‖ ^ 2 ≤ ‖∑ i ∈ t, c i • v i‖ ^ 2)
    (s : Finset I) {u : E} (hu : u ∈ Submodule.span ℂ (Set.range v)) :
    ∑ i ∈ s, ‖g i u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hu
  change (∑ i ∈ c.support, c i • v i) = u at hc
  have hp := selected_packet_bound v g hd hb c.support c s
  exact hc ▸ hp

private theorem completed_core_bessel [DecidableEq I] (v : I → E) (g : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, g i (v j) = if i = j then 1 else 0)
    (hb : ∀ (t : Finset I) (c : I → ℂ),
      ∑ i ∈ t, ‖c i‖ ^ 2 ≤ ‖∑ i ∈ t, c i • v i‖ ^ 2)
    (s : Finset I) {u : E} (hu : u ∈ closure (Submodule.span ℂ (Set.range v) : Set E)) :
    ∑ i ∈ s, ‖g i u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have hc : IsClosed {u : E | ∑ i ∈ s, ‖g i u‖ ^ 2 ≤ ‖u‖ ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact hc.closure_subset_iff.mpr (fun u hu => finite_core_bessel v g hd hb s hu) hu

private theorem extend_coefficient_family (D : Submodule ℂ E) (a : I → D →L[ℂ] ℂ) :
    ∃ g : I → E →L[ℂ] ℂ, ∀ i (u : D), g i u.val = a i u := by
  classical
  choose g hg hn using (fun i => exists_extension_norm_eq D (a i))
  exact ⟨g, hg⟩
private theorem subtype_completed_bessel [DecidableEq I]
    (D : Submodule ℂ E) (v : I → D) (a : I → D →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (hb : ∀ (t : Finset I) (c : I → ℂ),
      ∑ i ∈ t, ‖c i‖ ^ 2 ≤ ‖∑ i ∈ t, c i • (v i).val‖ ^ 2)
    (u : D) (hu : u.val ∈ closure (Submodule.span ℂ (Set.range (fun i => (v i).val)) : Set E))
    (s : Finset I) : ∑ i ∈ s, ‖a i u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  obtain ⟨g, hg⟩ := extend_coefficient_family D a
  have hgen : ∀ i j, g i (v j).val = if i = j then 1 else 0 := by
    intro i j
    exact (hg i (v j)).trans (hd i j)
  have h := completed_core_bessel (fun i => (v i).val) g hgen hb s hu
  simpa only [hg] using! h
end CompletedBessel
/-- Every finite selection of actual squared frequency amplitudes is bounded by
the squared norm of the completed bounded chain. -/
theorem causalFrequencyCoefficient_bessel (b : ℝ) (u : causalFrequencySpace b) (s : Finset ℝ) :
    ∑ ω ∈ s, ‖causalFrequencyCoefficient b ω u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
  subtype_completed_bessel (causalFrequencySpace b) (causalFrequencyMode b)
    (causalFrequencyCoefficient b) (causalFrequencyCoefficient_mode b)
    (causalFrequencyPacket_norm_sq_lower_bound b) u u.property s

/-- The full actual amplitude family is square summable over the real frequency
index, and its total squared amplitude does not exceed the squared chain norm. -/
theorem causalFrequencyCoefficient_summable_sq (b : ℝ) (u : causalFrequencySpace b) :
    Summable (fun ω : ℝ => ‖causalFrequencyCoefficient b ω u‖ ^ 2) ∧
      (∑' ω : ℝ, ‖causalFrequencyCoefficient b ω u‖ ^ 2) ≤ ‖u‖ ^ 2 := by
  exact ⟨summable_of_sum_le (fun ω => sq_nonneg _) (causalFrequencyCoefficient_bessel b u),
    Real.tsum_le_of_sum_le (fun ω => sq_nonneg _) (causalFrequencyCoefficient_bessel b u)⟩

end RHTower.FokasLenells
