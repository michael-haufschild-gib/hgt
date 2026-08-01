import GaloisForLFunctions.RHTower.DeningerLocallyConstantFactor
import GaloisForLFunctions.RHTower.DeningerTransversePartition

/-!
# Locally constant sections are finite sums

A locally constant function on a compact profinite space with values in a module is a finite sum of
indicators of a clopen partition times constant values: it is constant on each piece of the
partition through which it factors, and the indicators of a partition sum to one.

So the locally constant sections over a profinite factor are the union of the finite direct sums
attached to the finite clopen partitions — every section already lives at a finite stage.

* `deningerLocallyConstant_eq_sum` : the finite-sum expansion.
-/

namespace RHTower

open Set

universe u v

section FiniteStage

variable {B : Type u} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  [TotallyDisconnectedSpace B] {V : Type v} [AddCommGroup V] [Module ℝ V]

/-- **A locally constant function is a finite sum of indicators times values.**  It factors through
a finite clopen partition, and on the piece containing a point only that indicator survives. -/
theorem deningerLocallyConstant_eq_sum {F : B → V} (hF : IsLocallyConstant F) :
    ∃ (ι : Type u) (_ : Fintype ι) (D : ι → Set B) (y : ι → V),
      (∀ a, IsClopen (D a)) ∧ (∀ b : B, ∃! a, b ∈ D a)
        ∧ ∀ b : B, F b = ∑ a, (D a).indicator (fun _ => (1 : ℝ)) b • y a := by
  classical
  obtain ⟨ι, hfin, D, hDclopen, hDpart, hDconst⟩ := deningerLocallyConstant_factors hF
  refine ⟨ι, hfin, D, fun a => if h : (D a).Nonempty then F h.choose else 0,
    hDclopen, hDpart, fun b => ?_⟩
  obtain ⟨a₀, ha₀, huniq⟩ := hDpart b
  rw [Finset.sum_eq_single a₀]
  · have hne : (D a₀).Nonempty := ⟨b, ha₀⟩
    rw [Set.indicator_of_mem ha₀, one_smul]
    dsimp only
    rw [dif_pos hne]
    exact hDconst a₀ b hne.choose ha₀ hne.choose_spec
  · intro a _ hane
    rw [Set.indicator_of_notMem, zero_smul]
    intro hmem
    exact hane (huniq a hmem)
  · intro h
    exact absurd (Finset.mem_univ a₀) h

end FiniteStage

end RHTower
