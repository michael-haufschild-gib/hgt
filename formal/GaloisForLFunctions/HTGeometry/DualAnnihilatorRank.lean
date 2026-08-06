import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Basic

/-!
# Comparing spans through their annihilators

If every covector annihilating one family annihilates a second family, the
span of the second is no larger than the span of the first.  This is the
dual-annihilator dimension formula in finite dimensions.

A linear functional on a finite coordinate space is the pairing with its
values on the standard basis, so the hypothesis can be stated with explicit
coordinate sums.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The dual annihilator comparison -/

/-- **Comparing dimensions through dual annihilators.** -/
theorem finrank_le_of_dualAnnihilator_le {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {U W : Submodule ℂ V}
    (h : W.dualAnnihilator ≤ U.dualAnnihilator) :
    Module.finrank ℂ U ≤ Module.finrank ℂ W := by
  have hU := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  have hW := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hle : Module.finrank ℂ (Submodule.dualAnnihilator W)
      ≤ Module.finrank ℂ (Submodule.dualAnnihilator U) := Submodule.finrank_mono h
  omega

/-! ### Functionals on a coordinate space -/

variable {d : Type} [Fintype d] [DecidableEq d]

theorem dual_apply_eq_sum (φ : Module.Dual ℂ (d → ℂ)) (v : d → ℂ) :
    φ v = ∑ j, v j * φ (Pi.single j 1) := by
  classical
  have hsingle : ∀ j : d,
      (fun j' : d => if j = j' then (1 : ℂ) else 0) = Pi.single j (1 : ℂ) := by
    intro j
    funext j'
    rw [Pi.single_apply]
    by_cases h : j' = j
    · simp [h]
    · simp [h, Ne.symm h]
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hsingle j, smul_eq_mul]

/-- **Span comparison from a coordinate annihilator hypothesis.** -/
theorem finrank_span_le_of_annihilator {S T : Set (d → ℂ)}
    (h : ∀ c : d → ℂ, (∀ v ∈ S, ∑ j, c j * v j = 0) →
      ∀ w ∈ T, ∑ j, c j * w j = 0) :
    Module.finrank ℂ (Submodule.span ℂ T)
      ≤ Module.finrank ℂ (Submodule.span ℂ S) := by
  refine finrank_le_of_dualAnnihilator_le ?_
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ ⊢
  have hS : ∀ v ∈ S, ∑ j, φ (Pi.single j 1) * v j = 0 := by
    intro v hv
    have hvz : φ v = 0 := hφ v (Submodule.subset_span hv)
    rw [dual_apply_eq_sum φ v] at hvz
    rw [← hvz]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hT := h (fun j => φ (Pi.single j 1)) hS
  intro w hw
  refine Submodule.span_induction (p := fun x _ => φ x = 0) ?_ ?_ ?_ ?_ hw
  · intro x hx
    have := hT x hx
    rw [dual_apply_eq_sum φ x, ← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · exact map_zero φ
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro a x _ hx
    rw [map_smul, hx, smul_zero]

end

end GaloisForLFunctions.HTGeometry
