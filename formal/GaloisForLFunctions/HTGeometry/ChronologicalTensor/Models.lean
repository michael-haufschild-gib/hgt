import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Foundations
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FourPoint
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Curvature

/-!
# Exact models of the chronological capacity seminorm

The four- and six-endpoint response polynomials are realized by explicit window
families. Their sharp inequalities and unit-cost optimizers identify the actual
capacity suprema, including the continuously curved supporting family.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Finset

def fourWindows : Fin 2 → Fin 2 → Finset (Fin 3) :=
  ![![{0}, {2}], ![{1}, univ]]

def sixWindows : Fin 2 → Fin 3 → Finset (Fin 5) :=
  ![![{0}, {2}, {4}], ![univ, {1,2,3}, {2}]]

theorem normalizeProbe_fixed_iff {n : ℕ} (g : Fin n → ℝ) :
    normalizeProbe g = g ↔ variation g ≤ 1 := by
  constructor
  · intro h
    have hb := normalizeProbe_budget g
    rw [h] at hb
    exact hb
  · intro h
    funext i
    simp only [normalizeProbe, max_eq_left h, div_one]

theorem variation_four (g : Fin 3 → ℝ) : variation g = fourCost (g 0) (g 1) (g 2) := by
  simp only [variation, Fin.sum_univ_three, fourCost]

theorem variation_six (g : Fin 5 → ℝ) : variation g = sixCost (g 0) (g 1) (g 2) (g 3) (g 4) := by
  simp only [variation, Fin.sum_univ_five, sixCost]

theorem fourWindows_value (A B : ℝ) (g : Fin 3 → ℝ) :
    familyValue fourWindows ![A,B] g = fourResponse A B (g 0) (g 1) (g 2) := by
  simp [familyValue, diagramValue, windowValue, fourWindows, Fin.sum_univ_two,
    Fin.prod_univ_two, Fin.sum_univ_three, fourResponse, separated, enclosing]

theorem sixWindows_value (A B : ℝ) (g : Fin 5 → ℝ) :
    familyValue sixWindows ![A,B] g = weightedSixResponse A B (g 0) (g 1) (g 2) (g 3) (g 4) := by
  simp [familyValue, diagramValue, windowValue, sixWindows, Fin.sum_univ_two,
    Fin.prod_univ_three, Fin.sum_univ_five, weightedSixResponse, separatedThree, rainbowThree]
  ring_nf
  simp

theorem fourWindows_capacity (A B : ℝ) :
    familyCapacity fourWindows ![A,B] = fourCapacity A B := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g, rfl⟩
    dsimp only
    rw [fourWindows_value]
    have h := four_sharp_bound A B ((normalizeProbe g) 0) ((normalizeProbe g) 1) ((normalizeProbe g) 2)
    have hv := normalizeProbe_budget g
    rw [variation_four] at hv
    have ht : 0 ≤ fourCost ((normalizeProbe g) 0) ((normalizeProbe g) 1) ((normalizeProbe g) 2) := by
      unfold fourCost; positivity
    have hp := pow_le_pow_left₀ ht hv 2
    rw [one_pow] at hp
    have hc : 0 ≤ fourCapacity A B := (abs_nonneg B).trans (le_max_right _ _)
    exact h.trans ((mul_le_mul_of_nonneg_left hp hc).trans_eq (mul_one _))
  · obtain ⟨u,v,w,hcost,hvalue⟩ := four_attained A B
    let g : Fin 3 → ℝ := ![u,v,w]
    have hv : variation g = 1 := by simpa [variation_four, g] using hcost
    have hg := (normalizeProbe_fixed_iff g).mpr (le_of_eq hv)
    have h := familyCapacity_probe_bound fourWindows ![A,B] g
    rw [hg, fourWindows_value] at h
    change |fourResponse A B u v w| ≤ familyCapacity fourWindows ![A,B] at h
    rw [hvalue] at h
    exact h

theorem sixWindows_capacity : familyCapacity sixWindows ![27,1] = sixCapacity := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g, rfl⟩
    dsimp only
    rw [sixWindows_value]
    simp only [weightedSixResponse, one_mul] at *
    change |sixResponse ((normalizeProbe g) 0) ((normalizeProbe g) 1) ((normalizeProbe g) 2)
      ((normalizeProbe g) 3) ((normalizeProbe g) 4)| ≤ sixCapacity
    have h := six_sharp_bound ((normalizeProbe g) 0) ((normalizeProbe g) 1) ((normalizeProbe g) 2)
      ((normalizeProbe g) 3) ((normalizeProbe g) 4)
    have hv := normalizeProbe_budget g
    rw [variation_six] at hv
    have ht : 0 ≤ sixCost ((normalizeProbe g) 0) ((normalizeProbe g) 1) ((normalizeProbe g) 2)
        ((normalizeProbe g) 3) ((normalizeProbe g) 4) := by unfold sixCost; positivity
    have hp := pow_le_pow_left₀ ht hv 3
    rw [one_pow] at hp
    exact h.trans ((mul_le_mul_of_nonneg_left hp sixCapacity_nonneg).trans_eq (mul_one _))
  · let g : Fin 5 → ℝ := ![(1-peakPosition)/2,0,peakPosition,0,(1-peakPosition)/2]
    have hv : variation g = 1 := by simpa [variation_six, g] using six_attained.1
    have hg := (normalizeProbe_fixed_iff g).mpr (le_of_eq hv)
    have h := familyCapacity_probe_bound sixWindows ![27,1] g
    rw [hg, sixWindows_value] at h
    simp only [weightedSixResponse, one_mul] at *
    change |sixResponse ((1-peakPosition)/2) 0 peakPosition 0 ((1-peakPosition)/2)| ≤
      familyCapacity sixWindows ![27,1] at h
    rw [six_attained.2] at h
    exact h

theorem sixWindows_arc_capacity (s : ℝ) :
    familyCapacity sixWindows ![arcA s,arcB s] = arcCapacity s := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g, rfl⟩
    dsimp only
    rw [sixWindows_value]
    have h := arc_sharp_bound s ((normalizeProbe g) 0) ((normalizeProbe g) 1) ((normalizeProbe g) 2)
      ((normalizeProbe g) 3) ((normalizeProbe g) 4)
    have hv := normalizeProbe_budget g
    rw [variation_six] at hv
    have ht : 0 ≤ sixCost ((normalizeProbe g) 0) ((normalizeProbe g) 1) ((normalizeProbe g) 2)
        ((normalizeProbe g) 3) ((normalizeProbe g) 4) := by unfold sixCost; positivity
    have hp := pow_le_pow_left₀ ht hv 3
    rw [one_pow] at hp
    exact h.trans ((mul_le_mul_of_nonneg_left hp (arc_coefficients_nonneg s).2.2).trans_eq (mul_one _))
  · let g : Fin 5 → ℝ := ![(1-arcPosition s)/2,0,arcPosition s,0,(1-arcPosition s)/2]
    have hv : variation g = 1 := by simpa [variation_six, g] using (arc_attained s).1
    have hg := (normalizeProbe_fixed_iff g).mpr (le_of_eq hv)
    have h := familyCapacity_probe_bound sixWindows ![arcA s,arcB s] g
    rw [hg, sixWindows_value] at h
    change |weightedSixResponse (arcA s) (arcB s) ((1-arcPosition s)/2) 0
      (arcPosition s) 0 ((1-arcPosition s)/2)| ≤ familyCapacity sixWindows ![arcA s,arcB s] at h
    rw [(arc_attained s).2] at h
    exact h

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
