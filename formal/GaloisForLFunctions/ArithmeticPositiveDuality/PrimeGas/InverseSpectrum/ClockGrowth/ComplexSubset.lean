import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # A coherent subset of a finite family of complex increments -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset

private theorem abs_coordinate_sum {ι : Type*} (F : Finset ι) (v : ι → ℂ) (φ : ℂ →+ ℝ)
    (hφ : ∀ z : ℂ, |φ z| ≤ ‖z‖) {B : ℝ} (hb : ∀ S ⊆ F, ‖∑ i ∈ S, v i‖ ≤ B) :
    ∑ i ∈ F, |φ (v i)| ≤ B+B := by
  classical
  let P := F.filter (fun i => 0 ≤ φ (v i))
  let N := F.filter (fun i => φ (v i) < 0)
  have hs (S : Finset ι) (hS : S ⊆ F) : |∑ i ∈ S, φ (v i)| ≤ B := by
    rw [← map_sum]
    exact (hφ _).trans (hb _ hS)
  have hP := (le_abs_self _).trans (hs P (filter_subset _ _))
  have hN := (neg_le_abs _).trans (hs N (filter_subset _ _))
  have he : ∑ i ∈ F, |φ (v i)| = (∑ i ∈ P, φ (v i))-(∑ i ∈ N, φ (v i)) := by
    simp only [P,N,sum_filter,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ φ (v i)
    · simp only [abs_of_nonneg hi,if_pos hi,if_neg (not_lt.mpr hi),sub_zero]
    · simp only [abs_of_neg (lt_of_not_ge hi),if_neg hi,if_pos (lt_of_not_ge hi),zero_sub]
  rw [he,sub_eq_add_neg]
  exact add_le_add hP hN

/-- Some subfamily carries at least a quarter of the sum of the complex lengths. -/
theorem exists_complex_subset {ι : Type*} (F : Finset ι) (v : ι → ℂ) :
    ∃ S ⊆ F, (∑ i ∈ F, ‖v i‖) ≤ 4*‖∑ i ∈ S, v i‖ := by
  classical
  obtain ⟨S,hS,hm⟩ := F.powerset.exists_max_image (fun U => ‖∑ i ∈ U, v i‖) ⟨∅,mem_powerset.mpr (empty_subset _)⟩
  have hb (U : Finset ι) (hU : U ⊆ F) := hm U (mem_powerset.mpr hU)
  have hr := abs_coordinate_sum F v Complex.reAddGroupHom Complex.abs_re_le_norm hb
  have hi := abs_coordinate_sum F v Complex.imAddGroupHom Complex.abs_im_le_norm hb
  refine ⟨S,mem_powerset.mp hS,?_⟩
  have h := sum_le_sum (s := F) (fun i _ => Complex.norm_le_abs_re_add_abs_im (v i))
  rw [sum_add_distrib] at h
  change (∑ i ∈ F, |(v i).re|) ≤ _ at hr
  change (∑ i ∈ F, |(v i).im|) ≤ _ at hi
  linarith only [h,hr,hi]

#print axioms exists_complex_subset

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
