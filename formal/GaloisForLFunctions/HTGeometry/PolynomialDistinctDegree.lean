import Mathlib

/-!
# Polynomials of distinct degrees are linearly independent

A finite family of nonzero polynomials with an injective degree map is linearly independent
(`linearIndependent_of_natDegree_injective`): in any nontrivial vanishing combination, the
highest-degree participating term contributes its leading coefficient to that degree with no
cancellation, forcing its coefficient to be zero.

Applied to the leading-symbol weight polynomials of a differential polynomial, this is the true
positive counterpart of the same-order degeneracy: differential monomials of pairwise distinct
total order carry linearly independent leading symbols, so no leading-symbol cancellation
occurs among them.
-/

open Polynomial

namespace GaloisForLFunctions

/-- **Distinct degrees give independence.**  A finite family of nonzero polynomials whose
degrees are pairwise distinct is linearly independent. -/
theorem linearIndependent_of_natDegree_injective {ι : Type*} [Fintype ι] {K : Type*} [Field K]
    {p : ι → Polynomial K} (hne : ∀ i, p i ≠ 0)
    (hdeg : Function.Injective fun i => (p i).natDegree) :
    LinearIndependent K p := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ := hcon
  set S := Finset.univ.filter (fun i => g i ≠ 0) with hS
  have hSne : S.Nonempty := ⟨i, by simp [hS, hi]⟩
  obtain ⟨i₀, hi₀S, hi₀max⟩ := S.exists_max_image (fun i => (p i).natDegree) hSne
  set d₀ := (p i₀).natDegree with hd₀
  have hco : ∑ i, g i * (p i).coeff d₀ = 0 := by
    have h := congrArg (fun q : Polynomial K => q.coeff d₀) hg
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul,
      Polynomial.coeff_zero] at h
    exact h
  have hsingle : ∑ i, g i * (p i).coeff d₀ = g i₀ * (p i₀).coeff d₀ := by
    refine Finset.sum_eq_single i₀ (fun b _ hbne => ?_) (fun h => absurd (Finset.mem_univ i₀) h)
    by_cases hgb : g b = 0
    · rw [hgb, zero_mul]
    · have hbS : b ∈ S := by simp [hS, hgb]
      have hble : (p b).natDegree ≤ d₀ := hi₀max b hbS
      have hbne_deg : (p b).natDegree ≠ d₀ := fun h => hbne (hdeg h)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne hble hbne_deg), mul_zero]
  rw [hsingle] at hco
  have hgi₀ : g i₀ ≠ 0 := by simpa [hS] using hi₀S
  have hlc : (p i₀).coeff d₀ ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (hne i₀)
  exact (mul_ne_zero hgi₀ hlc) hco

end GaloisForLFunctions
