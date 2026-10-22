import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearSubspace
import Mathlib.Analysis.RCLike.Basic

/-!
# Balancing a nuclear representation

Rescaling a rank-one term by a real scalar and its reciprocal changes neither the term nor the
product of the two norms, so a nuclear representation over the real or complex numbers can always
be rebalanced so that each functional has the same norm as its vector.  Degenerate terms, where one
of the two factors vanishes, are replaced by zero.

A balanced representation is what turns the coefficient family of a nuclear map into a
square-summable one: the squares of the functional norms are then exactly the terms of the
convergent series.  This is the normalization step of the factorization of a nuclear map through a
Hilbert space.

* `DeningerIsNuclear.exists_balanced` : a nuclear map has a representation whose functionals and
  vectors have equal norms.
* `DeningerIsNuclear.exists_balanced_summable_sq` : in a balanced representation the squares of the
  functional norms are summable.
-/

namespace RHTower

section Balanced

variable {𝕜 X Y : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **A nuclear representation can be balanced.**  Each rank-one term is rescaled so that the
functional and the vector have the same norm, without changing the term or the sum of the products
of the norms. -/
theorem DeningerIsNuclear.exists_balanced {T : X →L[𝕜] Y} (hT : DeningerIsNuclear T) :
    ∃ (ι : Type) (φ : ι → (X →L[𝕜] 𝕜)) (y : ι → Y),
      (∀ a, ‖φ a‖ = ‖y a‖) ∧ (Summable fun a => ‖φ a‖ * ‖y a‖) ∧
        ∀ x, HasSum (fun a => φ a x • y a) (T x) := by
  classical
  obtain ⟨ι, φ, y, hsum, happ⟩ := hT
  set deg : ι → Prop := fun a => ‖φ a‖ = 0 ∨ ‖y a‖ = 0 with hdeg
  set t : ι → ℝ := fun a => if deg a then 0 else Real.sqrt (‖y a‖ / ‖φ a‖) with ht
  set φ' : ι → (X →L[𝕜] 𝕜) :=
    fun a => if deg a then 0 else ((t a : 𝕜)) • φ a with hφ'
  set y' : ι → Y := fun a => if deg a then 0 else (((t a)⁻¹ : ℝ) : 𝕜) • y a with hy'
  have htpos : ∀ a, ¬ deg a → 0 < t a := by
    intro a ha
    rw [ht]
    simp only [if_neg ha]
    refine Real.sqrt_pos.mpr (div_pos ?_ ?_)
    · exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (fun h => ha (Or.inr h)))
    · exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (fun h => ha (Or.inl h)))
  have hnormφ' : ∀ a, ‖φ' a‖ = Real.sqrt (‖φ a‖ * ‖y a‖) := by
    intro a
    by_cases ha : deg a
    · rw [hφ']
      simp only [if_pos ha, norm_zero]
      rcases ha with h | h <;> rw [h] <;> simp
    · have hp : 0 < ‖φ a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm fun h => ha (Or.inl h))
      rw [hφ']
      simp only [norm_smul, RCLike.norm_ofReal, ht, if_neg ha,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hnn : 0 ≤ Real.sqrt (‖y a‖ / ‖φ a‖) * ‖φ a‖ := by positivity
      have hsq : (Real.sqrt (‖y a‖ / ‖φ a‖) * ‖φ a‖) ^ (2 : ℕ)
          = ‖φ a‖ * ‖y a‖ := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        field_simp
      rw [← hsq, Real.sqrt_sq hnn]
  have hnormy' : ∀ a, ‖y' a‖ = Real.sqrt (‖φ a‖ * ‖y a‖) := by
    intro a
    by_cases ha : deg a
    · rw [hy']
      simp only [if_pos ha, norm_zero]
      rcases ha with h | h <;> rw [h] <;> simp
    · have hp : 0 < ‖φ a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm fun h => ha (Or.inl h))
      have hq : 0 < ‖y a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm fun h => ha (Or.inr h))
      have hts : t a = Real.sqrt (‖y a‖ / ‖φ a‖) := by rw [ht]; simp only [if_neg ha]
      rw [hy']
      simp only [if_neg ha, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (le_of_lt (inv_pos.mpr (htpos a ha)))]
      rw [hts]
      have hnn : 0 ≤ (Real.sqrt (‖y a‖ / ‖φ a‖))⁻¹ * ‖y a‖ := by positivity
      have hsq : ((Real.sqrt (‖y a‖ / ‖φ a‖))⁻¹ * ‖y a‖) ^ (2 : ℕ)
          = ‖φ a‖ * ‖y a‖ := by
        rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
        field_simp
      rw [← hsq, Real.sqrt_sq hnn]
  refine ⟨ι, φ', y', fun a => by rw [hnormφ' a, hnormy' a], ?_, ?_⟩
  · have hprod : ∀ a, ‖φ' a‖ * ‖y' a‖ = ‖φ a‖ * ‖y a‖ := by
      intro a
      rw [hnormφ' a, hnormy' a, Real.mul_self_sqrt (by positivity)]
    exact hsum.congr fun a => (hprod a).symm
  · intro x
    have hterm : ∀ a, φ' a x • y' a = φ a x • y a := by
      intro a
      by_cases ha : deg a
      · rw [hφ', hy']
        simp only [if_pos ha, zero_apply, zero_smul]
        rcases ha with h | h
        · rw [norm_eq_zero] at h
          rw [h]
          simp
        · rw [norm_eq_zero] at h
          rw [h]
          simp
      · have hne : t a ≠ 0 := ne_of_gt (htpos a ha)
        rw [hφ', hy']
        have hne𝕜 : ((t a : 𝕜)) ≠ 0 := by
          simpa [RCLike.ofReal_eq_zero] using hne
        simp only [if_neg ha, smul_apply, smul_smul]
        congr 1
        rw [smul_eq_mul, RCLike.ofReal_inv]
        field_simp
    exact (happ x).congr_fun fun a => hterm a

/-- **In a balanced representation the squares of the functional norms are summable.** -/
theorem DeningerIsNuclear.exists_balanced_summable_sq {T : X →L[𝕜] Y}
    (hT : DeningerIsNuclear T) :
    ∃ (ι : Type) (φ : ι → (X →L[𝕜] 𝕜)) (y : ι → Y),
      (∀ a, ‖φ a‖ = ‖y a‖) ∧ (Summable fun a => ‖φ a‖ ^ (2 : ℕ)) ∧
        ∀ x, HasSum (fun a => φ a x • y a) (T x) := by
  obtain ⟨ι, φ, y, hbal, hsum, happ⟩ := hT.exists_balanced
  refine ⟨ι, φ, y, hbal, ?_, happ⟩
  refine hsum.congr fun a => ?_
  rw [← hbal a]
  ring

end Balanced

end RHTower

