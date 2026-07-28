import Mathlib

/-!
# Conjugation symmetry carries no positivity

A family of complex numbers closed under conjugation has a **real** sum of squares: pairing each
member with its partner cancels the imaginary parts.  It is tempting to read that reality as a step
towards positivity, and a large part of the functional-equation literature is organised around
exactly this symmetry.

It is not a step towards positivity, and the failure is not delicate.  For any family,

```text
Re ∑ gᵢ²  =  ∑ ‖gᵢ‖²  −  2 ∑ (Im gᵢ)² ,
```

so the sum of squares equals the total energy minus twice the imaginary energy — and conjugation
symmetry constrains only the *first* of those, leaving the second completely free.  The two-element
family `{i, −i}` is closed under conjugation and has sum of squares `−2`, while its energy is `+2`.

Consequently a positivity statement about `∑ gᵢ²` can never be obtained from the symmetry of the
index family; it must come from reality of the individual members, which is a strictly stronger
input.  Symmetry gives the *reality* of the sum, and reality of a sum is compatible with every
real value.
-/

open Finset

namespace GaloisForLFunctions

/-- **The energy decomposition of a sum of squares.**  Real part of the sum of squares equals total
energy minus twice the imaginary energy.  Both subtracted quantities are nonnegative, so the sum of
squares never exceeds the energy, and the gap measures exactly the failure of reality. -/
theorem re_sum_sq_eq_energy_sub_two_imaginary {ι : Type*} [Fintype ι] (g : ι → ℂ) :
    (∑ i, g i ^ 2).re = (∑ i, ‖g i‖ ^ 2) - 2 * ∑ i, (g i).im ^ 2 := by
  classical
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sq, Complex.mul_re, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- The sum of squares is bounded above by the energy, always. -/
theorem re_sum_sq_le_energy {ι : Type*} [Fintype ι] (g : ι → ℂ) :
    (∑ i, g i ^ 2).re ≤ ∑ i, ‖g i‖ ^ 2 := by
  rw [re_sum_sq_eq_energy_sub_two_imaginary]
  have : 0 ≤ ∑ i, (g i).im ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- **Reality of every member is exactly what makes the sum of squares equal the energy.** -/
theorem re_sum_sq_eq_energy_iff {ι : Type*} [Fintype ι] (g : ι → ℂ) :
    (∑ i, g i ^ 2).re = (∑ i, ‖g i‖ ^ 2) ↔ ∀ i, (g i).im = 0 := by
  rw [re_sum_sq_eq_energy_sub_two_imaginary]
  constructor
  · intro h i
    have hzero : ∑ j, (g j).im ^ 2 = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (g j).im).mp hzero i
      (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h
    have : ∑ i, (g i).im ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [h i]; norm_num
    rw [this]; ring

/-- A family closed under an involution implementing conjugation has a real sum of squares. -/
theorem sum_sq_im_eq_zero_of_conjSymmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℂ) (σ : Equiv.Perm ι) (hσ : ∀ i, g (σ i) = (starRingEnd ℂ) (g i)) :
    (∑ i, g i ^ 2).im = 0 := by
  classical
  have hconj : (starRingEnd ℂ) (∑ i, g i ^ 2) = ∑ i, g i ^ 2 := by
    rw [map_sum]
    calc ∑ i, (starRingEnd ℂ) (g i ^ 2) = ∑ i, g (σ i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hσ i, map_pow]
      _ = ∑ i, g i ^ 2 := Equiv.sum_comp σ (fun i => g i ^ 2)
  exact Complex.conj_eq_iff_im.mp hconj

/-- **Conjugation symmetry gives no positivity.**  An explicit two-element family, closed under an
involution implementing conjugation, whose sum of squares is strictly negative while its energy is
strictly positive.  Reality of the sum is therefore compatible with any sign, and no positivity
statement can be derived from the symmetry alone. -/
theorem exists_conjSymmetric_family_re_sum_sq_neg :
    ∃ (g : Fin 2 → ℂ) (σ : Equiv.Perm (Fin 2)),
      (∀ i, g (σ i) = (starRingEnd ℂ) (g i)) ∧
      (∑ i, g i ^ 2).im = 0 ∧
      (∑ i, g i ^ 2).re < 0 ∧
      0 < ∑ i, ‖g i‖ ^ 2 := by
  classical
  refine ⟨![Complex.I, -Complex.I], Equiv.swap 0 1, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · simp [Fin.sum_univ_two, Complex.I_sq]
  · simp [Fin.sum_univ_two, Complex.I_sq]
  · simp [Fin.sum_univ_two]

/-- **The gap is the imaginary energy, and symmetry does not touch it.**  Restating the two facts
together: symmetry forces the sum of squares to be real, and the distance from that real number to
the energy is twice the imaginary energy, which symmetry leaves unconstrained. -/
theorem conjSymmetric_sum_sq_eq_energy_sub_imaginary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℂ) (σ : Equiv.Perm ι) (hσ : ∀ i, g (σ i) = (starRingEnd ℂ) (g i)) :
    (∑ i, g i ^ 2).im = 0 ∧
      (∑ i, g i ^ 2).re = (∑ i, ‖g i‖ ^ 2) - 2 * ∑ i, (g i).im ^ 2 :=
  ⟨sum_sq_im_eq_zero_of_conjSymmetric g σ hσ, re_sum_sq_eq_energy_sub_two_imaginary g⟩

end GaloisForLFunctions
