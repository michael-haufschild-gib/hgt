import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# Two cells and the exact order of the special linear group

A determinant-one matrix with nonzero upper-left entry has a unit and
two scalar coordinates. If that entry is zero, the lower-left entry is
a unit and one scalar remains. These two explicit cells give
`#SL₂(F_q)=q(q²-1)` without any choice of generators.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Matrix
variable (K : Type*) [Field K]

/-- The cell where the upper-left entry is nonzero. -/
def specialLinearTwoFirstCell (a : Kˣ) (c t : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(a : K), t * a; c, (a : K)⁻¹ + t * c], by
    rw [Matrix.det_fin_two]
    change (a : K) * ((a : K)⁻¹ + t * c) - (t * a) * c = 1
    rw [mul_add, mul_inv_cancel₀ a.ne_zero]
    ring⟩

/-- The cell where the upper-left entry vanishes. -/
def specialLinearTwoSecondCell (c : Kˣ) (t : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -(c : K)⁻¹; (c : K), t * c], by
    rw [Matrix.det_fin_two]
    change (0 : K) * (t * c) - (-(c : K)⁻¹) * c = 1
    simp only [zero_mul, neg_mul, zero_sub, neg_neg, inv_mul_cancel₀ c.ne_zero]⟩

private def specialLinearTwoCellMap : ((Kˣ × K × K) ⊕ (Kˣ × K)) → SpecialLinearGroup (Fin 2) K
  | .inl (a, c, t) => specialLinearTwoFirstCell K a c t
  | .inr (c, t) => specialLinearTwoSecondCell K c t

private theorem specialLinearTwoCellMap_bijective : Function.Bijective (specialLinearTwoCellMap K) := by
  constructor
  · rintro (⟨a, c, t⟩ | ⟨c, t⟩) (⟨a', c', t'⟩ | ⟨c', t'⟩) h
    · have ha : a = a' := Units.ext (congrArg (fun M : SpecialLinearGroup (Fin 2) K => M 0 0) h)
      subst a'
      have hc : c = c' := congrArg (fun M : SpecialLinearGroup (Fin 2) K => M 1 0) h
      subst c'
      have ht : t * (a : K) = t' * a := congrArg (fun M : SpecialLinearGroup (Fin 2) K => M 0 1) h
      have he := mul_right_cancel₀ a.ne_zero ht
      subst t'
      rfl
    · exact (a.ne_zero (congrArg (fun M : SpecialLinearGroup (Fin 2) K => M 0 0) h)).elim
    · exact (a'.ne_zero (congrArg (fun M : SpecialLinearGroup (Fin 2) K => M 0 0) h).symm).elim
    · have hc : c = c' := Units.ext (congrArg (fun M : SpecialLinearGroup (Fin 2) K => M 1 0) h)
      subst c'
      have ht : t * (c : K) = t' * c := congrArg (fun M : SpecialLinearGroup (Fin 2) K => M 1 1) h
      have he := mul_right_cancel₀ c.ne_zero ht
      subst t'
      rfl
  · intro M
    have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using M.property
    by_cases ha : M 0 0 = 0
    · have hc : M 1 0 ≠ 0 := by
        intro h
        rw [ha, h, zero_mul, mul_zero, sub_self] at hdet
        exact zero_ne_one hdet
      refine ⟨.inr (Units.mk0 (M 1 0) hc, M 1 1 / M 1 0), ?_⟩
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j
      · exact ha.symm
      · change -(M 1 0)⁻¹ = M 0 1
        rw [ha, zero_mul, zero_sub] at hdet
        field_simp [hc]
        linear_combination hdet
      · rfl
      · change (M 1 1 / M 1 0) * M 1 0 = M 1 1
        exact div_mul_cancel₀ _ hc
    · refine ⟨.inl (Units.mk0 (M 0 0) ha, M 1 0, M 0 1 / M 0 0), ?_⟩
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j
      · rfl
      · change (M 0 1 / M 0 0) * M 0 0 = M 0 1
        exact div_mul_cancel₀ _ ha
      · rfl
      · change (M 0 0)⁻¹ + (M 0 1 / M 0 0) * M 1 0 = M 1 1
        field_simp [ha]
        linear_combination -hdet

/-- Every determinant-one matrix belongs to exactly one of the two explicit scalar cells. -/
def specialLinearTwoCellEquiv : ((Kˣ × K × K) ⊕ (Kˣ × K)) ≃ SpecialLinearGroup (Fin 2) K :=
  Equiv.ofBijective (specialLinearTwoCellMap K) (specialLinearTwoCellMap_bijective K)

/-- Over any finite field, the special linear group has exactly `q(q²-1)` elements. -/
theorem specialLinearTwo_card [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * ((Nat.card K) ^ 2 - 1) := by
  rw [← Nat.card_congr (specialLinearTwoCellEquiv K)]
  simp only [Nat.card_sum, Nat.card_prod, Nat.card_units]
  have hq : 1 ≤ Nat.card K := by
    letI := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  let k := Nat.card K - 1
  have hk : Nat.card K = k + 1 := (Nat.sub_add_cancel hq).symm
  have hs : (k + 1) ^ 2 - 1 = k ^ 2 + 2 * k := by
    rw [show (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 by ring, Nat.add_sub_cancel]
  simp only [hk, Nat.add_sub_cancel, hs]
  ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
