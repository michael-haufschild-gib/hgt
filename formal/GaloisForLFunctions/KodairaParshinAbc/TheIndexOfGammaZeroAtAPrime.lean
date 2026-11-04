import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# The index of `Γ₀(p)`

The modular curve `X₀(23)` used for the discriminant inequality has a `j`-map of degree
`[SL(2, ℤ) : Γ₀(23)] = 24`.  For a prime `p` the left cosets of `Γ₀(p)` are classified by the first
column of a matrix modulo `p`, read as a point of `P¹(F_p)`:

  `γ = [[a, b], [c, d]] ↦ (a : c) = a/c ∈ F_p`, or `∞` if `c ≡ 0`.

Indeed the lower-left entry of `γ⁻¹ γ'` is `a c' - c a'`, which vanishes modulo `p` exactly when the
two first columns are proportional; and every point of `P¹(F_p)` is the first column of
`[[t, -1], [1, 0]]` or of the identity.  Hence `SL(2, ℤ) ⧸ Γ₀(p) ≃ P¹(F_p)` and

  `[SL(2, ℤ) : Γ₀(p)] = p + 1`,  in particular `[SL(2, ℤ) : Γ₀(23)] = 24`.
-/

noncomputable section

open Matrix CongruenceSubgroup
open scoped MatrixGroups

namespace GaloisForLFunctions.KodairaParshinAbc

variable {p : ℕ} [hp : Fact p.Prime]

/-- The first column of `γ` modulo `p`, as a point of `P¹(F_p) = F_p ∪ {∞}`. -/
def firstColumnPoint (γ : SL(2, ℤ)) : Option (ZMod p) :=
  if ((γ 1 0 : ℤ) : ZMod p) = 0 then none else some (((γ 0 0 : ℤ) : ZMod p) / ((γ 1 0 : ℤ) : ZMod p))

/-- The first column of a matrix of determinant one is nonzero modulo `p`. -/
theorem firstColumn_ne_zero (γ : SL(2, ℤ)) :
    ¬ (((γ 0 0 : ℤ) : ZMod p) = 0 ∧ ((γ 1 0 : ℤ) : ZMod p) = 0) := by
  rintro ⟨ha, hc⟩
  have hdet : (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hcast := congrArg (fun z : ℤ => (z : ZMod p)) hdet
  push_cast at hcast
  rw [ha, hc] at hcast
  simp at hcast

/-- The lower-left entry of `γ⁻¹ γ'` is `a c' - c a'`. -/
theorem inv_mul_apply_one_zero (γ γ' : SL(2, ℤ)) :
    (γ⁻¹ * γ') 1 0 = γ 0 0 * γ' 1 0 - γ 1 0 * γ' 0 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **Two matrices lie in the same left coset of `Γ₀(p)` iff their first columns define the same
point of `P¹(F_p)`.** -/
theorem inv_mul_mem_Gamma0_iff (γ γ' : SL(2, ℤ)) :
    γ⁻¹ * γ' ∈ Gamma0 p ↔ firstColumnPoint (p := p) γ = firstColumnPoint γ' := by
  rw [Gamma0_mem, inv_mul_apply_one_zero]
  push_cast
  set a : ZMod p := ((γ 0 0 : ℤ) : ZMod p)
  set c : ZMod p := ((γ 1 0 : ℤ) : ZMod p)
  set a' : ZMod p := ((γ' 0 0 : ℤ) : ZMod p)
  set c' : ZMod p := ((γ' 1 0 : ℤ) : ZMod p)
  have h₁ := firstColumn_ne_zero (p := p) γ
  have h₂ := firstColumn_ne_zero (p := p) γ'
  unfold firstColumnPoint
  change a * c' - c * a' = 0 ↔ (if c = 0 then none else some (a / c)) =
    (if c' = 0 then none else some (a' / c'))
  by_cases hc : c = 0
  · have ha : a ≠ 0 := fun ha => h₁ ⟨ha, hc⟩
    by_cases hc' : c' = 0
    · simp [hc, hc']
    · simp only [hc, hc', if_true, if_false, zero_mul, sub_zero, reduceCtorEq, iff_false]
      exact mul_ne_zero ha hc'
  · by_cases hc' : c' = 0
    · have ha' : a' ≠ 0 := fun ha' => h₂ ⟨ha', hc'⟩
      simp only [hc, hc', if_true, if_false, mul_zero, zero_sub, neg_eq_zero, reduceCtorEq,
        iff_false]
      exact mul_ne_zero hc ha'
    · simp only [hc, hc', if_false, Option.some.injEq]
      rw [div_eq_div_iff hc hc', sub_eq_zero]
      constructor <;> intro h <;> linear_combination h

/-- The representative `[[t, -1], [1, 0]]` of the point `t ∈ F_p`. -/
def pointRepresentative (t : ZMod p) : SL(2, ℤ) :=
  ⟨!![(t.val : ℤ), -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem firstColumnPoint_surjective :
    Function.Surjective (firstColumnPoint (p := p)) := by
  rintro (_ | t)
  · refine ⟨1, ?_⟩
    simp [firstColumnPoint]
  · refine ⟨pointRepresentative t, ?_⟩
    simp [firstColumnPoint, pointRepresentative]

/-- **`SL(2, ℤ) ⧸ Γ₀(p) ≃ P¹(F_p)`.** -/
def gamma0QuotientEquiv : SL(2, ℤ) ⧸ Gamma0 p ≃ Option (ZMod p) :=
  Equiv.ofBijective
    (Quotient.lift (firstColumnPoint (p := p)) fun γ γ' h =>
      (inv_mul_mem_Gamma0_iff γ γ').mp (QuotientGroup.leftRel_apply.mp h))
    ⟨by
      rintro ⟨γ⟩ ⟨γ'⟩ h
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((inv_mul_mem_Gamma0_iff γ γ').mpr h)),
    fun t => by
      obtain ⟨γ, hγ⟩ := firstColumnPoint_surjective t
      exact ⟨QuotientGroup.mk γ, hγ⟩⟩

/-- **`[SL(2, ℤ) : Γ₀(p)] = p + 1`.** -/
theorem index_Gamma0_prime : (Gamma0 p).index = p + 1 := by
  rw [Subgroup.index, Nat.card_congr gamma0QuotientEquiv, Finite.card_option, Nat.card_zmod]

/-- The `j`-map of `X₀(23)` has degree `[SL(2, ℤ) : Γ₀(23)] = 24`. -/
theorem index_Gamma0_twentyThree : (Gamma0 23).index = 24 := by
  haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  exact index_Gamma0_prime

end GaloisForLFunctions.KodairaParshinAbc
