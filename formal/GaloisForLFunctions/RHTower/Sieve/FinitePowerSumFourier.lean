import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.Chebyshev

namespace RHTower.Sieve

open scoped BigOperators ComplexConjugate

noncomputable section

def finiteProductCharacter (q k : ℕ) [NeZero q]
    (ξ x : Fin k → ZMod q) : ℂ :=
  ∏ j : Fin k, ZMod.stdAddChar (ξ j * x j)

theorem sum_stdAddChar_mul (q : ℕ) [NeZero q] (x : ZMod q) :
    (∑ ξ : ZMod q, (ZMod.stdAddChar (ξ * x) : ℂ)) =
      if x = 0 then q else 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]
    simpa [AddChar.mulShift, mul_comm] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hx)

theorem sum_finiteProductCharacter (q k : ℕ) [NeZero q]
    (x : Fin k → ZMod q) :
    (∑ ξ : Fin k → ZMod q, finiteProductCharacter q k ξ x) =
      if x = 0 then (q ^ k : ℂ) else 0 := by
  simp only [finiteProductCharacter]
  calc
    (∑ ξ : Fin k → ZMod q,
        ∏ j : Fin k, ZMod.stdAddChar (ξ j * x j)) =
        ∏ j : Fin k, ∑ ξ : ZMod q,
          ZMod.stdAddChar (ξ * x j) :=
      (Fintype.prod_sum (fun j (ξ : ZMod q) =>
        (ZMod.stdAddChar (ξ * x j) : ℂ))).symm
    _ = if x = 0 then (q ^ k : ℂ) else 0 := by
      simp_rw [sum_stdAddChar_mul]
      by_cases hx : x = 0
      · subst x
        simp
      · rw [if_neg hx]
        have : ∃ j : Fin k, x j ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hx (funext hall)
        obtain ⟨j, hj⟩ := this
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

theorem finiteProductCharacter_add (q k : ℕ) [NeZero q]
    (ξ x y : Fin k → ZMod q) :
    finiteProductCharacter q k ξ (x + y) =
      finiteProductCharacter q k ξ x * finiteProductCharacter q k ξ y := by
  simp only [finiteProductCharacter, Pi.add_apply, mul_add,
    AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

theorem conj_finiteProductCharacter (q k : ℕ) [NeZero q]
    (ξ x : Fin k → ZMod q) :
    conj (finiteProductCharacter q k ξ x) =
      finiteProductCharacter q k ξ (-x) := by
  unfold finiteProductCharacter
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [AddChar.starComp_apply (by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne q))]
  rw [AddChar.inv_apply]
  simp

def finiteCharacterSum {α : Type*} [Fintype α]
    (q k : ℕ) [NeZero q] (f : α → Fin k → ZMod q)
    (ξ : Fin k → ZMod q) : ℂ :=
  ∑ a : α, finiteProductCharacter q k ξ (f a)

theorem normSq_finiteCharacterSum_eq
    {α : Type*} [Fintype α] (q k : ℕ) [NeZero q]
    (f : α → Fin k → ZMod q) (ξ : Fin k → ZMod q) :
    ‖finiteCharacterSum q k f ξ‖ ^ (2 : ℕ) =
      ∑ p : α × α, finiteProductCharacter q k ξ (f p.2 - f p.1) := by
  have hnorm : (‖finiteCharacterSum q k f ξ‖ : ℂ) ^ (2 : ℕ) =
      conj (finiteCharacterSum q k f ξ) * finiteCharacterSum q k f ξ := by
    rw [← Complex.ofReal_pow]
    rw [← Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_conj_mul_self]
  rw [hnorm,
    finiteCharacterSum, map_sum, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  simp only [Finset.univ_product_univ]
  apply Finset.sum_congr rfl
  intro p _
  rw [conj_finiteProductCharacter]
  rw [← finiteProductCharacter_add]
  simp [sub_eq_add_neg, add_comm]

theorem sum_normSq_finiteCharacterSum_eq_energy
    {α : Type*} [Fintype α] (q k : ℕ) [NeZero q]
    (f : α → Fin k → ZMod q) :
    ((∑ ξ : Fin k → ZMod q, ‖finiteCharacterSum q k f ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      (q ^ k : ℂ) *
        Fintype.card {p : α × α // f p.1 = f p.2} := by
  push_cast
  simp_rw [normSq_finiteCharacterSum_eq]
  rw [Finset.sum_comm]
  simp_rw [sum_finiteProductCharacter]
  simp_rw [sub_eq_zero]
  rw [Finset.sum_ite]
  have hfilter :
      (Finset.univ.filter fun p : α × α => f p.2 = f p.1) =
        Finset.univ.filter fun p : α × α => f p.1 = f p.2 := by
    ext p
    simp [eq_comm]
  rw [hfilter]
  rw [Fintype.card_of_subtype
    (Finset.univ.filter fun p : α × α => f p.1 = f p.2) (by simp)]
  simp [mul_comm]

end

end RHTower.Sieve

