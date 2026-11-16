import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.Ring

/-!
# Ramanujan moments with a degenerate character

The largest ideal killed by an additive character records exactly the loss of
Fourier separation. Mixed Ramanujan moments count unit tuples whose weighted
sum has the prescribed image modulo that ideal. This works for every finite
commutative ring, including rings without a primitive additive character.
-/

open Finset
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section
variable {R : Type*} [CommRing R]

/-- The ideal of elements invisible to every multiplicative shift of a character. -/
def characterRadical (ψ : AddChar R ℂ) : Ideal R where
  carrier := {a | ∀ g, ψ (g * a) = 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb g
    rw [mul_add, AddChar.map_add_eq_mul, ha g, hb g, one_mul]
  smul_mem' := by
    intro r a ha g
    simpa only [smul_eq_mul, mul_assoc] using ha (g * r)

/-- The character radical is the largest ideal contained in the additive kernel. -/
theorem le_characterRadical_iff (ψ : AddChar R ℂ) (I : Ideal R) :
    I ≤ characterRadical ψ ↔ ∀ a ∈ I, ψ a = 1 := by
  constructor
  · intro h a ha
    simpa only [one_mul] using h ha 1
  · intro h a ha g
    exact h (g * a) (I.mul_mem_left g ha)

/-- Primitivity is exactly the absence of a nonzero invisible ideal. -/
theorem isPrimitive_iff_characterRadical_eq_bot (ψ : AddChar R ℂ) :
    ψ.IsPrimitive ↔ characterRadical ψ = ⊥ := by
  constructor
  · intro h
    apply le_antisymm _ bot_le
    intro a ha
    rw [Ideal.mem_bot]
    by_contra ha0
    apply h ha0
    ext g
    simpa only [AddChar.mulShift_apply, AddChar.one_apply, mul_comm a g] using ha g
  · intro h a ha he
    have hm : a ∈ characterRadical ψ := by
      intro g
      have hg := DFunLike.congr_fun he g
      simpa only [AddChar.mulShift_apply, AddChar.one_apply, mul_comm a g] using hg
    rw [h, Ideal.mem_bot] at hm
    exact ha hm

variable [Fintype R]

/-- Orthogonality retains precisely the character radical, even for nonprimitive characters. -/
theorem sum_character_mul_eq_radical (ψ : AddChar R ℂ) (a : R) :
    (∑ g : R, ψ (g * a)) =
      if a ∈ characterRadical ψ then (Fintype.card R : ℂ) else 0 := by
  by_cases ha : a ∈ characterRadical ψ
  · rw [if_pos ha]
    simp only [(show ∀ g, ψ (g * a) = 1 from ha), sum_const,
      card_univ, nsmul_eq_mul, mul_one]
  · rw [if_neg ha]
    have hn : ψ.mulShift a ≠ 1 := by
      intro h
      apply ha
      intro g
      have hg := DFunLike.congr_fun h g
      simpa only [AddChar.mulShift_apply, AddChar.one_apply, mul_comm a g] using hg
    simpa only [AddChar.mulShift_apply, mul_comm a] using
      AddChar.sum_eq_zero_of_ne_one hn

/-- Ramanujan sum attached to any additive character of a finite ring. -/
def ringRamanujanSum (ψ : AddChar R ℂ) (g : R) : ℂ :=
  ∑ u : Rˣ, ψ (g * (u : R))

/-- Unit tuples in a prescribed fiber modulo the character radical. -/
def radicalUnitTupleCount (ψ : AddChar R ℂ) {ι : Type*} [Fintype ι]
    (r : ι → R) (t : R) : ℕ :=
  ((univ : Finset (ι → Rˣ)).filter
    (fun u => (∑ i, r i * (u i : R)) - t ∈ characterRadical ψ)).card

omit [Fintype R] in
private theorem map_character_sum (ψ : AddChar R ℂ) {ι : Type*}
    (s : Finset ι) (f : ι → R) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [sum_insert hi, prod_insert hi, AddChar.map_add_eq_mul, ih]

/-- Mixed Fourier moments count fibers modulo the exact invisible ideal. -/
theorem sum_ringRamanujan_product_character (ψ : AddChar R ℂ)
    {ι : Type*} [Fintype ι] (r : ι → R) (t : R) :
    (∑ g : R, (∏ i, ringRamanujanSum ψ (g * r i)) * ψ (-(g * t))) =
      (Fintype.card R : ℂ) * radicalUnitTupleCount ψ r t := by
  simp_rw [ringRamanujanSum, Fintype.prod_sum, sum_mul]
  rw [sum_comm]
  have hterm (u : ι → Rˣ) (g : R) :
      (∏ i, ψ ((g * r i) * (u i : R))) * ψ (-(g * t)) =
        ψ (g * ((∑ i, r i * (u i : R)) - t)) := by
    rw [← map_character_sum, ← AddChar.map_add_eq_mul]
    congr 1
    simp only [mul_assoc, ← mul_sum]
    ring
  simp_rw [hterm, sum_character_mul_eq_radical]
  rw [radicalUnitTupleCount, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- Every raw moment is a natural multiple of the ring cardinality, without a primitivity premise. -/
theorem ringRamanujan_moment_is_nat (ψ : AddChar R ℂ) (k : ℕ) :
    ∃ n : ℕ, (∑ g : R, ringRamanujanSum ψ g ^ k) =
      (Fintype.card R * n : ℕ) := by
  refine ⟨radicalUnitTupleCount ψ (fun _ : Fin k => 1) 0, ?_⟩
  simpa only [mul_one, mul_zero, neg_zero, AddChar.map_zero_eq_one,
    prod_const, card_univ, Fintype.card_fin, Nat.cast_mul] using
    sum_ringRamanujan_product_character ψ (fun _ : Fin k => 1) 0

#print axioms le_characterRadical_iff
#print axioms isPrimitive_iff_characterRadical_eq_bot
#print axioms sum_character_mul_eq_radical
#print axioms sum_ringRamanujan_product_character
#print axioms ringRamanujan_moment_is_nat

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
