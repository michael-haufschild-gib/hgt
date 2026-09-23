import GaloisForLFunctions.RHTower.Sieve.HeathBrownFareyWindow
import GaloisForLFunctions.QuantumAlg.Util.RationalApproximation

/-!
# Primitive positive direction packing in arbitrary ratio windows

Heath--Brown collision directions need not have slope at most one.  This module extends Farey
packing to the full positive square by proving ordinary separation directly from the nonzero
cross-product determinant of two reduced fractions.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Coprime positive integral directions with both coordinates at most `Q`. -/
def heathBrownPrimitiveSquare (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter fun p => Nat.Coprime p.1 p.2

theorem mem_heathBrownPrimitiveSquare {Q : ℕ} {p : ℕ × ℕ} :
    p ∈ heathBrownPrimitiveSquare Q ↔
      1 ≤ p.1 ∧ p.1 ≤ Q ∧ 1 ≤ p.2 ∧ p.2 ≤ Q ∧ Nat.Coprime p.1 p.2 := by
  simp [heathBrownPrimitiveSquare]
  tauto

/-- Reduced positive directions have distinct slopes on the full square. -/
theorem heathBrownFareyValue_injOn_primitiveSquare {Q : ℕ} :
    Set.InjOn heathBrownFareyValue (heathBrownPrimitiveSquare Q : Set (ℕ × ℕ)) := by
  intro p hp q hq hpq
  have hp' := mem_heathBrownPrimitiveSquare.mp hp
  have hq' := mem_heathBrownPrimitiveSquare.mp hq
  have hp2 : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hp'.2.2.1
  have hq2 : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast hq'.2.2.1
  have hcrossR : (p.1 : ℝ) * (q.2 : ℝ) = (q.1 : ℝ) * (p.2 : ℝ) := by
    unfold heathBrownFareyValue at hpq
    field_simp at hpq
    simpa [mul_comm] using hpq
  have hcross : p.1 * q.2 = q.1 * p.2 := by exact_mod_cast hcrossR
  obtain ⟨h1, h2⟩ :=
    QuantumAlg.RationalApproximation.reducedFraction_eq_of_cross_mul
      hp'.2.2.1 hq'.2.2.1 hp'.2.2.2.2 hq'.2.2.2.2 hcross
  exact Prod.ext h1 h2

/-- Any two distinct primitive positive directions of height at most `Q` are separated by
`Q⁻²` in ordinary slope. -/
theorem heathBrownPrimitiveSquare_sep {Q : ℕ} (hQ : 1 ≤ Q) :
    ∀ p ∈ heathBrownPrimitiveSquare Q, ∀ q ∈ heathBrownPrimitiveSquare Q, p ≠ q →
      1 / (Q : ℝ) ^ (2 : ℕ) ≤ |heathBrownFareyValue p - heathBrownFareyValue q| := by
  intro p hp q hq hpq
  have hp' := mem_heathBrownPrimitiveSquare.mp hp
  have hq' := mem_heathBrownPrimitiveSquare.mp hq
  have hp2 : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hp'.2.2.1
  have hq2 : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast hq'.2.2.1
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hcross : p.1 * q.2 ≠ q.1 * p.2 := by
    intro heq
    obtain ⟨h1, h2⟩ :=
      QuantumAlg.RationalApproximation.reducedFraction_eq_of_cross_mul
        hp'.2.2.1 hq'.2.2.1 hp'.2.2.2.2 hq'.2.2.2.2 heq
    exact hpq (Prod.ext h1 h2)
  have hcrossZ : (p.1 : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (p.2 : ℤ) ≠ 0 := by
    intro hz
    apply hcross
    exact_mod_cast sub_eq_zero.mp hz
  have honeZ : (1 : ℤ) ≤
      |(p.1 : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (p.2 : ℤ)| :=
    Int.one_le_abs hcrossZ
  have hone : (1 : ℝ) ≤
      |(p.1 : ℝ) * (q.2 : ℝ) - (q.1 : ℝ) * (p.2 : ℝ)| := by
    exact_mod_cast honeZ
  have hden : (p.2 : ℝ) * (q.2 : ℝ) ≤ (Q : ℝ) ^ (2 : ℕ) := by
    have hpQ : (p.2 : ℝ) ≤ Q := by exact_mod_cast hp'.2.2.2.1
    have hqQ : (q.2 : ℝ) ≤ Q := by exact_mod_cast hq'.2.2.2.1
    nlinarith
  have hfrac : 1 / (Q : ℝ) ^ (2 : ℕ) ≤
      |(p.1 : ℝ) * (q.2 : ℝ) - (q.1 : ℝ) * (p.2 : ℝ)| /
        ((p.2 : ℝ) * (q.2 : ℝ)) := by
    have hdenpos : (0 : ℝ) < (p.2 : ℝ) * (q.2 : ℝ) := mul_pos hp2 hq2
    rw [div_le_div_iff₀ (sq_pos_of_pos hQpos) hdenpos]
    nlinarith
  change 1 / (Q : ℝ) ^ (2 : ℕ) ≤
    |(p.1 : ℝ) / (p.2 : ℝ) - (q.1 : ℝ) / (q.2 : ℝ)|
  refine hfrac.trans_eq ?_
  have heq : (p.1 : ℝ) / (p.2 : ℝ) - (q.1 : ℝ) / (q.2 : ℝ) =
      ((p.1 : ℝ) * (q.2 : ℝ) - (q.1 : ℝ) * (p.2 : ℝ)) /
        ((p.2 : ℝ) * (q.2 : ℝ)) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hp2 hq2)]

/-- Primitive directions of height at most `Q` in one arbitrary positive ratio window. -/
def heathBrownPrimitiveWindow (Q : ℕ) (a b : ℝ) : Finset (ℕ × ℕ) :=
  (heathBrownPrimitiveSquare Q).filter fun p =>
    a ≤ heathBrownFareyValue p ∧ heathBrownFareyValue p ≤ b

/-- **Full-square primitive-window packing.** An interval of width `b-a` contains at most
`(b-a)Q²+1` primitive positive directions of height at most `Q`. -/
theorem card_heathBrownPrimitiveWindow_le {Q : ℕ} (hQ : 1 ≤ Q)
    {a b : ℝ} (hab : a ≤ b) :
    ((heathBrownPrimitiveWindow Q a b).card : ℝ) ≤
      (b - a) * (Q : ℝ) ^ (2 : ℕ) + 1 := by
  let W := heathBrownPrimitiveWindow Q a b
  let V := W.image heathBrownFareyValue
  have hinj : Set.InjOn heathBrownFareyValue (W : Set (ℕ × ℕ)) :=
    heathBrownFareyValue_injOn_primitiveSquare.mono fun p hp =>
      (Finset.mem_filter.mp hp).1
  have hcard : V.card = W.card := Finset.card_image_of_injOn hinj
  have hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y →
      1 / (Q : ℝ) ^ (2 : ℕ) ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨p, hpW, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hqW, rfl⟩ := Finset.mem_image.mp hy
    apply heathBrownPrimitiveSquare_sep hQ p (Finset.mem_filter.mp hpW).1 q
      (Finset.mem_filter.mp hqW).1
    intro hpq
    subst q
    exact hxy rfl
  have hsub : ∀ x ∈ V, x ∈ Set.Icc a b := by
    intro x hx
    obtain ⟨p, hpW, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hpW).2
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hL : (0 : ℝ) < 1 / (Q : ℝ) ^ (2 : ℕ) := by positivity
  have hbound := card_le_of_separated_of_subset_Icc hL hab V hsep hsub
  rw [hcard] at hbound
  change (W.card : ℝ) ≤ _
  convert hbound using 1
  field_simp

end

end RHTower.Sieve
