import GaloisForLFunctions.RHTower.Deninger.DeningerFlattenDrop

/-!
# Comparing two descriptions of the same list

If the same list is described twice as a conjugator, a concatenation of copies of a cyclically
reduced word, and a tail, then the two cyclically reduced words are rotations of one another, by the
difference of the conjugator lengths modulo their common length.

* `deningerFlatten_add` : concatenations of copies add.
* `deningerRotate_of_flatten_eq` : the comparison.
-/

namespace RHTower

open Monoid Monoid.PushoutI

variable {ι : Type*} {G : ι → Type*}

theorem deningerFlatten_add (V : List (Σ i, G i)) (a b : ℕ) :
    deningerFlatten (G := G) V (a + b) =
      deningerFlatten (G := G) V a ++ deningerFlatten (G := G) V b := by
  induction a with
  | zero => simp [deningerFlatten]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by ring, deningerFlatten_succ, ih, deningerFlatten_succ,
      List.append_assoc]

/-- **The comparison.**  Two descriptions of the same list force the two cyclically reduced words to
be rotations of one another. -/
theorem deningerRotate_of_flatten_eq (Cx Cy Vx Vy Bx By : List (Σ i, G i)) (M q r : ℕ)
    (hlen : Vx.length = Vy.length)
    (hCle : Cx.length ≤ Cy.length)
    (ht : Cy.length - Cx.length = q * Vx.length + r) (hr : r < Vx.length)
    (hM : q + 2 ≤ M)
    (heq : Cx ++ (deningerFlatten (G := G) Vx M ++ Bx) =
      Cy ++ (deningerFlatten (G := G) Vy M ++ By)) :
    Vy = Vx.rotate r := by
  set t := Cy.length - Cx.length with hT
  obtain ⟨k, hk⟩ : ∃ k, M - q = k + 1 := ⟨M - q - 1, by omega⟩
  have hkpos : 1 ≤ k := by omega
  have hdropL : (Cy ++ (deningerFlatten (G := G) Vy M ++ By)).drop Cy.length =
      deningerFlatten (G := G) Vy M ++ By := by
    rw [List.drop_append, List.drop_eq_nil_of_le (le_of_eq rfl)]
    simp
  have hdropR : (Cx ++ (deningerFlatten (G := G) Vx M ++ Bx)).drop Cy.length =
      (deningerFlatten (G := G) Vx M ++ Bx).drop t := by
    rw [List.drop_append, List.drop_eq_nil_of_le hCle, List.nil_append, ← hT]
  have hstep : deningerFlatten (G := G) Vy M ++ By =
      (deningerFlatten (G := G) Vx M ++ Bx).drop t := by
    rw [← hdropL, ← hdropR, heq]
  have hlenF : (deningerFlatten (G := G) Vx M).length = M * Vx.length :=
    deningerFlatten_length Vx M
  have htle : t ≤ (deningerFlatten (G := G) Vx M).length := by
    rw [hlenF, ht]
    have : (q + 1) * Vx.length ≤ M * Vx.length :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith [this]
  rw [List.drop_append_of_le_length htle, ht,
    ← List.drop_drop, deningerDrop_mul_flatten Vx q M (by omega), hk,
    deningerDrop_flatten_succ Vx r (by omega) k] at hstep
  have hsplit : deningerFlatten (G := G) Vy M =
      deningerFlatten (G := G) Vy k ++ deningerFlatten (G := G) Vy (M - k) := by
    rw [← deningerFlatten_add]
    congr 1
    omega
  rw [hsplit] at hstep
  simp only [List.append_assoc] at hstep
  have hlenEq : (deningerFlatten (G := G) Vy k).length =
      (deningerFlatten (G := G) (Vx.rotate r) k).length := by
    rw [deningerFlatten_length, deningerFlatten_length, List.length_rotate, hlen]
  have hflat : deningerFlatten (G := G) Vy k = deningerFlatten (G := G) (Vx.rotate r) k :=
    List.append_inj_left hstep hlenEq
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact deningerFlatten_inj Vy (Vx.rotate r) j hflat (by rw [List.length_rotate, hlen])

end RHTower
