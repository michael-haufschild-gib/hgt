import GaloisForLFunctions.RHTower.DeningerPowerLength

/-!
# The two exponent comparison

Two elements with the same power have cyclically reduced parts of the same length, and are
themselves of the same length.  Comparing at one exponent leaves the constant term of the linear
growth undetermined; comparing at two exponents cancels it.

* `deningerLen_eq_of_pow_eq` : the comparison.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The two exponent comparison.**  If two elements presented as conjugates of cyclically reduced
words of at least two letters have the same `n`-th power, their cyclically reduced parts have the
same length and the elements have the same length. -/
theorem deningerLen_eq_of_pow_eq
    (Cx Rx Vx Cy Ry Vy : List (Σ i, G i))
    (hxred : ∀ p ∈ Cx ++ Rx, p.2 ∉ (φ p.1).range)
    (hxalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (Cx ++ Rx))
    (hVxne : Vx ≠ []) (hVxred : ∀ p ∈ Vx, p.2 ∉ (φ p.1).range)
    (hVxalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) Vx)
    (hVxcyc : ∀ p ∈ Vx.getLast?, ∀ q ∈ Vx.head?, p.1 ≠ q.1)
    (hxhead : Vx.head?.map Sigma.fst = Rx.head?.map Sigma.fst)
    (hxprod : deningerLetterProd (φ := φ) Rx =
      deningerLetterProd (φ := φ) Vx * (deningerLetterProd (φ := φ) Cx)⁻¹)
    (hyred : ∀ p ∈ Cy ++ Ry, p.2 ∉ (φ p.1).range)
    (hyalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (Cy ++ Ry))
    (hVyne : Vy ≠ []) (hVyred : ∀ p ∈ Vy, p.2 ∉ (φ p.1).range)
    (hVyalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) Vy)
    (hVycyc : ∀ p ∈ Vy.getLast?, ∀ q ∈ Vy.head?, p.1 ≠ q.1)
    (hyhead : Vy.head?.map Sigma.fst = Ry.head?.map Sigma.fst)
    (hyprod : deningerLetterProd (φ := φ) Ry =
      deningerLetterProd (φ := φ) Vy * (deningerLetterProd (φ := φ) Cy)⁻¹)
    (m : ℕ)
    (heq : (deningerLetterProd (φ := φ) (Cx ++ Rx)) ^ (m + 1) =
      (deningerLetterProd (φ := φ) (Cy ++ Ry)) ^ (m + 1)) :
    Vx.length = Vy.length ∧
      deningerLen d (deningerLetterProd (φ := φ) (Cx ++ Rx)) =
        deningerLen d (deningerLetterProd (φ := φ) (Cy ++ Ry)) := by
  have heq2 : (deningerLetterProd (φ := φ) (Cx ++ Rx)) ^ (2 * m + 2) =
      (deningerLetterProd (φ := φ) (Cy ++ Ry)) ^ (2 * m + 2) := by
    have hx : ∀ g : PushoutI φ, g ^ (2 * m + 2) = (g ^ (m + 1)) ^ (2 : ℕ) := by
      intro g
      rw [← pow_mul]
      ring_nf
    rw [hx, hx, heq]
  have e1 : deningerLen d (deningerLetterProd (φ := φ) (Cx ++ Rx)) + m * Vx.length =
      deningerLen d (deningerLetterProd (φ := φ) (Cy ++ Ry)) + m * Vy.length := by
    rw [← deningerLen_conj_pow_sub (d := d) Cx Rx Vx hxred hxalt hVxne hVxred hVxalt hVxcyc
        hxhead hxprod m,
      ← deningerLen_conj_pow_sub (d := d) Cy Ry Vy hyred hyalt hVyne hVyred hVyalt hVycyc
        hyhead hyprod m, heq]
  have e2 : deningerLen d (deningerLetterProd (φ := φ) (Cx ++ Rx)) + (2 * m + 1) * Vx.length =
      deningerLen d (deningerLetterProd (φ := φ) (Cy ++ Ry)) + (2 * m + 1) * Vy.length := by
    rw [← deningerLen_conj_pow_sub (d := d) Cx Rx Vx hxred hxalt hVxne hVxred hVxalt hVxcyc
        hxhead hxprod (2 * m + 1),
      ← deningerLen_conj_pow_sub (d := d) Cy Ry Vy hyred hyalt hVyne hVyred hVyalt hVycyc
        hyhead hyprod (2 * m + 1), heq2]
  have h3 : (2 * m + 1) * Vx.length = m * Vx.length + (m + 1) * Vx.length := by ring
  have h4 : (2 * m + 1) * Vy.length = m * Vy.length + (m + 1) * Vy.length := by ring
  rw [h3, h4, ← add_assoc, ← add_assoc, e1] at e2
  have hV : Vx.length = Vy.length :=
    Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) (Nat.add_left_cancel e2)
  refine ⟨hV, ?_⟩
  rw [hV] at e1
  exact Nat.add_right_cancel e1

end RHTower
