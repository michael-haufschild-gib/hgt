import GaloisForLFunctions.RHTower.Deninger.DeningerCycRedPowWord
import GaloisForLFunctions.RHTower.Deninger.DeningerPushoutMetric

/-!
# A long cyclically reduced element is not conjugate to a short one

The powers of an element of length at most one stay of length at most one, so the powers of a
conjugate of it have lengths bounded by twice the length of the conjugator plus one.  The powers of
a cyclically reduced word of at least two letters are cyclically reduced words of the multiplied
length, so their lengths are unbounded.

* `deningerShort_pow_len` : powers of a short element stay short.
* `deningerCycRed_not_conj_short` : the two are never conjugate.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Powers of a short element stay short.** -/
theorem deningerShort_pow_len (u : PushoutI φ) (hu : deningerLen d u ≤ 1) (n : ℕ) :
    deningerLen d (u ^ n) ≤ 1 := by
  classical
  rcases deningerExists_letterProd (d := d) u with ⟨h₀, hu₀, -⟩ | ⟨L, hLne, -, -, hLlen, hu₀⟩
  · rw [hu₀, ← map_pow, deningerLen_base]
    omega
  · obtain ⟨p, hp⟩ : ∃ p, L = [p] := by
      have h1 : 0 < L.length := List.length_pos_iff.2 hLne
      exact List.length_eq_one_iff.mp (by omega)
    have hupow : u ^ n = PushoutI.of (φ := φ) p.1 (p.2 ^ n) := by
      rw [hu₀, hp, deningerLetterProd_cons, deningerLetterProd_nil, mul_one, ← map_pow]
    rw [hupow]
    have := deningerLen_of_mul_le (d := d) p.1 (p.2 ^ n) 1
    rw [mul_one, deningerLen_one] at this
    omega

include d in
/-- **A long cyclically reduced element is not conjugate to a short one.** -/
theorem deningerCycRed_not_conj_short (V : List (Σ i, G i)) (h2 : 2 ≤ V.length)
    (hred : ∀ p ∈ V, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V)
    (hcyc : ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1)
    (g u : PushoutI φ) (hu : deningerLen d u ≤ 1)
    (hconj : deningerLetterProd (φ := φ) V = g⁻¹ * u * g) : False := by
  classical
  set k : ℕ := 2 * deningerLen d g + 1 with hk
  obtain ⟨W, hWlen, -, hWred, hWalt, -, hWprod⟩ :=
    deningerCycRed_pow_word (d := d) V (by
      intro hc
      rw [hc] at h2
      simp at h2) hred halt hcyc k
  have hpow : deningerLetterProd (φ := φ) V ^ (k + 1) = g⁻¹ * u ^ (k + 1) * g := by
    rw [hconj]
    have h := conj_pow (i := k + 1) (a := g⁻¹) (b := u)
    rw [inv_inv] at h
    exact h
  have hlarge : deningerLen d (deningerLetterProd (φ := φ) W) = (k + 1) * V.length :=
    (deningerLen_letterProd (d := d) W hWred hWalt).trans hWlen
  have hsmall : deningerLen d (g⁻¹ * u ^ (k + 1) * g) ≤ 1 + 2 * deningerLen d g := by
    have h1 := deningerLen_conj_le (d := d) g (u ^ (k + 1))
    have h2 := deningerShort_pow_len (d := d) u hu (k + 1)
    omega
  rw [← hpow, hWprod, hlarge] at hsmall
  have : 2 * (k + 1) ≤ (k + 1) * V.length := by
    calc 2 * (k + 1) = (k + 1) * 2 := by ring
      _ ≤ (k + 1) * V.length := Nat.mul_le_mul_left _ h2
  omega

end RHTower
