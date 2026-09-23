/-
Doc 33 §1 (task #131, item 2 — the algebra layer): the k = 1 deck class dichotomy.

At level n = 2 the deck class of a window is ±1 (`deckClass_level_two`), the flip is
characterized by the two basepoint ratios (`deckClass_eq_neg_one_iff`), and over REAL
carrier values (Ξ real on the critical line) every level-2 root value is itself real or
purely imaginary according to the sign of the carrier (`sq_root_real_of_pos`,
`sq_root_im_of_neg`) — the ingredients of the classical sign-change reading. The
root/conjugate ratio lemmas (`sq_conj_ratio_of_pos/neg`) evaluate `z / conj z` to the
carrier's sign; DictionarySign.lean composes them with the line-mirror chart into the
(K1) capstone — no seam continuation is needed.
-/
import GaloisForLFunctions.RHTower.DeckCocycle

namespace RHTower

/-- **Level-2 dichotomy**: the k = 1 deck class is `1` or `−1`. -/
theorem deckClass_level_two {f g₁ g₂ : ℂ → ℂ} {pP pM : ℂ}
    (h₁P : g₁ pP ^ (2 : ℕ) = f pP) (h₂P : g₂ pP ^ (2 : ℕ) = f pP)
    (h₁M : g₁ pM ^ (2 : ℕ) = f pM) (h₂M : g₂ pM ^ (2 : ℕ) = f pM)
    (hfP : f pP ≠ 0) (hfM : f pM ≠ 0) :
    deckClass g₁ g₂ pP pM = 1 ∨ deckClass g₁ g₂ pP pM = -1 := by
  have h := deckClass_pow_eq_one h₁P h₂P h₁M h₂M hfP hfM
  have hfactor : (deckClass g₁ g₂ pP pM - 1) * (deckClass g₁ g₂ pP pM + 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hfactor with h0 | h0
  · exact Or.inl (by linear_combination h0)
  · exact Or.inr (by linear_combination h0)

/-- **Flip criterion**: the class is `−1` iff the basepoint ratios are opposite. -/
theorem deckClass_eq_neg_one_iff {g₁ g₂ : ℂ → ℂ} {pP pM : ℂ}
    (h2M : g₂ pM ≠ 0) (h1M : g₁ pM ≠ 0) :
    deckClass g₁ g₂ pP pM = -1 ↔ g₁ pP / g₂ pP = -(g₁ pM / g₂ pM) := by
  have hM : g₁ pM / g₂ pM ≠ 0 := div_ne_zero h1M h2M
  rw [deckClass, div_eq_iff hM]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    rw [h]
    ring

/-- Over a positive real carrier value, every level-2 root value is REAL:
if `z² = w` with `w` real and `0 < w`, then `z` is real. -/
theorem sq_root_real_of_pos {z w : ℂ} (hw : z ^ (2 : ℕ) = w) (hre : w.im = 0)
    (hpos : 0 < w.re) : z.im = 0 := by
  have him : (z ^ (2 : ℕ)).im = 0 := by rw [hw]; exact hre
  have hpos' : 0 < (z ^ (2 : ℕ)).re := by rw [hw]; exact hpos
  rw [sq, Complex.mul_im] at him
  rw [sq, Complex.mul_re] at hpos'
  rcases mul_eq_zero.mp (by linarith [him] : z.re * z.im = 0) with h | h
  · exfalso
    rw [h] at hpos'
    nlinarith [hpos']
  · exact h

/-- Over a negative real carrier value, every level-2 root value is purely imaginary. -/
theorem sq_root_im_of_neg {z w : ℂ} (hw : z ^ (2 : ℕ) = w) (hre : w.im = 0)
    (hneg : w.re < 0) : z.re = 0 := by
  have him : (z ^ (2 : ℕ)).im = 0 := by rw [hw]; exact hre
  have hneg' : (z ^ (2 : ℕ)).re < 0 := by rw [hw]; exact hneg
  rw [sq, Complex.mul_im] at him
  rw [sq, Complex.mul_re] at hneg'
  rcases mul_eq_zero.mp (by linarith [him] : z.re * z.im = 0) with h | h
  · exact h
  · exfalso
    rw [h] at hneg'
    nlinarith [hneg']

/-- Ratio of two real-valued level-2 roots over the same positive real value:
the ratio is `1` or `−1` and its sign is the product of the roots' signs. -/
theorem real_root_ratio {z₁ z₂ w : ℂ} (h₁ : z₁ ^ (2 : ℕ) = w) (h₂ : z₂ ^ (2 : ℕ) = w)
    (hw : w ≠ 0) : z₁ / z₂ = 1 ∨ z₁ / z₂ = -1 := by
  have h₂0 : z₂ ≠ 0 := fun h0 => hw (by rw [← h₂, h0]; ring)
  have hsq : (z₁ / z₂) ^ (2 : ℕ) = 1 := by
    rw [div_pow, h₁, h₂, div_self hw]
  have hfactor : (z₁ / z₂ - 1) * (z₁ / z₂ + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfactor with h0 | h0
  · exact Or.inl (by linear_combination h0)
  · exact Or.inr (by linear_combination h0)

/-- Over a positive real carrier value the root/conjugate ratio is `+1`. -/
theorem sq_conj_ratio_of_pos {z w : ℂ} (hw : z ^ (2 : ℕ) = w) (hre : w.im = 0)
    (hpos : 0 < w.re) : z / (starRingEnd ℂ) z = 1 := by
  have him : z.im = 0 := sq_root_real_of_pos hw hre hpos
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hw
    have hw0 : w = 0 := by rw [← hw]; norm_num
    rw [hw0] at hpos
    simp at hpos
  rw [Complex.conj_eq_iff_im.mpr him, div_self hz0]

/-- Over a negative real carrier value the root/conjugate ratio is `−1`. -/
theorem sq_conj_ratio_of_neg {z w : ℂ} (hw : z ^ (2 : ℕ) = w) (hre : w.im = 0)
    (hneg : w.re < 0) : z / (starRingEnd ℂ) z = -1 := by
  have hzre : z.re = 0 := sq_root_im_of_neg hw hre hneg
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hw
    have hw0 : w = 0 := by rw [← hw]; norm_num
    rw [hw0] at hneg
    simp at hneg
  have hconj : (starRingEnd ℂ) z = -z := by
    apply Complex.ext
    · simp [hzre]
    · simp
  rw [hconj, div_neg, div_self hz0]

end RHTower
