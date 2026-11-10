import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitContents
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Rat.Floor

/-!
# Integral layers inside a digit-content vector

For cyclic caps b, the minimum of `p^k b(h+k)` over one period is bounded by b
and satisfies `d(h) ≤ p d(h+1)`. At each coordinate it equals either the cap or
the neighbouring bound. Applied to `b(h)=ceil(c(h))−1`, this rounds inverse
content down without making its cyclic difference negative or exceeding the
original integral digit counts.

If all coordinates of c exceed an integer m at least one, the resulting integral
vector d has coordinates at least m. Its cyclic difference and the remaining
digit counts are both nonzero. This is the extraction step for positive
carry-free compositions with divisible parts.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {s : ℕ} [NeZero s]

/-- Cyclic minimum of the geometrically weighted caps. -/
def cyclicMinorant (p : ℕ) (b : ZMod s → ℤ) (h : ZMod s) : ℤ :=
  (range s).inf' ⟨0, mem_range.mpr (NeZero.pos s)⟩
    (fun k => (p : ℤ) ^ k * b (h + k))

theorem cyclicMinorant_le (p : ℕ) (b : ZMod s → ℤ) (h : ZMod s) :
    cyclicMinorant p b h ≤ b h := by
  have hh := inf'_le (fun k : ℕ => (p : ℤ) ^ k * b (h + k))
    (mem_range.mpr (NeZero.pos s) : 0 ∈ range s)
  simpa only [cyclicMinorant, pow_zero, Nat.cast_zero, add_zero, one_mul] using hh

theorem le_cyclicMinorant {p : ℕ} (hp : 1 ≤ p) {b : ZMod s → ℤ} {m : ℤ}
    (hm : 0 ≤ m) (hb : ∀ h, m ≤ b h) (h : ZMod s) : m ≤ cyclicMinorant p b h := by
  apply le_inf'
  intro k _
  have hpk : (1 : ℤ) ≤ (p : ℤ) ^ k := one_le_pow₀ (by exact_mod_cast hp)
  exact (hb _).trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hpk (hm.trans (hb _)))

theorem cyclicMinorant_le_mul_next {p : ℕ} (hp : 1 ≤ p) {b : ZMod s → ℤ}
    (hb : ∀ h, 0 ≤ b h) (h : ZMod s) :
    cyclicMinorant p b h ≤ p * cyclicMinorant p b (h + 1) := by
  obtain ⟨k, hk, he⟩ := exists_mem_eq_inf'
    (show (range s).Nonempty from ⟨0, mem_range.mpr (NeZero.pos s)⟩)
    (fun k => (p : ℤ) ^ k * b (h + 1 + k))
  change cyclicMinorant p b (h + 1) = _ at he
  have hi : h + 1 + (k : ZMod s) = h + (k + 1 : ℕ) := by push_cast; ring
  rw [he, hi, ← mul_assoc, ← pow_succ']
  by_cases hk1 : k + 1 < s
  · exact inf'_le _ (mem_range.mpr hk1)
  · have hks : k + 1 = s := by have := mem_range.mp hk; omega
    rw [hks, ZMod.natCast_self, add_zero]
    have hpk : (1 : ℤ) ≤ (p : ℤ) ^ s := one_le_pow₀ (by exact_mod_cast hp)
    have hh := mul_le_mul_of_nonneg_right hpk (hb h)
    exact (cyclicMinorant_le p b h).trans (by simpa only [one_mul] using hh)

theorem cyclicMinorant_eq_cap_or_mul_next {p : ℕ} (hp : 1 ≤ p) {b : ZMod s → ℤ}
    (hb : ∀ h, 0 ≤ b h) (h : ZMod s) :
    cyclicMinorant p b h = b h ∨
      cyclicMinorant p b h = p * cyclicMinorant p b (h + 1) := by
  obtain ⟨k, hk, he⟩ := exists_mem_eq_inf'
    (show (range s).Nonempty from ⟨0, mem_range.mpr (NeZero.pos s)⟩)
    (fun k => (p : ℤ) ^ k * b (h + k))
  change cyclicMinorant p b h = _ at he
  cases k with
  | zero => exact Or.inl (by simpa only [pow_zero, Nat.cast_zero, add_zero, one_mul] using he)
  | succ k =>
    right
    apply le_antisymm (cyclicMinorant_le_mul_next hp hb h)
    have hk' : k ∈ range s := mem_range.mpr (by have := mem_range.mp hk; omega)
    have hle : cyclicMinorant p b (h + 1) ≤ (p : ℤ) ^ k * b (h + 1 + k) := inf'_le _ hk'
    have hh := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg p)
    rw [he]
    have hi : h + 1 + (k : ZMod s) = h + (k + 1 : ℕ) := by push_cast; ring
    simpa only [hi, pow_succ', mul_assoc] using hh

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {s : ℕ} [NeZero s]

/-- Integer caps immediately below a rational vector. -/
def strictIntegerCap (c : ZMod s → ℚ) (h : ZMod s) : ℤ := ⌈c h⌉ - 1

omit [NeZero s] in
theorem strictIntegerCap_lt (c : ZMod s → ℚ) (h : ZMod s) :
    (strictIntegerCap c h : ℚ) < c h := by
  have hh := Int.ceil_lt_add_one (c h)
  dsimp only [strictIntegerCap]
  push_cast
  linarith only [hh]

omit [NeZero s] in
theorem le_strictIntegerCap {c : ZMod s → ℚ} {m : ℤ}
    (hc : ∀ h, (m : ℚ) < c h) (h : ZMod s) : m ≤ strictIntegerCap c h := by
  have hh := Int.lt_ceil.mpr (hc h)
  dsimp only [strictIntegerCap]
  omega

theorem cyclicMinorant_cap_lt (p : ℕ) (c : ZMod s → ℚ) (h : ZMod s) :
    (cyclicMinorant p (strictIntegerCap c) h : ℚ) < c h := by
  have hh : (cyclicMinorant p (strictIntegerCap c) h : ℚ) ≤ (strictIntegerCap c h : ℚ) :=
    by exact_mod_cast cyclicMinorant_le p (strictIntegerCap c) h
  exact hh.trans_lt (strictIntegerCap_lt c h)

/-- Rounding inverse content preserves each nonnegative integral digit count. -/
theorem cyclicDifference_minorant_cap_bounds (p : ℕ) (hp : 2 ≤ p)
    (c : ZMod s → ℚ) (u : ZMod s → ℤ) (hu : ∀ h, 0 ≤ u h)
    (hc : ∀ h, 1 < c h)
    (hE : cyclicDifference (p : ℚ) c = fun h => (u h : ℚ)) (h : ZMod s) :
    0 ≤ cyclicDifference (p : ℤ) (cyclicMinorant p (strictIntegerCap c)) h ∧
      cyclicDifference (p : ℤ) (cyclicMinorant p (strictIntegerCap c)) h ≤ u h := by
  have hp1 : 1 ≤ p := by omega
  have hb (j : ZMod s) : 0 ≤ strictIntegerCap c j :=
    (by norm_num : (0 : ℤ) ≤ 1).trans (le_strictIntegerCap hc j)
  have hnext := cyclicMinorant_le_mul_next hp1 hb h
  constructor
  · exact sub_nonneg.mpr hnext
  · rcases cyclicMinorant_eq_cap_or_mul_next hp1 hb h with hd | hd
    · have hpQ : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
      have hsmall := mul_lt_mul_of_pos_left (cyclicMinorant_cap_lt p c (h + 1)) hpQ
      have hceil := Int.le_ceil (c h)
      have he := congrFun hE h
      dsimp only [cyclicDifference] at he
      have hlt : ((cyclicDifference (p : ℤ) (cyclicMinorant p (strictIntegerCap c)) h : ℤ) : ℚ) <
          (u h : ℚ) + 1 := by
        dsimp only [cyclicDifference]
        rw [hd]
        simp only [strictIntegerCap, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one]
        linarith only [hsmall, hceil, he]
      have hltZ : cyclicDifference (p : ℤ) (cyclicMinorant p (strictIntegerCap c)) h < u h + 1 :=
        by exact_mod_cast hlt
      omega
    · dsimp only [cyclicDifference]
      rw [hd, sub_self]
      exact hu h

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {s : ℕ} [NeZero s]

/-- A positive inverse coordinate prevents a nonnegative cyclic difference from vanishing. -/
theorem exists_pos_of_cyclicDifference (p : ℕ) (hp : 2 ≤ p)
    (c : ZMod s → ℚ) (u : ZMod s → ℤ) (hu : ∀ h, 0 ≤ u h) (hc : 0 < c 0)
    (hE : cyclicDifference (p : ℚ) c = fun h => (u h : ℚ)) : ∃ h, 0 < u h := by
  by_contra! hn
  have hu0 (h : ZMod s) : u h = 0 := le_antisymm (hn h) (hu h)
  have he0 : cyclicDifference (p : ℚ) c = cyclicDifference (p : ℚ) (0 : ZMod s → ℚ) := by
    funext h
    have hh := congrFun hE h
    simpa only [hu0, Int.cast_zero, cyclicDifference, Pi.zero_apply, mul_zero, sub_self] using hh
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpow : (p : ℚ) ^ s ≠ 1 := ne_of_gt (one_lt_pow₀ hpQ (NeZero.ne s))
  have hz := congrFun (cyclicDifference_injective (p : ℚ) hpow he0) 0
  change c 0 = 0 at hz
  exact (ne_of_gt hc) hz

/-- A proper positive integral layer can be removed whenever every inverse coordinate exceeds m. -/
theorem exists_integral_content_layer (p m : ℕ) (hp : 2 ≤ p) (hm : 1 ≤ m)
    (c : ZMod s → ℚ) (u : ZMod s → ℤ) (hu : ∀ h, 0 ≤ u h)
    (hc : ∀ h, (m : ℚ) < c h)
    (hE : cyclicDifference (p : ℚ) c = fun h => (u h : ℚ)) :
    ∃ d : ZMod s → ℤ,
      (∀ h, (m : ℤ) ≤ d h ∧ (d h : ℚ) < c h) ∧
      (∀ h, 0 ≤ cyclicDifference (p : ℤ) d h ∧ cyclicDifference (p : ℤ) d h ≤ u h) ∧
      (∃ h, 0 < cyclicDifference (p : ℤ) d h) ∧
      (∃ h, cyclicDifference (p : ℤ) d h < u h) := by
  let d := cyclicMinorant p (strictIntegerCap c)
  have hp1 : 1 ≤ p := by omega
  have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hc1 (h : ZMod s) : 1 < c h := hmQ.trans_lt (hc h)
  have hcap (h : ZMod s) : (m : ℤ) ≤ strictIntegerCap c h :=
    le_strictIntegerCap (by simpa only [Int.cast_natCast] using hc) h
  have hlow (h : ZMod s) : (m : ℤ) ≤ d h :=
    le_cyclicMinorant hp1 (Nat.cast_nonneg m) hcap h
  have hlt (h : ZMod s) : (d h : ℚ) < c h := cyclicMinorant_cap_lt p c h
  have hb (h : ZMod s) := cyclicDifference_minorant_cap_bounds p hp c u hu hc1 hE h
  refine ⟨d, fun h => ⟨hlow h, hlt h⟩, hb, ?_, ?_⟩
  · apply exists_pos_of_cyclicDifference p hp (fun h => (d h : ℚ))
      (cyclicDifference (p : ℤ) d) (fun h => (hb h).1)
    · have hh : 0 < d 0 := by have := hlow 0; omega
      exact_mod_cast hh
    · funext h
      simp only [cyclicDifference, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  · have hrem : cyclicDifference (p : ℚ) (fun h => c h - (d h : ℚ)) =
        fun h => ((u h - cyclicDifference (p : ℤ) d h : ℤ) : ℚ) := by
      funext h
      have hh := congrFun hE h
      dsimp only [cyclicDifference] at hh ⊢
      push_cast
      linear_combination hh
    obtain ⟨h, hh⟩ := exists_pos_of_cyclicDifference p hp (fun h => c h - (d h : ℚ))
      (fun h => u h - cyclicDifference (p : ℤ) d h)
      (fun h => sub_nonneg.mpr (hb h).2) (sub_pos.mpr (hlt 0)) hrem
    exact ⟨h, sub_pos.mp hh⟩

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.exists_integral_content_layer
