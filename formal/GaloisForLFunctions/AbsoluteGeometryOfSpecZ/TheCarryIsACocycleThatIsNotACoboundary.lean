import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheWittCarryIsTheDigitCarryUpToTheFermatQuotient

/-!
# The carry is a cocycle that is not a coboundary

In `𝔽_p[T]` the digits of a sum are the sums of the digits. In `ℤ` the second digit of a sum is
the sum of the second digits plus the carry of the first.

* **The second digit** (`add_div_eq_add_digit_carry`): `⌊(x+y)/p⌋ = ⌊x/p⌋ + ⌊y/p⌋ + κ(x, y)` with
  `κ(x, y) = ⌊(x mod p + y mod p)/p⌋`. So `ℤ/p²` is the set of pairs of residues with the addition
  of `𝔽_p[T]/(T²)` twisted by `κ`.
* **A cocycle** (`digitCarry_cocycle`): `κ(a, b) + κ(a+b, d) = κ(b, d) + κ(a, b+d)`: both sides
  are the carry of the three residues.
* **Not a coboundary** (`digitCarry_not_coboundary`): there is no `f` with
  `κ(a, b) = f(a) + f(b) − f(a+b)`. Along `1 + 1 + ⋯ + 1` the carries add up to `1` and a
  coboundary adds up to `p·f(1) = 0`.
* **The Witt carry has the same class** (`wittCarry_not_coboundary`): it is the digit carry plus
  the coboundary of the Fermat quotient, so no choice of a section of `ℤ/p² → 𝔽_p` removes it.

The carry is the class of the extension `ℤ/p²` of `𝔽_p` by `𝔽_p`, and the class is not zero: the
deformation from the truncated polynomials to the truncated integers is not trivial in any
coordinates.
-/

open Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- **The second digit of a sum** is the sum of the second digits plus the carry of the first. -/
theorem add_div_eq_add_digit_carry {p : ℕ} (hp : 0 < p) (x y : ℕ) :
    (x + y) / p = x / p + y / p + (x % p + y % p) / p := by
  rw [Nat.add_div hp]
  congr 1
  have hx := Nat.mod_lt x hp
  have hy := Nat.mod_lt y hp
  split_ifs with h
  · exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm
  · exact (Nat.div_eq_of_lt (by omega)).symm

/-- The digit carry of two residues modulo `p`. -/
def digitCarry (p : ℕ) [NeZero p] (a b : ZMod p) : ZMod p := (((a.val + b.val) / p : ℕ) : ZMod p)

/-- **The carry is a cocycle.** -/
theorem digitCarry_cocycle (p : ℕ) [NeZero p] (a b d : ZMod p) :
    digitCarry p a b + digitCarry p (a + b) d = digitCarry p b d + digitCarry p a (b + d) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have e1 : a.val + b.val + d.val =
      p * ((a.val + b.val) / p) + ((a.val + b.val) % p + d.val) := by
    linarith [Nat.div_add_mod (a.val + b.val) p]
  have e2 : a.val + b.val + d.val =
      p * ((b.val + d.val) / p) + (a.val + (b.val + d.val) % p) := by
    linarith [Nat.div_add_mod (b.val + d.val) p]
  have h1 : (a.val + b.val) / p + ((a.val + b.val) % p + d.val) / p =
      (a.val + b.val + d.val) / p := by
    rw [e1, Nat.mul_add_div hp]
  have h2 : (b.val + d.val) / p + (a.val + (b.val + d.val) % p) / p =
      (a.val + b.val + d.val) / p := by
    rw [e2, Nat.mul_add_div hp]
  unfold digitCarry
  rw [ZMod.val_add a b, ZMod.val_add b d, ← Nat.cast_add, ← Nat.cast_add, h1, h2]

/-- **The carry is not a coboundary.** -/
theorem digitCarry_not_coboundary (p : ℕ) [Fact (1 < p)] :
    ¬ ∃ f : ZMod p → ZMod p, ∀ a b : ZMod p, digitCarry p a b = f a + f b - f (a + b) := by
  rintro ⟨f, hf⟩
  have hp : 1 < p := Fact.out
  -- the carries along `0, 1, …, p − 1` add up to `1`
  have hsum : ∑ k ∈ range p, digitCarry p (k : ZMod p) 1 = 1 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun k hk => by
      have hk' : k < q + 1 := by
        have := Finset.mem_range.mp hk
        omega
      rw [digitCarry, ZMod.val_natCast_of_lt hk', ZMod.val_one,
        Nat.div_eq_of_lt (by
          have := Finset.mem_range.mp hk
          omega), Nat.cast_zero], zero_add, digitCarry,
      ZMod.val_natCast_of_lt (Nat.lt_succ_self q), ZMod.val_one, Nat.div_self (Nat.succ_pos q),
      Nat.cast_one]
  -- a coboundary adds up to `p·f(1) = 0`
  have hcob : ∑ k ∈ range p, digitCarry p (k : ZMod p) 1 = 0 := by
    have hterm : ∀ k ∈ range p, digitCarry p (k : ZMod p) 1 =
        f 1 + (f (k : ZMod p) - f ((k + 1 : ℕ) : ZMod p)) := fun k _ => by
      rw [hf, Nat.cast_add, Nat.cast_one]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_range_sub' (fun k : ℕ => f (k : ZMod p)), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ZMod.natCast_self, zero_mul, Nat.cast_zero, sub_self, add_zero]
  rw [hsum] at hcob
  exact one_ne_zero hcob

/-- **The Witt carry is not a coboundary modulo `p`.** No function `f` on the residues has
`(a^p + b^p − (a+b)^p)/p ≡ f(a) + f(b) − f(a+b)` on the representatives `0, …, p − 1`. -/
theorem wittCarry_not_coboundary {p : ℕ} (hp : p.Prime) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ¬ ∃ f : ZMod p → ZMod p, ∀ a b : ZMod p,
      ((wittCarry p (a.val : ℤ) (b.val : ℤ) : ℤ) : ZMod p) = f a + f b - f (a + b) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  rintro ⟨f, hf⟩
  refine digitCarry_not_coboundary p
    ⟨fun a => f a - ((fermatQuot p (a.val : ℤ) : ℤ) : ZMod p), fun a b => ?_⟩
  have h := prime_dvd_wittCarry_sub_digit hp a.val b.val
  rw [← ZMod.val_add a b] at h
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast] at h0
  rw [digitCarry]
  linear_combination -h0 + hf a b

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
