import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRestrictionToTheFrobeniusGraph

/-!
# The Witt carry is the digit carry up to the Fermat quotient

`ℤ_p` is `𝔽_p[[T]]` with a deformed addition. The deformation is a carry, and it has three
presentations, one for each section of `ℤ → 𝔽_p`.

* **Teichmüller.** `a ↦ [a]` is multiplicative and not additive. The defect
  `[a] + [b] − [a + b]` vanishes on the diagonal, and its necklace coordinate at `p` is the first
  Witt carry polynomial (`natCast_mul_coord_teichmullerCarry`):

    `p · b_p([a] + [b] − [a + b]) = a^p + b^p − (a + b)^p`.

* **Digits and the floor.** For residues `a, b` the digit carry is the integer `κ` with
  `a + b = r + pκ`, `r` the residue of the sum; it is the floor cocycle
  `⌊(a+b)/p⌋ − ⌊a/p⌋ − ⌊b/p⌋` of `RigidArithmeticOfCuts.TheCarryOfTheFloor`.
* **They are one class** (`prime_dvd_wittCarry_sub`). Whenever `a + b = r + pκ`,

    `(a^p + b^p − (a+b)^p)/p ≡ κ + φ(a) + φ(b) − φ(r)  (mod p)`,   `φ(x) = (x^p − x)/p`:

  the Witt carry is the digit carry plus the coboundary of the Fermat quotient. The two sections
  differ by the `p`-derivation, and the carry is the obstruction to its additivity.
-/

open Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The defect of additivity of the Teichmüller section. -/
def teichmullerCarry (a b : ℤ) : ghostRing := teichmuller a + teichmuller b - teichmuller (a + b)

/-- The Teichmüller carry vanishes on the diagonal. -/
theorem ghostComponent_one_teichmullerCarry (a b : ℤ) :
    ghostComponent 1 (teichmullerCarry a b) = 0 := by
  rw [teichmullerCarry, map_sub, map_add, ghostComponent_teichmuller, ghostComponent_teichmuller,
    ghostComponent_teichmuller, PNat.one_coe]
  ring

/-- **The necklace coordinate of the Teichmüller carry at `p` is the Witt carry polynomial.** -/
theorem natCast_mul_coord_teichmullerCarry (a b : ℤ) {p : ℕ+} (hp : p.Prime) :
    ((p : ℕ) : ℤ) * coord (teichmullerCarry a b) p =
      a ^ (p : ℕ) + b ^ (p : ℕ) - (a + b) ^ (p : ℕ) := by
  have h := ghostComponent_prime_eq (teichmullerCarry a b) hp
  rw [ghostComponent_one_teichmullerCarry, zero_add] at h
  rw [← h, teichmullerCarry, map_sub, map_add, ghostComponent_teichmuller,
    ghostComponent_teichmuller, ghostComponent_teichmuller]

/-- The first Witt carry polynomial `(a^p + b^p − (a+b)^p)/p`. -/
def wittCarry (p : ℕ) (a b : ℤ) : ℤ := (a ^ p + b ^ p - (a + b) ^ p) / (p : ℤ)

/-- The Fermat quotient `(x^p − x)/p`. -/
def fermatQuot (p : ℕ) (x : ℤ) : ℤ := (x ^ p - x) / (p : ℤ)

theorem natCast_mul_fermatQuot {p : ℕ} (hp : p.Prime) (x : ℤ) :
    (p : ℤ) * fermatQuot p x = x ^ p - x :=
  Int.mul_ediv_cancel' (prime_dvd_pow_sub_self hp x)

theorem natCast_mul_wittCarry {p : ℕ} (hp : p.Prime) (a b : ℤ) :
    (p : ℤ) * wittCarry p a b = a ^ p + b ^ p - (a + b) ^ p := by
  refine Int.mul_ediv_cancel' ?_
  have h : a ^ p + b ^ p - (a + b) ^ p =
      (a ^ p - a) + (b ^ p - b) - ((a + b) ^ p - (a + b)) := by ring
  rw [h]
  exact dvd_sub (dvd_add (prime_dvd_pow_sub_self hp a) (prime_dvd_pow_sub_self hp b))
    (prime_dvd_pow_sub_self hp (a + b))

/-- **The Witt carry is the digit carry plus the coboundary of the Fermat quotient.** If
`a + b = r + pκ`, then `C_p(a, b) ≡ κ + φ(a) + φ(b) − φ(r) (mod p)`. -/
theorem prime_dvd_wittCarry_sub {p : ℕ} (hp : p.Prime) {a b r κ : ℤ} (h : a + b = r + (p : ℤ) * κ) :
    (p : ℤ) ∣ wittCarry p a b - (κ + fermatQuot p a + fermatQuot p b - fermatQuot p r) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- `(a + b)^p ≡ r^p (mod p²)`
  have hlift : (p : ℤ) ^ (1 + 1) ∣ (a + b) ^ p - r ^ p := by
    refine prime_pow_succ_dvd_pow_sub_pow hp one_ne_zero ?_
    rw [pow_one, h, add_sub_cancel_left]
    exact dvd_mul_right _ _
  have hkey : (p : ℤ) * (wittCarry p a b -
      (κ + fermatQuot p a + fermatQuot p b - fermatQuot p r)) = -((a + b) ^ p - r ^ p) := by
    have h1 := natCast_mul_wittCarry hp a b
    have h2 := natCast_mul_fermatQuot hp a
    have h3 := natCast_mul_fermatQuot hp b
    have h4 := natCast_mul_fermatQuot hp r
    linear_combination h1 - h2 - h3 + h4 + h
  have hd : (p : ℤ) * (p : ℤ) ∣ (p : ℤ) * (wittCarry p a b -
      (κ + fermatQuot p a + fermatQuot p b - fermatQuot p r)) := by
    rw [hkey]
    have := (dvd_neg).mpr hlift
    rwa [show (p : ℤ) ^ (1 + 1) = (p : ℤ) * (p : ℤ) by ring] at this
  exact (mul_dvd_mul_iff_left hp0).mp hd

/-- **For digits**: with `r` the residue of `a + b` modulo `p` and `κ = ⌊(a + b)/p⌋` the digit
carry, `C_p(a, b) ≡ κ + φ(a) + φ(b) − φ(r) (mod p)`. -/
theorem prime_dvd_wittCarry_sub_digit {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    (p : ℤ) ∣ wittCarry p a b - ((((a + b) / p : ℕ) : ℤ) + fermatQuot p a + fermatQuot p b -
      fermatQuot p (((a + b) % p : ℕ) : ℤ)) := by
  refine prime_dvd_wittCarry_sub hp ?_
  have := Nat.mod_add_div (a + b) p
  exact_mod_cast this.symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
