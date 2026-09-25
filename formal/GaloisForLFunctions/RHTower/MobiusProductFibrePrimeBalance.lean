import GaloisForLFunctions.RHTower.MobiusProductFibreVariation

/-!
# Prime insertion and factorisation balance at the Gamma--Hankel boundary

At exponent one, putting a new prime on either side of a positive product
fibre has a sharp sign boundary. The two placements minus the old Cauchy atom
have sign determined by `(a+b)^2 - (p-1)^2*a*b`. Scale two is strictly
expansive, scale three is nonnegative and neutral on the diagonal, and every
scale greater than three has both balanced and unbalanced chambers.

The literal Möbius source has the same two-placement defect with its arithmetic
sign reversed. In particular, the two `m:3m` off-diagonal entries exactly pay
the old `m:m` diagonal entry when `3` does not divide `m`. This is an exact
source-side local law, not a global bound on the signed covariance: all other
pair channels and the child diagonal remain.
-/

namespace RHTower.MobiusProductFibre

noncomputable section

/-- Change of one positive Cauchy atom under the two placements of scale `p`. -/
def primeSplitDefect (p a b : ℝ) : ℝ :=
  1 / (p * a + b) + 1 / (a + p * b) - 1 / (a + b)

/-- Exact factorisation-balance numerator of the prime-split defect. -/
theorem primeSplitDefect_eq
    {p a b : ℝ} (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) :
    primeSplitDefect p a b =
      ((a + b) ^ 2 - (p - 1) ^ 2 * a * b) /
        ((a + b) * (p * a + b) * (a + p * b)) := by
  have h1 : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have h2 : p * a + b ≠ 0 := ne_of_gt (add_pos (mul_pos hp ha) hb)
  have h3 : a + p * b ≠ 0 := ne_of_gt (add_pos ha (mul_pos hp hb))
  unfold primeSplitDefect
  field_simp
  ring

/-- The defect is positive precisely in the unbalanced chamber. -/
theorem primeSplitDefect_pos_iff
    {p a b : ℝ} (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) :
    0 < primeSplitDefect p a b ↔
      (p - 1) ^ 2 * a * b < (a + b) ^ 2 := by
  rw [primeSplitDefect_eq hp ha hb]
  have hd : 0 < (a + b) * (p * a + b) * (a + p * b) := by positivity
  constructor
  · intro h
    have := (lt_div_iff₀ hd).mp h
    linarith
  · intro h
    exact div_pos (by linarith) hd

/-- Every scale greater than three contracts the balanced pair. -/
theorem primeSplitDefect_neg_balanced
    {p a : ℝ} (hp : 3 < p) (ha : 0 < a) :
    primeSplitDefect p a a < 0 := by
  rw [primeSplitDefect_eq (by linarith : 0 < p) ha ha]
  have hd : 0 < (a + a) * (p * a + a) * (a + p * a) := by positivity
  have hn : (a + a) ^ 2 - (p - 1) ^ 2 * a * a < 0 := by
    have hpp : 0 < p - 3 := by linarith
    have hpa : 0 < p + 1 := by linarith
    have hsq : 0 < a ^ 2 := sq_pos_of_pos ha
    nlinarith [mul_pos (mul_pos hpp hpa) hsq]
  exact div_neg_of_neg_of_pos hn hd

/-- Every positive scale expands some unbalanced pair. -/
theorem primeSplitDefect_pos_unbalanced
    {p : ℝ} (hp : 0 < p) :
    0 < primeSplitDefect p 1 (p ^ 2) := by
  have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp
  rw [primeSplitDefect_eq hp (by norm_num) hp2]
  have hd : 0 < (1 + p ^ 2) * (p * 1 + p ^ 2) * (1 + p * p ^ 2) := by positivity
  have hn : (1 + p ^ 2) ^ 2 - (p - 1) ^ 2 * 1 * p ^ 2 =
      2 * p ^ 3 + p ^ 2 + 1 := by ring
  rw [hn]
  exact div_pos (by positivity) hd

/-- Scale two expands every positive pair. -/
theorem primeSplitDefect_pos_two
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < primeSplitDefect 2 a b := by
  rw [primeSplitDefect_pos_iff (by norm_num) ha hb]
  nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]

/-- Scale three is the exact transition: nonnegative, zero at balance. -/
theorem primeSplitDefect_nonneg_three
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ primeSplitDefect 3 a b := by
  rw [primeSplitDefect_eq (by norm_num) ha hb]
  have hd : 0 ≤ (a + b) * (3 * a + b) * (a + 3 * b) := by positivity
  have hn : (a + b) ^ 2 - (3 - 1) ^ 2 * a * b = (a - b) ^ 2 := by ring
  rw [hn]
  exact div_nonneg (sq_nonneg _) hd

/-- Literal Möbius sign reversal when a new prime is inserted. -/
theorem mu_prime_mul {p m : ℕ} (hp : p.Prime) (hpm : Nat.Coprime p m) :
    mu (p * m) = -mu m := by
  unfold mu
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpm]
  rw [ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

/-- One old Möbius pair and its two prime-insertion children have the exact
factorisation-balance defect, with no averaging or discarded coefficient. -/
theorem source_prime_split_balance
    {p m n : ℕ} (hp : p.Prime)
    (hpm : Nat.Coprime p m) (hpn : Nat.Coprime p n) :
    mu m * mu n / ((m + n : ℕ) : ℝ) +
      mu (p * m) * mu n / ((p * m + n : ℕ) : ℝ) +
      mu m * mu (p * n) / ((m + p * n : ℕ) : ℝ) =
      -(mu m * mu n) * primeSplitDefect p m n := by
  rw [mu_prime_mul hp hpm, mu_prime_mul hp hpn]
  unfold primeSplitDefect
  push_cast
  ring

/-- At prime three the two old-to-child cross entries exactly cancel the old
diagonal entry. The child diagonal and every other pair are still present. -/
theorem source_three_diagonal_cross_cancel
    {m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime 3 m) :
    mu m * mu m / ((m + m : ℕ) : ℝ) +
      mu (3 * m) * mu m / ((3 * m + m : ℕ) : ℝ) +
      mu m * mu (3 * m) / ((m + 3 * m : ℕ) : ℝ) = 0 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdef : primeSplitDefect 3 (m : ℝ) (m : ℝ) = 0 := by
    rw [primeSplitDefect_eq (by norm_num) hmR hmR]
    have hn : ((m : ℝ) + m) ^ 2 - (3 - 1) ^ 2 * (m : ℝ) * m = 0 := by ring
    rw [hn, zero_div]
  simpa [hdef] using source_prime_split_balance Nat.prime_three hcop hcop

end
end RHTower.MobiusProductFibre
