import GaloisForLFunctions.RHTower.MobiusProductFibreVariation

namespace RHTower.MobiusProductFibre

noncomputable section

def primeSplitDefect (p a b : ℝ) : ℝ :=
  1 / (p * a + b) + 1 / (a + p * b) - 1 / (a + b)

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

theorem primeSplitDefect_pos_two
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < primeSplitDefect 2 a b := by
  rw [primeSplitDefect_pos_iff (by norm_num) ha hb]
  nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]

theorem primeSplitDefect_nonneg_three
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ primeSplitDefect 3 a b := by
  rw [primeSplitDefect_eq (by norm_num) ha hb]
  have hd : 0 ≤ (a + b) * (3 * a + b) * (a + 3 * b) := by positivity
  have hn : (a + b) ^ 2 - (3 - 1) ^ 2 * a * b = (a - b) ^ 2 := by ring
  rw [hn]
  exact div_nonneg (sq_nonneg _) hd

theorem mu_prime_mul {p m : ℕ} (hp : p.Prime) (hpm : Nat.Coprime p m) :
    mu (p * m) = -mu m := by
  unfold mu
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpm]
  rw [ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

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
