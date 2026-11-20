import GaloisForLFunctions.HagedornBootstrap.LetterCounting
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.Combinatorics.NecklaceGrowth

/-!
# Hagedorn points of free matrix theories

**Pure Yang–Mills.** The transverse gauge field on `S³` has `2(n² − 1)` letters at energy `n`,
which is the `𝒩 = 4` census law at energy `k/2`. So its letter function in `x` is the `𝒩 = 4` letter
function in `y`: `z_V(x) = (6x² − 2x³)/(1 − x)³ = 2x²(3 − x)/(1 − x)³`. The free Yang–Mills
Hagedorn point is therefore `x_H = 2 − √3`, and the free Yang–Mills Hagedorn temperature
`1/ln(2 + √3)` is exactly twice the free `𝒩 = 4` one.

**Single-trace states.** For a matrix model with `a` letters of unit energy, `z(x) = ax` and the
Hagedorn point is `x_H = 1/a`. The single-trace states are the primitive necklaces of the corpus,
and their generating function `Σ N(a, n) xⁿ` converges for `x < 1/a` and diverges at `x = 1/a`
(for `a ≥ 2`), by the corpus Möbius error bound `aⁿ − nN(a, n) ≤ (n/2) a^{n/2}`: the Hagedorn
temperature is the radius of convergence of the single-trace partition function.
-/

noncomputable section

open Real Finset

namespace GaloisForLFunctions.HagedornBootstrap

open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

/-! ### Pure Yang–Mills -/

/-- The transverse gauge letters `z_V(x) = (6x² − 2x³)/(1 − x)³`. -/
def gaugeLetterZ (x : ℝ) : ℝ := (6 * x ^ 2 - 2 * x ^ 3) / (1 - x) ^ 3

theorem gaugeLetterZ_eq (x : ℝ) : gaugeLetterZ x = singleLetterZ x := by
  unfold gaugeLetterZ singleLetterZ; ring

/-- **The free Yang–Mills Hagedorn point is `x_H = 2 − √3`.** -/
theorem gaugeLetterZ_eq_one_iff {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    gaugeLetterZ x = 1 ↔ x = hagedornY := by
  rw [gaugeLetterZ_eq]; exact singleLetterZ_eq_one_iff h0 h1

/-- **`T_H(Yang–Mills) = 2 T_H(𝒩 = 4)` in the free theory:** `−log x_H^{YM} = β₀/2`. -/
theorem yangMills_hagedornBeta : -Real.log hagedornY = hagedornBeta / 2 := by
  unfold hagedornBeta; ring

theorem yangMills_hagedornTemperature :
    (-Real.log hagedornY)⁻¹ = 2 * hagedornBeta⁻¹ := by
  rw [yangMills_hagedornBeta]
  have := hagedornBeta_pos.ne'
  field_simp

/-! ### Single-trace necklaces -/

/-- Below `x_H = 1/a` the single-trace generating function converges. -/
theorem summable_necklace_gen {a : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx : a * x < 1) :
    Summable (fun n : ℕ => (necklaceCount a (n + 1) : ℝ) * x ^ (n + 1)) := by
  have hg : Summable (fun n : ℕ => ((a : ℝ) * x) ^ (n + 1)) :=
    (summable_geometric_of_lt_one (by positivity) hx).comp_injective (add_left_injective 1)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hg
  have hb := mul_necklaceCount_le_pow a (n + 1) (by omega)
  have hb' : ((n + 1 : ℕ) : ℝ) * (necklaceCount a (n + 1) : ℝ) ≤ (a : ℝ) ^ (n + 1) := by
    exact_mod_cast hb
  have hN : (necklaceCount a (n + 1) : ℝ) ≤ (a : ℝ) ^ (n + 1) := by
    have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    nlinarith [Nat.cast_nonneg (α := ℝ) (necklaceCount a (n + 1))]
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hN (by positivity)

/-- `a^{⌊m/2⌋} ≤ (√a)^m` for `a ≥ 1`. -/
theorem pow_half_le_sqrt_pow {a : ℝ} (ha : 1 ≤ a) (m : ℕ) : a ^ (m / 2) ≤ Real.sqrt a ^ m := by
  have hs : 1 ≤ Real.sqrt a := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt ha
  calc a ^ (m / 2) = Real.sqrt a ^ (2 * (m / 2)) := by
        rw [pow_mul, Real.sq_sqrt (by linarith)]
    _ ≤ Real.sqrt a ^ m := pow_le_pow_right₀ hs (Nat.mul_div_le m 2)

/-- **At the Hagedorn point `x = 1/a` the single-trace generating function diverges** (`a ≥ 2`). -/
theorem not_summable_necklace_at_hagedorn {a : ℕ} (ha : 2 ≤ a) :
    ¬ Summable (fun n : ℕ => (necklaceCount a (n + 1) : ℝ) * (1 / (a : ℝ)) ^ (n + 1)) := by
  intro hs
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (by omega : 1 ≤ a)
  have ha0 : (0 : ℝ) < a := by linarith
  set r := 1 / Real.sqrt a with hr
  have hsqrt : 1 < Real.sqrt a := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast (by omega : 1 < a))
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one (by linarith)]; exact hsqrt
  have hgeo : Summable (fun n : ℕ => r ^ (n + 1)) :=
    (summable_geometric_of_lt_one hr0 hr1).comp_injective (add_left_injective 1)
  -- `1/m ≤ N(m)/aᵐ + r^m` with `m = n + 1`
  have hlow : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤
      (necklaceCount a (n + 1) : ℝ) * (1 / (a : ℝ)) ^ (n + 1) + r ^ (n + 1) := by
    intro n
    set m := n + 1 with hm
    have herr := necklaceCount_error_le_half_pow a n
    rw [max_eq_left (by omega : 1 ≤ a), ← hm] at herr
    have hb := mul_necklaceCount_le_pow a m (by omega)
    have hR : ((a : ℝ) ^ m) ≤ (m : ℝ) * necklaceCount a m + ((m / 2 : ℕ) : ℝ) * (a : ℝ) ^ (m / 2) := by
      have : a ^ m ≤ m * necklaceCount a m + (m / 2) * a ^ (m / 2) := by omega
      exact_mod_cast this
    have hhalf : ((m / 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m 2
    have hpow := pow_half_le_sqrt_pow ha1 m
    have hmpos : (0 : ℝ) < m := by positivity
    have hapos : (0 : ℝ) < (a : ℝ) ^ m := by positivity
    have hsq : Real.sqrt a ^ m / (a : ℝ) ^ m = r ^ m := by
      rw [hr, div_pow, one_pow]
      have : (a : ℝ) ^ m = Real.sqrt a ^ m * Real.sqrt a ^ m := by
        rw [← mul_pow, Real.mul_self_sqrt ha0.le]
      rw [this]; field_simp
    have hcast : ((n : ℝ) + 1) = (m : ℝ) := by rw [hm]; push_cast; ring
    rw [hcast, one_div_pow, mul_one_div]
    rw [div_le_iff₀ hmpos]
    have key : (a : ℝ) ^ m ≤ (m : ℝ) * necklaceCount a m + (m : ℝ) * Real.sqrt a ^ m := by
      have : ((m / 2 : ℕ) : ℝ) * (a : ℝ) ^ (m / 2) ≤ (m : ℝ) * Real.sqrt a ^ m :=
        mul_le_mul hhalf hpow (by positivity) hmpos.le
      linarith
    have e : ((necklaceCount a m : ℝ) / (a : ℝ) ^ m + r ^ m) * (m : ℝ) =
        ((m : ℝ) * necklaceCount a m + (m : ℝ) * Real.sqrt a ^ m) / (a : ℝ) ^ m := by
      rw [← hsq]; field_simp
    rw [e, le_div_iff₀ hapos, one_mul]
    exact key
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hlow (hs.add hgeo)
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp (by simpa using hsum))

end GaloisForLFunctions.HagedornBootstrap
