import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheBlockMatrixOfTheDegreesTheJetsAndTheFloorMaps
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper
import GaloisForLFunctions.RHTower.HarmonicGeometricBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The first block matrices of ratio four and seven have a margin

The block matrix of the degrees, the jets and the floor maps on the blocks `(a, a + 1]`,
`1 ≤ a ≤ 3`, with the contacts `k ≤ 4`, and on the blocks `1 ≤ a ≤ 6` with the contacts `k ≤ 7`,
is positive definite:

* `sum_blockMatrix_four_ge`: `Σ σ_j σ_l blockMatrix 4 (1 + j) (1 + l) ≥ (1/20) Σ σ_j²` on three
  blocks (contacts of `2` and `3`);
* `sum_blockMatrix_seven_ge`: `Σ σ_j σ_l blockMatrix 7 (1 + j) (1 + l) ≥ (1/100) Σ σ_j²` on six
  blocks (contacts of `2`, `3`, `4`, `5`);
* `sum_blockMatrix_four_fine_ge`: `Σ σ_j σ_l blockMatrix 4 (2 + j) (2 + l) ≥ (1/100) Σ σ_j²` on
  the six blocks `2, …, 7`: the window of ratio four on blocks of half the size.

The entries are integer combinations of `γ`, `log π` and the logarithms of the primes up to `13`.
Each entry is enclosed within `10⁻⁴` of a decimal table (`table4`, `table7`), and the form of the
table minus the margin is a sum of squares with decimal coefficients plus a diagonally dominant
remainder. On six blocks the matrix is not diagonally dominant: the first block has the diagonal
`0.19` and five off-diagonal entries of size up to `0.19`.

The logarithms are enclosed through `log((1 + y)/(1 − y)) = 2(y + y³/3 + …)` at the ratios
`9/8`, `128/125`, `50/49`, `121/120`, `169/168`.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Logarithms of the primes up to `13` -/

/-- Two terms of the series of `log((1 + y)/(1 − y))`. -/
theorem two_terms_le_log_div {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    2 * y + 2 * y ^ 3 / 3 ≤ Real.log ((1 + y) / (1 - y)) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := y) (by rwa [abs_of_nonneg hy0])
  have hle := sum_le_hasSum (Finset.range 2)
    (fun k _ => mul_nonneg (by positivity) (pow_nonneg hy0 _)) h
  rw [Real.log_div (by linarith) (by linarith)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
  norm_num at hle
  linarith

theorem log_nine_eighths_mem :
    (0.11778275 : ℝ) ≤ Real.log (9 / 8) ∧ Real.log (9 / 8) ≤ 0.11778323 := by
  have h1 := two_terms_le_log_div (y := 1 / 17) (by norm_num) (by norm_num)
  have h2 := RHTower.log_le_geometric_cubic (x := 9 / 8) (by norm_num)
  rw [show ((1 : ℝ) + 1 / 17) / (1 - 1 / 17) = 9 / 8 by norm_num] at h1
  constructor
  · refine le_trans ?_ h1
    norm_num
  · refine h2.trans ?_
    norm_num

theorem log_three_mem : (1.0986121 : ℝ) < Real.log 3 ∧ Real.log 3 < 1.0986124 := by
  have h : Real.log (9 / 8) = 2 * Real.log 3 - 3 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h1 := log_nine_eighths_mem
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  constructor <;> linarith [h1.1, h1.2]

theorem log_five_mem : (1.6094379 : ℝ) < Real.log 5 ∧ Real.log 5 < 1.609438 := by
  have h : Real.log (128 / 125) = 7 * Real.log 2 - 3 * Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (128 : ℝ) = 2 ^ 7 by norm_num,
      show (125 : ℝ) = 5 ^ 3 by norm_num, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h1 := two_terms_le_log_div (y := 3 / 253) (by norm_num) (by norm_num)
  have h2 := RHTower.log_le_geometric_cubic (x := 128 / 125) (by norm_num)
  rw [show ((1 : ℝ) + 3 / 253) / (1 - 3 / 253) = 128 / 125 by norm_num] at h1
  have h1' : (0.02371652 : ℝ) ≤ Real.log (128 / 125) := le_trans (by norm_num) h1
  have h2' : Real.log (128 / 125) ≤ (0.02371653 : ℝ) := h2.trans (by norm_num)
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  constructor <;> linarith

theorem log_seven_mem : (1.9459101 : ℝ) < Real.log 7 ∧ Real.log 7 < 1.9459103 := by
  have h : Real.log (50 / 49) = Real.log 2 + 2 * Real.log 5 - 2 * Real.log 7 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (50 : ℝ) = 2 * 5 ^ 2 by norm_num,
      show (49 : ℝ) = 7 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have h1 := two_terms_le_log_div (y := 1 / 99) (by norm_num) (by norm_num)
  have h2 := RHTower.log_le_geometric_cubic (x := 50 / 49) (by norm_num)
  rw [show ((1 : ℝ) + 1 / 99) / (1 - 1 / 99) = 50 / 49 by norm_num] at h1
  have h1' : (0.0202027 : ℝ) ≤ Real.log (50 / 49) := le_trans (by norm_num) h1
  have h2' : Real.log (50 / 49) ≤ (0.02020271 : ℝ) := h2.trans (by norm_num)
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  have h5 := log_five_mem
  constructor <;> linarith [h5.1, h5.2]

theorem log_eleven_mem : (2.3978951 : ℝ) < Real.log 11 ∧ Real.log 11 < 2.3978954 := by
  have h : Real.log (121 / 120) =
      2 * Real.log 11 - 3 * Real.log 2 - Real.log 3 - Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (121 : ℝ) = 11 ^ 2 by norm_num,
      show (120 : ℝ) = 2 ^ 3 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h1 := two_terms_le_log_div (y := 1 / 241) (by norm_num) (by norm_num)
  have h2 := RHTower.log_le_geometric_cubic (x := 121 / 120) (by norm_num)
  rw [show ((1 : ℝ) + 1 / 241) / (1 - 1 / 241) = 121 / 120 by norm_num] at h1
  have h1' : (0.0082988 : ℝ) ≤ Real.log (121 / 120) := le_trans (by norm_num) h1
  have h2' : Real.log (121 / 120) ≤ (0.00829881 : ℝ) := h2.trans (by norm_num)
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  have h5 := log_five_mem
  have h6 := log_three_mem
  constructor <;> linarith [h5.1, h5.2, h6.1, h6.2]

theorem log_thirteen_mem : (2.5649492 : ℝ) < Real.log 13 ∧ Real.log 13 < 2.5649495 := by
  have h : Real.log (169 / 168) =
      2 * Real.log 13 - 3 * Real.log 2 - Real.log 3 - Real.log 7 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (169 : ℝ) = 13 ^ 2 by norm_num,
      show (168 : ℝ) = 2 ^ 3 * 3 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h1 := two_terms_le_log_div (y := 1 / 337) (by norm_num) (by norm_num)
  have h2 := RHTower.log_le_geometric_cubic (x := 169 / 168) (by norm_num)
  rw [show ((1 : ℝ) + 1 / 337) / (1 - 1 / 337) = 169 / 168 by norm_num] at h1
  have h1' : (0.00593473 : ℝ) ≤ Real.log (169 / 168) := le_trans (by norm_num) h1
  have h2' : Real.log (169 / 168) ≤ (0.00593474 : ℝ) := h2.trans (by norm_num)
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  have h5 := log_seven_mem
  have h6 := log_three_mem
  constructor <;> linarith [h5.1, h5.2, h6.1, h6.2]

theorem log_pi_lt : Real.log Real.pi < 1.1447302 := by
  have h1 : Real.log Real.pi < Real.log 3.141593 :=
    Real.log_lt_log Real.pi_pos Real.pi_lt_d6
  have h2 : Real.log (3.141593 : ℝ) = Real.log 3 + Real.log (3141593 / 3000000) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h3 := RHTower.log_le_geometric_cubic (x := 3141593 / 3000000) (by norm_num)
  have h3' : Real.log (3141593 / 3000000) ≤ (0.0461178 : ℝ) := h3.trans (by norm_num)
  linarith [log_three_mem.2]

theorem log_two_pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
  Real.log_mul two_ne_zero Real.pi_ne_zero

theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

theorem log_six : Real.log 6 = Real.log 2 + Real.log 3 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem log_eight : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  push_cast
  ring

theorem log_nine : Real.log 9 = 2 * Real.log 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

theorem log_ten : Real.log 10 = Real.log 2 + Real.log 5 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem log_twelve : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
  rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  push_cast
  ring

theorem log_fourteen : Real.log 14 = Real.log 2 + Real.log 7 := by
  rw [show (14 : ℝ) = 2 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem log_fifteen : Real.log 15 = Real.log 3 + Real.log 5 := by
  rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

theorem log_sixteen : Real.log 16 = 4 * Real.log 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  push_cast
  ring

/-! ### The contacts up to `4` and up to `7` -/

theorem vonMangoldt_two : (Λ 2 : ℝ) = Real.log 2 := by
  simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two

theorem vonMangoldt_three : (Λ 3 : ℝ) = Real.log 3 := by
  simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three

theorem vonMangoldt_four : (Λ 4 : ℝ) = Real.log 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    vonMangoldt_two]

theorem vonMangoldt_five : (Λ 5 : ℝ) = Real.log 5 := by
  simpa using ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)

theorem vonMangoldt_six : (Λ 6 : ℝ) = 0 := by
  refine ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr fun h => ?_
  obtain ⟨p, k, hp, _, he⟩ := (isPrimePow_nat_iff _).mp h
  have h2 : 2 ∣ p ^ k := he ▸ (by norm_num : 2 ∣ 6)
  have h3 : 3 ∣ p ^ k := he ▸ (by norm_num : 3 ∣ 6)
  have hp2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)
  have hp3 :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem vonMangoldt_seven : (Λ 7 : ℝ) = Real.log 7 := by
  simpa using ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 7)

/-- The contacts up to `4`: the floor maps of `2`, `3` and `4`. -/
theorem floorContact_four (a b : ℕ) :
    floorContact 4 a b = (if b / 2 = a then Real.log 2 / 2 else 0) +
      (if b / 3 = a then Real.log 3 / 3 else 0) + (if b / 4 = a then Real.log 2 / 4 else 0) := by
  rw [floorContact, show Icc 2 4 = {2, 3, 4} by rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    vonMangoldt_two, vonMangoldt_three, vonMangoldt_four]
  push_cast
  ring

/-- The contacts up to `7`: the floor maps of `2`, `3`, `4`, `5` and `7`. -/
theorem floorContact_seven (a b : ℕ) :
    floorContact 7 a b = (if b / 2 = a then Real.log 2 / 2 else 0) +
      (if b / 3 = a then Real.log 3 / 3 else 0) + (if b / 4 = a then Real.log 2 / 4 else 0) +
      (if b / 5 = a then Real.log 5 / 5 else 0) + (if b / 7 = a then Real.log 7 / 7 else 0) := by
  rw [floorContact, show Icc 2 7 = {2, 3, 4, 5, 6, 7} by rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    vonMangoldt_two, vonMangoldt_three, vonMangoldt_four, vonMangoldt_five, vonMangoldt_six,
    vonMangoldt_seven]
  simp only [zero_div, ite_self]
  push_cast
  ring

/-! ### Ratio four: three blocks -/

/-- The decimal table of the block matrix on the blocks `1, 2, 3`. -/
def table4 : ℕ → ℕ → ℝ
  | 0, 0 => 0.18755
  | 1, 1 => 0.20465
  | 2, 2 => 0.3379
  | 0, 1 => -0.06744
  | 1, 0 => -0.06744
  | 0, 2 => -0.09425
  | 2, 0 => -0.09425
  | 1, 2 => -0.08372
  | 2, 1 => -0.08372
  | _, _ => 0

theorem table4_symm (j l : ℕ) : table4 j l = table4 l j := by
  rcases j with _ | _ | _ | j <;> rcases l with _ | _ | _ | l <;> rfl

/-- Evaluates an entry of the block matrix into `γ`, `log π` and logarithms of primes, and
compares it with a decimal through the enclosures of the logarithms. -/
macro "block_entry" : tactic =>
  `(tactic|
    (simp only [blockDegree, blockDensity, blockJet, xLogXDiff, xLogX]
     norm_num [log_two_pi, log_four, log_six, log_eight, log_nine, log_ten, log_twelve,
       log_fourteen, log_fifteen, log_sixteen]
     linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_mem.1, log_three_mem.2,
       log_five_mem.1, log_five_mem.2, log_seven_mem.1, log_seven_mem.2, log_eleven_mem.1,
       log_eleven_mem.2, log_thirteen_mem.1, log_thirteen_mem.2, log_pi_lt,
       RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion]))

theorem table4_diag (j : ℕ) (hj : j < 3) : table4 j j ≤ blockMatrix 4 (1 + j) (1 + j) := by
  interval_cases j
  · show (0.18755 : ℝ) ≤ blockMatrix 4 1 1
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.20465 : ℝ) ≤ blockMatrix 4 2 2
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.3379 : ℝ) ≤ blockMatrix 4 3 3
    rw [blockMatrix_self (by norm_num)]
    block_entry

theorem table4_off (j l : ℕ) (hjl : j < l) (hl : l < 3) :
    |blockMatrix 4 (1 + j) (1 + l) - table4 j l| ≤ 1 / 10000 := by
  interval_cases l <;> interval_cases j
  · show |blockMatrix 4 1 2 - (-0.06744)| ≤ 1 / 10000
    rw [blockMatrix_of_lt (by norm_num), floorContact_four, abs_le]
    constructor <;> block_entry
  · show |blockMatrix 4 1 3 - (-0.09425)| ≤ 1 / 10000
    rw [blockMatrix_of_lt (by norm_num), floorContact_four, abs_le]
    constructor <;> block_entry
  · show |blockMatrix 4 2 3 - (-0.08372)| ≤ 1 / 10000
    rw [blockMatrix_of_lt (by norm_num), floorContact_four, abs_le]
    constructor <;> block_entry

/-- The table minus `503/10000` is a sum of three squares plus a diagonally dominant
remainder. -/
theorem table4_form_ge (σ : ℕ → ℝ) :
    503 / 10000 * ∑ j ∈ range 3, σ j ^ 2 ≤
      ∑ j ∈ range 3, ∑ l ∈ range 3, σ j * σ l * table4 j l := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, table4]
  have s3 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.277938)
    (sq_nonneg (σ 2 + -0.339105 * σ 0 + -0.30123 * σ 1))
  have s2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.1194823) (sq_nonneg (σ 1 + -0.802088 * σ 0))
  have s1 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.0187678) (sq_nonneg (σ 0))
  linarith [sq_nonneg (σ 0), sq_nonneg (σ 1), sq_nonneg (σ 2), sq_nonneg (σ 0 - σ 1),
    sq_nonneg (σ 0 + σ 1), sq_nonneg (σ 0 - σ 2), sq_nonneg (σ 0 + σ 2), sq_nonneg (σ 1 - σ 2),
    sq_nonneg (σ 1 + σ 2)]

/-- **Ratio four.** The block matrix on the blocks `1, 2, 3` with the contacts up to `4` is at
least `1/20`. -/
theorem sum_blockMatrix_four_ge (σ : ℕ → ℝ) :
    1 / 20 * ∑ j ∈ range 3, σ j ^ 2 ≤
      ∑ j ∈ range 3, ∑ l ∈ range 3, σ j * σ l * blockMatrix 4 (1 + j) (1 + l) := by
  refine le_trans ?_ (sum_sum_mul_ge_of_close σ (fun j l => blockMatrix 4 (1 + j) (1 + l)) table4
    (ε := 1 / 10000) (by norm_num) (fun j l => blockMatrix_comm 4 _ _) table4_symm table4_diag
    table4_off)
  have h := table4_form_ge σ
  have h0 : 0 ≤ ∑ j ∈ range 3, σ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  push_cast
  linarith

/-! ### Ratio seven: six blocks -/

/-- The decimal table of the block matrix on the blocks `1, …, 6`. -/
def table7 : ℕ → ℕ → ℝ
  | 0, 0 => 0.18755
  | 1, 1 => 0.20465
  | 2, 2 => 0.3379
  | 3, 3 => 0.4775
  | 4, 4 => 0.60735
  | 5, 5 => 0.72548
  | 0, 1 => -0.06744
  | 1, 0 => -0.06744
  | 0, 2 => -0.09425
  | 2, 0 => -0.09425
  | 0, 3 => 0.12318
  | 3, 0 => 0.12318
  | 0, 4 => -0.18392
  | 4, 0 => -0.18392
  | 0, 5 => 0.18878
  | 5, 0 => 0.18878
  | 1, 2 => -0.08372
  | 2, 1 => -0.08372
  | 1, 3 => -0.05126
  | 3, 1 => -0.05126
  | 1, 4 => 0.00865
  | 4, 1 => 0.00865
  | 1, 5 => 0.01141
  | 5, 1 => 0.01141
  | 2, 3 => -0.24499
  | 3, 2 => -0.24499
  | 2, 4 => 0.15271
  | 4, 2 => 0.15271
  | 2, 5 => -0.12472
  | 5, 2 => -0.12472
  | 3, 4 => -0.33777
  | 4, 3 => -0.33777
  | 3, 5 => 0.07015
  | 5, 3 => 0.07015
  | 4, 5 => -0.39839
  | 5, 4 => -0.39839
  | _, _ => 0

theorem table7_symm (j l : ℕ) : table7 j l = table7 l j := by
  rcases j with _ | _ | _ | _ | _ | _ | j <;> rcases l with _ | _ | _ | _ | _ | _ | l <;> rfl

theorem table7_diag (j : ℕ) (hj : j < 6) : table7 j j ≤ blockMatrix 7 (1 + j) (1 + j) := by
  interval_cases j
  · show (0.18755 : ℝ) ≤ blockMatrix 7 1 1
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.20465 : ℝ) ≤ blockMatrix 7 2 2
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.3379 : ℝ) ≤ blockMatrix 7 3 3
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.4775 : ℝ) ≤ blockMatrix 7 4 4
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.60735 : ℝ) ≤ blockMatrix 7 5 5
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.72548 : ℝ) ≤ blockMatrix 7 6 6
    rw [blockMatrix_self (by norm_num)]
    block_entry

/-- An entry off the diagonal of the block matrix with the contacts up to `7`, within `10⁻⁴` of
a decimal. -/
macro "block_off7" : tactic =>
  `(tactic|
    (rw [blockMatrix_of_lt (by norm_num), floorContact_seven, abs_le]
     constructor <;> block_entry))

theorem table7_off (j l : ℕ) (hjl : j < l) (hl : l < 6) :
    |blockMatrix 7 (1 + j) (1 + l) - table7 j l| ≤ 1 / 10000 := by
  interval_cases l <;> interval_cases j
  · show |blockMatrix 7 1 2 - (-0.06744)| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 1 3 - (-0.09425)| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 2 3 - (-0.08372)| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 1 4 - 0.12318| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 2 4 - (-0.05126)| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 3 4 - (-0.24499)| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 1 5 - (-0.18392)| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 2 5 - 0.00865| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 3 5 - 0.15271| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 4 5 - (-0.33777)| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 1 6 - 0.18878| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 2 6 - 0.01141| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 3 6 - (-0.12472)| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 4 6 - 0.07015| ≤ 1 / 10000
    block_off7
  · show |blockMatrix 7 5 6 - (-0.39839)| ≤ 1 / 10000
    block_off7

/-- The table minus `106/10000` is a sum of six squares plus a diagonally dominant remainder. The
squares are the Cholesky factors of the table minus `1/50`, eliminated from the last block. -/
theorem table7_form_ge (σ : ℕ → ℝ) :
    106 / 10000 * ∑ j ∈ range 6, σ j ^ 2 ≤
      ∑ j ∈ range 6, ∑ l ∈ range 6, σ j * σ l * table7 j l := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, table7]
  have s6 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.7055232)
    (sq_nonneg (σ 5 + 0.267577 * σ 0 + 0.016166 * σ 1 + -0.176782 * σ 2 + 0.099435 * σ 3 +
      -0.564674 * σ 4))
  have s5 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.3624395)
    (sq_nonneg (σ 4 + -0.21333 * σ 0 + 0.041636 * σ 1 + 0.22702 * σ 2 + -0.822625 * σ 3))
  have s4 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.205293)
    (sq_nonneg (σ 3 + 0.198748 * σ 0 + -0.194761 * σ 1 + -0.803229 * σ 2))
  have s3 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.1447595)
    (sq_nonneg (σ 2 + -0.072886 * σ 0 + -0.809952 * σ 1))
  have s2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.081137) (sq_nonneg (σ 1 + -0.836562 * σ 0))
  have s1 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.0349279) (sq_nonneg (σ 0))
  linarith [sq_nonneg (σ 0), sq_nonneg (σ 1), sq_nonneg (σ 2), sq_nonneg (σ 3), sq_nonneg (σ 4),
    sq_nonneg (σ 5), sq_nonneg (σ 0 - σ 1), sq_nonneg (σ 0 + σ 1), sq_nonneg (σ 0 - σ 2),
    sq_nonneg (σ 0 + σ 2), sq_nonneg (σ 0 - σ 3), sq_nonneg (σ 0 + σ 3), sq_nonneg (σ 0 - σ 4),
    sq_nonneg (σ 0 + σ 4), sq_nonneg (σ 0 - σ 5), sq_nonneg (σ 0 + σ 5), sq_nonneg (σ 1 - σ 2),
    sq_nonneg (σ 1 + σ 2), sq_nonneg (σ 1 - σ 3), sq_nonneg (σ 1 + σ 3), sq_nonneg (σ 1 - σ 4),
    sq_nonneg (σ 1 + σ 4), sq_nonneg (σ 1 - σ 5), sq_nonneg (σ 1 + σ 5), sq_nonneg (σ 2 - σ 3),
    sq_nonneg (σ 2 + σ 3), sq_nonneg (σ 2 - σ 4), sq_nonneg (σ 2 + σ 4), sq_nonneg (σ 2 - σ 5),
    sq_nonneg (σ 2 + σ 5), sq_nonneg (σ 3 - σ 4), sq_nonneg (σ 3 + σ 4), sq_nonneg (σ 3 - σ 5),
    sq_nonneg (σ 3 + σ 5), sq_nonneg (σ 4 - σ 5), sq_nonneg (σ 4 + σ 5)]

/-- **Ratio seven.** The block matrix on the blocks `1, …, 6` with the contacts up to `7` is at
least `1/100`. -/
theorem sum_blockMatrix_seven_ge (σ : ℕ → ℝ) :
    1 / 100 * ∑ j ∈ range 6, σ j ^ 2 ≤
      ∑ j ∈ range 6, ∑ l ∈ range 6, σ j * σ l * blockMatrix 7 (1 + j) (1 + l) := by
  refine le_trans ?_ (sum_sum_mul_ge_of_close σ (fun j l => blockMatrix 7 (1 + j) (1 + l)) table7
    (ε := 1 / 10000) (by norm_num) (fun j l => blockMatrix_comm 7 _ _) table7_symm table7_diag
    table7_off)
  have h := table7_form_ge σ
  have h0 : 0 ≤ ∑ j ∈ range 6, σ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  push_cast
  linarith

/-! ### Ratio four on finer blocks: the six blocks above two -/

/-- The decimal table of the block matrix with the contacts up to `4` on the blocks
`2, …, 7`. -/
def table4fine : ℕ → ℕ → ℝ
  | 0, 0 => 0.20465
  | 1, 1 => 0.3379
  | 2, 2 => 0.4775
  | 3, 3 => 0.60735
  | 4, 4 => 0.72548
  | 5, 5 => 0.83273
  | 0, 1 => -0.08372
  | 1, 0 => -0.08372
  | 0, 2 => -0.05126
  | 2, 0 => -0.05126
  | 0, 3 => 0.00865
  | 3, 0 => 0.00865
  | 0, 4 => 0.01141
  | 4, 0 => 0.01141
  | 0, 5 => 0.02203
  | 5, 0 => 0.02203
  | 1, 2 => -0.24499
  | 2, 1 => -0.24499
  | 1, 3 => 0.15271
  | 3, 1 => 0.15271
  | 1, 4 => -0.12472
  | 4, 1 => -0.12472
  | 1, 5 => -0.09721
  | 5, 1 => -0.09721
  | 2, 3 => -0.33777
  | 3, 2 => -0.33777
  | 2, 4 => 0.07015
  | 4, 2 => 0.07015
  | 2, 5 => 0.14506
  | 5, 2 => 0.14506
  | 3, 4 => -0.39839
  | 4, 3 => -0.39839
  | 3, 5 => 0.01573
  | 5, 3 => 0.01573
  | 4, 5 => -0.44121
  | 5, 4 => -0.44121
  | _, _ => 0

theorem table4fine_symm (j l : ℕ) : table4fine j l = table4fine l j := by
  rcases j with _ | _ | _ | _ | _ | _ | j <;> rcases l with _ | _ | _ | _ | _ | _ | l <;> rfl

theorem table4fine_diag (j : ℕ) (hj : j < 6) :
    table4fine j j ≤ blockMatrix 4 (2 + j) (2 + j) := by
  interval_cases j
  · show (0.20465 : ℝ) ≤ blockMatrix 4 2 2
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.3379 : ℝ) ≤ blockMatrix 4 3 3
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.4775 : ℝ) ≤ blockMatrix 4 4 4
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.60735 : ℝ) ≤ blockMatrix 4 5 5
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.72548 : ℝ) ≤ blockMatrix 4 6 6
    rw [blockMatrix_self (by norm_num)]
    block_entry
  · show (0.83273 : ℝ) ≤ blockMatrix 4 7 7
    rw [blockMatrix_self (by norm_num)]
    block_entry

/-- An entry off the diagonal of the block matrix with the contacts up to `4`, within `10⁻⁴` of
a decimal. -/
macro "block_off4" : tactic =>
  `(tactic|
    (rw [blockMatrix_of_lt (by norm_num), floorContact_four, abs_le]
     constructor <;> block_entry))

theorem table4fine_off (j l : ℕ) (hjl : j < l) (hl : l < 6) :
    |blockMatrix 4 (2 + j) (2 + l) - table4fine j l| ≤ 1 / 10000 := by
  interval_cases l <;> interval_cases j
  · show |blockMatrix 4 2 3 - (-0.08372)| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 2 4 - (-0.05126)| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 3 4 - (-0.24499)| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 2 5 - 0.00865| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 3 5 - 0.15271| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 4 5 - (-0.33777)| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 2 6 - 0.01141| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 3 6 - (-0.12472)| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 4 6 - 0.07015| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 5 6 - (-0.39839)| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 2 7 - 0.02203| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 3 7 - (-0.09721)| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 4 7 - 0.14506| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 5 7 - 0.01573| ≤ 1 / 10000
    block_off4
  · show |blockMatrix 4 6 7 - (-0.44121)| ≤ 1 / 10000
    block_off4

/-- The table minus `106/10000` is a sum of six squares plus a diagonally dominant remainder:
the Cholesky factors of the table minus `1/50`, eliminated from the last block. -/
theorem table4fine_form_ge (σ : ℕ → ℝ) :
    106 / 10000 * ∑ j ∈ range 6, σ j ^ 2 ≤
      ∑ j ∈ range 6, ∑ l ∈ range 6, σ j * σ l * table4fine j l := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, table4fine]
  have s6 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.8127736)
    (sq_nonneg (σ 5 + 0.0271059 * σ 0 + -0.119607 * σ 1 + 0.1784765 * σ 2 + 0.0193533 * σ 3 +
      -0.5428455 * σ 4))
  have s5 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.4660141)
    (sq_nonneg (σ 4 + 0.0501378 * σ 0 + -0.38088 * σ 1 + 0.3195163 * σ 2 + -0.8365672 * σ 3))
  have s4 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.2609586)
    (sq_nonneg (σ 3 + 0.1064153 * σ 0 + 0.02339 * σ 1 + -0.8277525 * σ 2))
  have s3 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.205268)
    (sq_nonneg (σ 2 + -0.1932771 * σ 0 + -0.8080658 * σ 1))
  have s2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.1045294) (sq_nonneg (σ 1 + -1.0035191 * σ 0))
  have s1 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.0670439) (sq_nonneg (σ 0))
  linarith [sq_nonneg (σ 0), sq_nonneg (σ 1), sq_nonneg (σ 2), sq_nonneg (σ 3), sq_nonneg (σ 4),
    sq_nonneg (σ 5), sq_nonneg (σ 0 - σ 1), sq_nonneg (σ 0 + σ 1), sq_nonneg (σ 0 - σ 2),
    sq_nonneg (σ 0 + σ 2), sq_nonneg (σ 0 - σ 3), sq_nonneg (σ 0 + σ 3), sq_nonneg (σ 0 - σ 4),
    sq_nonneg (σ 0 + σ 4), sq_nonneg (σ 0 - σ 5), sq_nonneg (σ 0 + σ 5), sq_nonneg (σ 1 - σ 2),
    sq_nonneg (σ 1 + σ 2), sq_nonneg (σ 1 - σ 3), sq_nonneg (σ 1 + σ 3), sq_nonneg (σ 1 - σ 4),
    sq_nonneg (σ 1 + σ 4), sq_nonneg (σ 1 - σ 5), sq_nonneg (σ 1 + σ 5), sq_nonneg (σ 2 - σ 3),
    sq_nonneg (σ 2 + σ 3), sq_nonneg (σ 2 - σ 4), sq_nonneg (σ 2 + σ 4), sq_nonneg (σ 2 - σ 5),
    sq_nonneg (σ 2 + σ 5), sq_nonneg (σ 3 - σ 4), sq_nonneg (σ 3 + σ 4), sq_nonneg (σ 3 - σ 5),
    sq_nonneg (σ 3 + σ 5), sq_nonneg (σ 4 - σ 5), sq_nonneg (σ 4 + σ 5)]

/-- **Ratio four on finer blocks.** The block matrix on the blocks `2, …, 7` with the contacts
up to `4` is at least `1/100`. -/
theorem sum_blockMatrix_four_fine_ge (σ : ℕ → ℝ) :
    1 / 100 * ∑ j ∈ range 6, σ j ^ 2 ≤
      ∑ j ∈ range 6, ∑ l ∈ range 6, σ j * σ l * blockMatrix 4 (2 + j) (2 + l) := by
  refine le_trans ?_ (sum_sum_mul_ge_of_close σ (fun j l => blockMatrix 4 (2 + j) (2 + l))
    table4fine (ε := 1 / 10000) (by norm_num) (fun j l => blockMatrix_comm 4 _ _)
    table4fine_symm table4fine_diag table4fine_off)
  have h := table4fine_form_ge σ
  have h0 : 0 ≤ ∑ j ∈ range 6, σ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  push_cast
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
