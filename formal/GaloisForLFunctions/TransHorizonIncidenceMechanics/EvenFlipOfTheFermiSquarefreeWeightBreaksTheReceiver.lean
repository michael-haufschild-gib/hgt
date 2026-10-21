import GaloisForLFunctions.TransHorizonIncidenceMechanics.FiniteKernelsRepairAPositiveDriftOnlyAtItsPole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.EvenFlipIsTheFermiTransformOfTheEvenPart
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusGradientCoercivityAndRenormalizedDefect

/-!
# The even flip breaks the receiver of the Fermi squarefree weight

Let `o(d) = 1_{d odd squarefree} d^{-ε}`; its Dirichlet series has its pole at `s = 1 − ε`.
The **Fermi weight** `F = (δ₁ − 2^{1−ε}δ₂) ⋆ o` carries the Fermi factor `1 − 2^{1−ε−s}` at the
prime `2`, which vanishes exactly at the pole. Indeed `F(d)d^{ε} = (g ⋆ s₀)(d)` with
`g(j²) = μ(j)1_{j odd}` (from `1_{odd sqf} = g ⋆ 1_{odd}`, the square-root Möbius normalization)
and `s₀ = 1_{odd} ⋆ (δ₁ − 2δ₂)`, the period-four pattern `(1, −2, 1, 0)` of mean zero. The kernel
`g` is critical Wiener and `s₀` has partial sums in `{−1, 0, 1}`, so **the receiver of `F` is bounded
at every `ε > 0`**.

Its **even flip** — the twist by `−1` of every Ramanujan coefficient at an even modulus —
is `F^♭(d) = F(d) + F(2d)` (`d` odd), `F^♭(d) = −F(d)` (`d` even), that is
`F^♭ = ((1 − 2^{1−ε})δ₁ + 2^{1−ε}δ₂) ⋆ o`. Its local factor at the pole is `2 − 2^{1−ε} ≠ 0`, and the
odd squarefree numbers fill a positive proportion `4/π²` of every late dyadic window, so by the pole
law of finite kernels **the receiver of `F^♭` is unbounded at every `ε ≤ 1/2`**.

The two weights have the same Ramanujan amplitudes, `W_{F^♭}(e) = ±W_F(e)` with the sign `−` exactly
on even `e`, the same mean, and opposite receivers. The arithmetic enters at the dilation `k ↦ 2k`:
the even flip is the sign twist invisible to every translated moment of a squarefree row, and the
Fermi factor at `2` is the only local factor whose zero sits on the pole.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Convolution tools -/

/-- Convolution with a kernel supported on `{1, 2}`. -/
theorem dirichletConv_twoPoint {k : ℕ → ℝ} (hk : ∀ j, j ≠ 1 → j ≠ 2 → k j = 0) (c : ℕ → ℝ)
    {n : ℕ} (hn : n ≠ 0) :
    RHTower.dirichletConv k c n = k 1 * c n + if 2 ∣ n then k 2 * c (n / 2) else 0 := by
  unfold RHTower.dirichletConv
  split_ifs with h2
  · have hsub : ({1, 2} : Finset ℕ) ⊆ n.divisors := by
      intro j hj
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact Nat.one_mem_divisors.mpr hn
      · exact Nat.mem_divisors.mpr ⟨h2, hn⟩
    rw [← sum_subset hsub fun j _ hj => ?_, sum_pair (by norm_num), Nat.div_one]
    simp only [mem_insert, mem_singleton, not_or] at hj
    rw [hk j hj.1 hj.2, zero_mul]
  · have hsub : ({1} : Finset ℕ) ⊆ n.divisors := by
      intro j hj
      rw [mem_singleton] at hj
      rw [hj]; exact Nat.one_mem_divisors.mpr hn
    rw [← sum_subset hsub fun j hj hj1 => ?_, sum_singleton, Nat.div_one, add_zero]
    rw [mem_singleton] at hj1
    have hj2 : j ≠ 2 := by
      rintro rfl; exact h2 (Nat.dvd_of_mem_divisors hj)
    rw [hk j hj1 hj2, zero_mul]

theorem mul_apply_eq_dirichletConv (f g : ArithmeticFunction ℝ) (n : ℕ) :
    (f * g) n = RHTower.dirichletConv ⇑f ⇑g n := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]; rfl

/-- Damping commutes with Dirichlet convolution. -/
theorem dampedSignWeight_dirichletConv (f g : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    dampedSignWeight (RHTower.dirichletConv f g) ε n =
      RHTower.dirichletConv (dampedSignWeight f ε) (dampedSignWeight g ε) n := by
  unfold dampedSignWeight RHTower.dirichletConv
  rw [sum_mul]
  refine sum_congr rfl fun d hd => ?_
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [Nat.mul_div_cancel_left k hd0, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-! ### The arithmetic functions -/

/-- The indicator of the odd integers, completely multiplicative. -/
def oddAF : ArithmeticFunction ℝ := ⟨fun n => if ¬ 2 ∣ n then 1 else 0, by simp⟩

theorem oddAF_apply (n : ℕ) : oddAF n = if ¬ 2 ∣ n then 1 else 0 := rfl

theorem oddAF_mul (a b : ℕ) : oddAF (a * b) = oddAF a * oddAF b := by
  simp only [oddAF_apply, Nat.prime_two.dvd_mul]
  by_cases ha : 2 ∣ a <;> by_cases hb : 2 ∣ b <;> simp [ha, hb]

theorem pmul_oddAF_mul (f g : ArithmeticFunction ℝ) :
    oddAF.pmul (f * g) = oddAF.pmul f * oddAF.pmul g := by
  ext n
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.mul_apply, mul_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, oddAF_mul]; ring

/-- `g(j²) = μ(j) 1_{j odd}`, zero off the squares. -/
def oddSqrtMoebius : ArithmeticFunction ℝ :=
  oddAF.pmul ((RHTower.sqrtPart (ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
    ArithmeticFunction ℤ) : ArithmeticFunction ℝ)

/-- The indicator of the odd squarefree integers. -/
def oddSqfAF : ArithmeticFunction ℝ :=
  oddAF.pmul (((ArithmeticFunction.moebius : ArithmeticFunction ℤ).pmul
    ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)

theorem oddSqfAF_apply (n : ℕ) : oddSqfAF n = if ¬ 2 ∣ n ∧ Squarefree n then 1 else 0 := by
  simp only [oddSqfAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply, oddAF_apply]
  by_cases hsq : Squarefree n
  · have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [sq] at h
    rw [h, Int.cast_one, mul_one]
    by_cases h2 : 2 ∣ n <;> simp [h2, hsq]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, zero_mul, Int.cast_zero, mul_zero]
    simp [hsq]

/-- **Odd square-root Möbius normalization**: `1_{odd sqf} = g ⋆ 1_{odd}`. -/
theorem oddSqfAF_eq : oddSqfAF = oddSqrtMoebius * oddAF := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => (F : ArithmeticFunction ℝ))
    RHTower.sqrtPart_moebius_mul_zeta
  simp only [ArithmeticFunction.intCoe_mul] at h
  have hz : oddAF.pmul (((ArithmeticFunction.zeta : ArithmeticFunction ℤ) : ArithmeticFunction ℤ) :
      ArithmeticFunction ℝ) = oddAF := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp
  rw [oddSqfAF, ← h, pmul_oddAF_mul, hz, oddSqrtMoebius]

theorem abs_oddSqrtMoebius_le (n : ℕ) : |oddSqrtMoebius n| ≤ |RHTower.squareIndicatorR n| := by
  simp only [oddSqrtMoebius, ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply]
  by_cases hsq : IsSquare n
  · obtain ⟨r, rfl⟩ := hsq
    rw [RHTower.squareIndicatorR, if_pos (IsSquare.mul_self r), abs_one,
      show r * r = r ^ 2 by ring, RHTower.sqrtPart_apply_sq, abs_mul]
    have hμ : |((ArithmeticFunction.moebius r : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hodd : |oddAF (r ^ 2)| ≤ 1 := by rw [oddAF_apply]; split_ifs <;> norm_num
    exact mul_le_one₀ hodd (abs_nonneg _) hμ
  · rw [RHTower.sqrtPart_apply_of_not_isSquare _ hsq]
    simp

/-- The Fermi factor at `2`: `δ₁ − 2δ₂`. -/
def fermiAF : ArithmeticFunction ℝ := ⟨fun n => if n = 1 then 1 else if n = 2 then -2 else 0, by simp⟩

theorem fermiAF_support (j : ℕ) (h1 : j ≠ 1) (h2 : j ≠ 2) : fermiAF j = 0 := by
  simp [fermiAF, h1, h2]

/-- The period-four pattern `(0, 1, −2, 1)` of `n mod 4`. -/
def fermiPattern (n : ℕ) : ℝ := if n % 4 = 1 ∨ n % 4 = 3 then 1 else if n % 4 = 2 then -2 else 0

/-- `s₀ = 1_{odd} ⋆ (δ₁ − 2δ₂)` is the period-four pattern. -/
theorem oddAF_mul_fermiAF_apply (n : ℕ) : (oddAF * fermiAF) n = fermiPattern n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fermiPattern]
  rw [mul_comm, mul_apply_eq_dirichletConv, dirichletConv_twoPoint fermiAF_support _ hn]
  simp only [fermiAF, ArithmeticFunction.coe_mk, oddAF_apply, fermiPattern]
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · have h2 : 2 ∣ n := by omega
    have h2' : 2 ∣ n / 2 := by omega
    simp [h, h2, h2']
  · have h2 : ¬ 2 ∣ n := by omega
    simp [h, h2]
  · have h2 : 2 ∣ n := by omega
    have h2' : ¬ 2 ∣ n / 2 := by omega
    simp [h, h2, h2']
  · have h2 : ¬ 2 ∣ n := by omega
    simp [h, h2]

theorem sum_range_fermiPattern (x : ℕ) :
    ∑ d ∈ range x, fermiPattern d = if x % 4 = 2 then 1 else if x % 4 = 3 then -1 else 0 := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.sum_range_succ, ih]
    have h4 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · simp [fermiPattern, h, show (x + 1) % 4 = 1 by omega]
    · simp [fermiPattern, h, show (x + 1) % 4 = 2 by omega]
    · simp [fermiPattern, h, show (x + 1) % 4 = 3 by omega]; norm_num
    · simp [fermiPattern, h, show (x + 1) % 4 = 0 by omega]

theorem abs_sum_range_fermiPattern_le (x : ℕ) : |∑ d ∈ range x, fermiPattern d| ≤ 1 := by
  rw [sum_range_fermiPattern]
  split_ifs <;> norm_num

theorem abs_fermiPattern_le (n : ℕ) : |fermiPattern n| ≤ 2 := by
  unfold fermiPattern; split_ifs <;> norm_num

/-! ### The weights -/

/-- The odd squarefree weight `o(d) = 1_{d odd sqf} d^{-ε}`. -/
def oddSqfWeight (ε : ℝ) : ℕ → ℝ := dampedSignWeight ⇑oddSqfAF ε

/-- The damped Fermi kernel `δ₁ − 2^{1−ε}δ₂`. -/
def fermiKernel (ε : ℝ) (j : ℕ) : ℝ := if j = 1 then 1 else if j = 2 then -(2 : ℝ) ^ (1 - ε) else 0

/-- The flipped kernel `(1 − 2^{1−ε})δ₁ + 2^{1−ε}δ₂`. -/
def flipKernel (ε : ℝ) (j : ℕ) : ℝ :=
  if j = 1 then 1 - (2 : ℝ) ^ (1 - ε) else if j = 2 then (2 : ℝ) ^ (1 - ε) else 0

/-- **The Fermi weight** `F = (δ₁ − 2^{1−ε}δ₂) ⋆ o`. -/
def fermiWeight (ε : ℝ) : ℕ → ℝ := RHTower.dirichletConv (fermiKernel ε) (oddSqfWeight ε)

/-- **Its even flip** `F^♭ = ((1 − 2^{1−ε})δ₁ + 2^{1−ε}δ₂) ⋆ o`. -/
def fermiFlipWeight (ε : ℝ) : ℕ → ℝ := RHTower.dirichletConv (flipKernel ε) (oddSqfWeight ε)

theorem two_mul_rpow_neg (ε : ℝ) : 2 * (2 : ℝ) ^ (-ε) = (2 : ℝ) ^ (1 - ε) := by
  rw [show 1 - ε = 1 + -ε by ring, Real.rpow_add two_pos, Real.rpow_one]

theorem fermiKernel_eq (ε : ℝ) : fermiKernel ε = dampedSignWeight ⇑fermiAF ε := by
  funext j
  by_cases h1 : j = 1
  · subst h1; simp [fermiKernel, dampedSignWeight, fermiAF]
  by_cases h2 : j = 2
  · subst h2
    simp only [fermiKernel, dampedSignWeight, fermiAF, ArithmeticFunction.coe_mk]
    norm_num
    rw [← two_mul_rpow_neg]
  · simp [fermiKernel, dampedSignWeight, fermiAF, h1, h2]

theorem oddSqfWeight_of_even {ε : ℝ} {n : ℕ} (hn : 2 ∣ n) : oddSqfWeight ε n = 0 := by
  simp [oddSqfWeight, dampedSignWeight, oddSqfAF_apply, hn]

theorem oddSqfWeight_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ oddSqfWeight ε n := by
  unfold oddSqfWeight dampedSignWeight
  rw [oddSqfAF_apply]
  split_ifs <;> simp [Real.rpow_nonneg]

theorem oddSqfWeight_le (ε : ℝ) (n : ℕ) : oddSqfWeight ε n ≤ (n : ℝ) ^ (-ε) := by
  unfold oddSqfWeight dampedSignWeight
  rw [oddSqfAF_apply]
  split_ifs <;> simp [Real.rpow_nonneg]

theorem oddSqfWeight_mem_dampedClass (ε : ℝ) : DampedClass 1 ε (oddSqfWeight ε) := fun d => by
  rw [one_mul, abs_of_nonneg (oddSqfWeight_nonneg ε d)]; exact oddSqfWeight_le ε d

theorem fermiWeight_apply (ε : ℝ) {n : ℕ} (hn : n ≠ 0) :
    fermiWeight ε n = oddSqfWeight ε n -
      if 2 ∣ n then (2 : ℝ) ^ (1 - ε) * oddSqfWeight ε (n / 2) else 0 := by
  rw [fermiWeight, dirichletConv_twoPoint (fun j h1 h2 => by simp [fermiKernel, h1, h2]) _ hn]
  have hk1 : fermiKernel ε 1 = 1 := by simp [fermiKernel]
  have hk2 : fermiKernel ε 2 = -(2 : ℝ) ^ (1 - ε) := by simp [fermiKernel]
  rw [hk1, hk2]
  split_ifs <;> ring

theorem fermiFlipWeight_apply (ε : ℝ) {n : ℕ} (hn : n ≠ 0) :
    fermiFlipWeight ε n = (1 - (2 : ℝ) ^ (1 - ε)) * oddSqfWeight ε n +
      if 2 ∣ n then (2 : ℝ) ^ (1 - ε) * oddSqfWeight ε (n / 2) else 0 := by
  rw [fermiFlipWeight, dirichletConv_twoPoint (fun j h1 h2 => by simp [flipKernel, h1, h2]) _ hn]
  have hk1 : flipKernel ε 1 = 1 - (2 : ℝ) ^ (1 - ε) := by simp [flipKernel]
  have hk2 : flipKernel ε 2 = (2 : ℝ) ^ (1 - ε) := by simp [flipKernel]
  rw [hk1, hk2]

/-- `2^{1−ε} (d/2)^{-ε} = 2 d^{-ε}` on even `d`. -/
private theorem rpow_mul_half_rpow {ε : ℝ} {n : ℕ} (hn : 2 ∣ n) :
    (2 : ℝ) ^ (1 - ε) * ((n / 2 : ℕ) : ℝ) ^ (-ε) = 2 * (n : ℝ) ^ (-ε) := by
  rw [Nat.cast_div hn (by norm_num), Nat.cast_ofNat,
    Real.div_rpow (Nat.cast_nonneg n) (by norm_num), ← two_mul_rpow_neg]
  have : (2 : ℝ) ^ (-ε) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
  field_simp

theorem fermiWeight_mem_dampedClass (ε : ℝ) : DampedClass 3 ε (fermiWeight ε) := fun n => by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fermiWeight, RHTower.dirichletConv]; positivity
  rw [fermiWeight_apply ε hn]
  have h0 := oddSqfWeight_nonneg ε n
  have h1 := oddSqfWeight_le ε n
  have hP : 0 ≤ (n : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  split_ifs with h2
  · rw [oddSqfWeight_of_even h2, zero_sub, abs_neg, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg two_pos.le _), abs_of_nonneg (oddSqfWeight_nonneg ε _)]
    have := mul_le_mul_of_nonneg_left (oddSqfWeight_le ε (n / 2))
      (Real.rpow_nonneg (zero_le_two (α := ℝ)) (1 - ε))
    rw [rpow_mul_half_rpow h2] at this
    linarith
  · rw [sub_zero, abs_of_nonneg h0]; linarith

theorem fermiFlipWeight_mem_dampedClass {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    DampedClass 3 ε (fermiFlipWeight ε) := fun n => by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fermiFlipWeight, RHTower.dirichletConv]; positivity
  rw [fermiFlipWeight_apply ε hn]
  have hP : 0 ≤ (n : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have ht1 : 1 ≤ (2 : ℝ) ^ (1 - ε) := Real.one_le_rpow (by norm_num) (by linarith)
  have ht2 : (2 : ℝ) ^ (1 - ε) ≤ 2 := by
    calc (2 : ℝ) ^ (1 - ε) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  split_ifs with h2
  · rw [oddSqfWeight_of_even h2, mul_zero, zero_add, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg two_pos.le _), abs_of_nonneg (oddSqfWeight_nonneg ε _)]
    have := mul_le_mul_of_nonneg_left (oddSqfWeight_le ε (n / 2))
      (Real.rpow_nonneg (zero_le_two (α := ℝ)) (1 - ε))
    rw [rpow_mul_half_rpow h2] at this
    linarith
  · rw [add_zero, abs_mul, abs_of_nonneg (oddSqfWeight_nonneg ε n)]
    have habs : |1 - (2 : ℝ) ^ (1 - ε)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc |1 - (2 : ℝ) ^ (1 - ε)| * oddSqfWeight ε n ≤ 1 * (n : ℝ) ^ (-ε) :=
          mul_le_mul habs (oddSqfWeight_le ε n) (oddSqfWeight_nonneg ε n) zero_le_one
      _ ≤ 3 * (n : ℝ) ^ (-ε) := by linarith

/-! ### The even flip -/

theorem fermiWeight_zero (ε : ℝ) : fermiWeight ε 0 = 0 := by
  simp [fermiWeight, RHTower.dirichletConv]

theorem fermiWeight_of_four_dvd (ε : ℝ) {n : ℕ} (h4 : 4 ∣ n) : fermiWeight ε n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact fermiWeight_zero ε
  have h2 : 2 ∣ n := (Nat.dvd_trans (by norm_num) h4)
  have h2' : 2 ∣ n / 2 := by omega
  rw [fermiWeight_apply ε hn, if_pos h2, oddSqfWeight_of_even h2, oddSqfWeight_of_even h2']
  ring

/-- **`F^♭` is the even flip of `F`**: `F^♭ = F + (c_e ⋆ (δ₁ − 2δ₂))` with `c_e(d) = 1_{odd}(d) F(2d)`,
i.e. `F^♭(d) = F(d) + F(2d)` for odd `d` and `F^♭(d) = −F(d)` for even `d`. -/
theorem fermiFlipWeight_eq (ε : ℝ) :
    fermiFlipWeight ε = fun d =>
      fermiWeight ε d + localFactorWeight (evenPartWeight (fermiWeight ε)) 2 2 d := by
  funext d
  rcases eq_or_ne d 0 with rfl | hd
  · simp [fermiFlipWeight, fermiWeight_zero, RHTower.dirichletConv, localFactorWeight,
      evenPartWeight]
  rw [fermiFlipWeight_apply ε hd, fermiWeight_apply ε hd]
  simp only [localFactorWeight, evenPartWeight]
  by_cases h2 : 2 ∣ d
  · have hodd : ¬ d % 2 = 1 := by omega
    simp only [h2, hodd, ↓reduceIte, oddSqfWeight_of_even h2]
    by_cases he : (d / 2) % 2 = 1
    · rw [if_pos he, Nat.mul_div_cancel' h2, fermiWeight_apply ε hd, if_pos h2,
        oddSqfWeight_of_even h2]
      ring
    · have h2' : 2 ∣ d / 2 := by omega
      rw [if_neg he, oddSqfWeight_of_even h2']
      ring
  · have hodd : d % 2 = 1 := by omega
    have h2d : 2 ∣ 2 * d := dvd_mul_right 2 d
    simp only [h2, hodd, ↓reduceIte]
    rw [fermiWeight_apply ε (by omega : 2 * d ≠ 0), if_pos h2d, oddSqfWeight_of_even h2d,
      Nat.mul_div_cancel_left d two_pos]
    ring

/-- **The even flip twists the Ramanujan coefficients by `σ₂`.** For a weight of the damped class
vanishing on multiples of four, `c^♭ = c + c_e ⋆ (δ₁ − 2δ₂)` has `W_{c^♭}(e) = σ₂(e) W_c(e)`,
`σ₂(e) = −1` exactly on even `e`: on even moduli `c^♭ = −c`; on odd moduli the multiples split by
parity and the dilation `k ↦ 2k` moves the odd-indexed part `2c(2ek)` onto the even multiples. -/
theorem weightRamanujanCoeff_evenFlip {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c)
    (h4 : ∀ m, 4 ∣ m → c m = 0) (e : ℕ) :
    weightRamanujanCoeff (fun d => c d + localFactorWeight (evenPartWeight c) 2 2 d) e =
      evenSign e * weightRamanujanCoeff c e := by
  set a : ℕ → ℝ := fun k => c (e * k) / ((e * k : ℕ) : ℝ)
  have hsum : Summable a := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp only [a, zero_mul, h4 0 (dvd_zero 4), zero_div]; exact summable_zero
    · exact (summable_div_of_dampedClass hε hc).comp_injective
        (fun x y h => Nat.eq_of_mul_eq_mul_left he h)
  have hsub : ∀ f : ℕ → ℕ, Function.Injective f → Summable (fun k => a (f k)) := fun f hf =>
    hsum.comp_injective hf
  have h2inj : Function.Injective (fun k : ℕ => 2 * k) := fun x y h => by simpa using h
  have h2inj' : Function.Injective (fun k : ℕ => 2 * k + 1) := fun x y h => by simpa using h
  unfold weightRamanujanCoeff evenSign
  split_ifs with he2
  · -- even moduli: every multiple is even and `c^♭ = −c` there
    rw [neg_one_mul, ← tsum_neg]
    refine tsum_congr fun k => ?_
    have hek : 2 ∣ e * k := Dvd.dvd.mul_right he2 k
    simp only [localFactorWeight, evenPartWeight, if_pos hek,
      show ¬ (e * k) % 2 = 1 by omega, ↓reduceIte]
    by_cases hk : (e * k / 2) % 2 = 1
    · rw [if_pos hk, Nat.mul_div_cancel' hek]; ring
    · have h4' : 4 ∣ e * k := by omega
      rw [if_neg hk, h4 _ h4']; ring
  · -- odd moduli: split the multiples by parity
    rw [one_mul]
    set b : ℕ → ℝ := fun k =>
      (c (e * k) + localFactorWeight (evenPartWeight c) 2 2 (e * k)) / ((e * k : ℕ) : ℝ)
    have hodd_e : e % 2 = 1 := by omega
    have hb_odd : ∀ k, b (2 * k + 1) = a (2 * k + 1) + 2 * a (2 * (2 * k + 1)) := fun k => by
      have hodd : (e * (2 * k + 1)) % 2 = 1 := by
        rw [Nat.mul_mod, hodd_e]; omega
      simp only [b, a, localFactorWeight, evenPartWeight, if_pos hodd,
        if_neg (show ¬ 2 ∣ e * (2 * k + 1) by omega), mul_zero, sub_zero]
      rw [show e * (2 * (2 * k + 1)) = 2 * (e * (2 * k + 1)) by ring]
      push_cast
      have he0 : (e : ℝ) * (2 * k + 1) ≠ 0 := by
        have : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
        positivity
      field_simp
    have hb_even : ∀ k, b (2 * k) = -a (2 * k) := fun k => by
      have hek : 2 ∣ e * (2 * k) := ⟨e * k, by ring⟩
      simp only [b, a, localFactorWeight, evenPartWeight, if_pos hek,
        show ¬ (e * (2 * k)) % 2 = 1 by omega, ↓reduceIte]
      by_cases hk : (e * (2 * k) / 2) % 2 = 1
      · rw [if_pos hk, Nat.mul_div_cancel' hek]; ring
      · have h4' : 4 ∣ e * (2 * k) := by omega
        rw [if_neg hk, h4 _ h4']; ring
    have ha4 : ∀ k, a (2 * (2 * k)) = 0 := fun k => by
      simp only [a]
      rw [h4 _ (Dvd.intro (e * k) (by ring)), zero_div]
    show ∑' k, b k = ∑' k, a k
    clear_value a b
    have hsA : Summable (fun k => a (2 * k)) := hsub (fun k => 2 * k) h2inj
    have hsA' : Summable (fun k => a (2 * k + 1)) := hsub (fun k => 2 * k + 1) h2inj'
    have hsA2 : Summable (fun k => a (2 * (2 * k + 1))) :=
      hsub (fun k => 2 * (2 * k + 1)) fun x y h => by simp only at h; omega
    have hsA4 : Summable (fun k => a (2 * (2 * k))) :=
      hsub (fun k => 2 * (2 * k)) fun x y h => by simp only at h; omega
    have hevenA : ∑' k, a (2 * k) = ∑' k, a (2 * (2 * k + 1)) := by
      have := tsum_even_add_odd (f := fun m => a (2 * m)) hsA4 hsA2
      rw [tsum_congr ha4, tsum_zero, zero_add] at this
      exact this.symm
    have hsB : Summable (fun k => b (2 * k)) := hsA.neg.congr fun k => (hb_even k).symm
    have hsB' : Summable (fun k => b (2 * k + 1)) :=
      (hsA'.add (hsA2.mul_left 2)).congr fun k => (hb_odd k).symm
    rw [← tsum_even_add_odd (f := b) hsB hsB', ← tsum_even_add_odd (f := a) hsA hsA',
      tsum_congr hb_even, tsum_congr hb_odd, tsum_neg, hsA'.tsum_add (hsA2.mul_left 2),
      tsum_mul_left, hevenA]
    ring

/-- **The Ramanujan amplitudes of the Fermi pair agree**: `W_{F^♭}(e) = σ₂(e) W_F(e)`. -/
theorem weightRamanujanCoeff_fermiFlipWeight {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    weightRamanujanCoeff (fermiFlipWeight ε) e = evenSign e * weightRamanujanCoeff (fermiWeight ε) e := by
  rw [fermiFlipWeight_eq]
  exact weightRamanujanCoeff_evenFlip hε (fermiWeight_mem_dampedClass ε)
    (fun m h => fermiWeight_of_four_dvd ε h) e

/-! ### The receivers -/

/-- The damped odd square-root Möbius kernel lies in the critical Wiener algebra. -/
theorem criticalWiener_dampedOddSqrtMoebius {ε : ℝ} (hε : 0 < ε) :
    CriticalWiener (dampedSignWeight ⇑oddSqrtMoebius ε) :=
  (criticalWiener_dampedSquare hε).of_nonneg_of_le
    (fun q => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _))
    fun q => mul_le_mul_of_nonneg_right (by
      unfold dampedSignWeight
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_oddSqrtMoebius_le q) (abs_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-- **The Fermi weight is paid at every damping.** -/
theorem receiverBounded_fermiWeight {ε : ℝ} (hε : 0 < ε) : ReceiverBounded (fermiWeight ε) := by
  have hfun : fermiWeight ε = RHTower.dirichletConv (dampedSignWeight ⇑oddSqrtMoebius ε)
      (dampedSignWeight fermiPattern ε) := by
    funext n
    have hAF : fermiAF * oddSqfAF = oddSqrtMoebius * (oddAF * fermiAF) := by
      rw [oddSqfAF_eq]; ring
    have hpat : (fun n => (oddAF * fermiAF) n) = fermiPattern := funext oddAF_mul_fermiAF_apply
    calc fermiWeight ε n
        = RHTower.dirichletConv (dampedSignWeight ⇑fermiAF ε) (dampedSignWeight ⇑oddSqfAF ε) n := by
          rw [fermiWeight, fermiKernel_eq]; rfl
      _ = dampedSignWeight ⇑(fermiAF * oddSqfAF) ε n := by
          rw [← dampedSignWeight_dirichletConv]
          simp only [dampedSignWeight, mul_apply_eq_dirichletConv]
      _ = dampedSignWeight ⇑(oddSqrtMoebius * (oddAF * fermiAF)) ε n := by rw [hAF]
      _ = RHTower.dirichletConv (dampedSignWeight ⇑oddSqrtMoebius ε)
            (dampedSignWeight fermiPattern ε) n := by
          rw [← hpat, dampedSignWeight, mul_apply_eq_dirichletConv,
            ← dampedSignWeight_dirichletConv]
          rfl
  rw [hfun]
  have hW := criticalWiener_dampedOddSqrtMoebius hε
  have hs : Summable (fun d : ℕ => |dampedSignWeight fermiPattern ε d / d|) := by
    refine ((Real.summable_nat_rpow.mpr (show -(1 + ε) < -1 by linarith)).mul_left 2).of_nonneg_of_le
      (fun _ => abs_nonneg _) fun d => ?_
    rw [dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_fermiPattern_le d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  exact receiverBounded_dirichletConv hW hs
    (exists_weightPronicEnergy_dampedSign_le zero_le_one hε abs_sum_range_fermiPattern_le)

/-- **The odd squarefree drift**: eventually `n Σ_{(n,2n]} o(d)/d ≥ (D/3) 2^{-1-ε} n^{1−ε}`, where
`D = 6/π²` is the squarefree density. -/
theorem eventually_oddSqfWeight_drift {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, RHTower.Sieve.squarefreeDensity / 3 * (2 : ℝ) ^ (-(1 + ε)) *
      (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), oddSqfWeight ε d / d := by
  have hD : 0 < RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  have hc := tendsto_oddSquarefreeWindow_card_div.eventually
    (eventually_gt_nhds (show RHTower.Sieve.squarefreeDensity / 3 <
      RHTower.Sieve.squarefreeDensity * 2 / 3 by linarith))
  filter_upwards [hc, eventually_ge_atTop 1] with n hcount hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcount' := (lt_div_iff₀ hn0).mp hcount
  set P := (2 * (n : ℝ)) ^ (-(1 + ε))
  have hP : 0 ≤ P := Real.rpow_nonneg (by positivity) _
  have hcell : ∀ d ∈ Ioc n (2 * n), oddSqfAF d * P ≤ oddSqfWeight ε d / d := fun d hd => by
    have hd := mem_Ioc.mp hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hd2 : (d : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
    have hnn : 0 ≤ oddSqfAF d := by rw [oddSqfAF_apply]; split_ifs <;> norm_num
    rw [oddSqfWeight, dampedSignWeight_div hε, mul_comm ((d : ℝ) ^ _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hd0 hd2 (by linarith)) hnn
  have hcard : ∑ d ∈ Ioc n (2 * n), oddSqfAF d = ((oddSquarefreeWindow n).card : ℝ) := by
    rw [oddSquarefreeWindow_card_eq_weighted_sum]
    refine sum_congr rfl fun d _ => ?_
    simp only [oddSqfAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply,
      oddAF_apply]
    by_cases h2 : 2 ∣ d <;> simp [h2, sq]
  have hsum : P * ((oddSquarefreeWindow n).card : ℝ) ≤
      ∑ d ∈ Ioc n (2 * n), oddSqfWeight ε d / d := by
    rw [← hcard, mul_sum]
    exact sum_le_sum fun d hd => by rw [mul_comm]; exact hcell d hd
  have hPn : P = (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (-(1 + ε)) := Real.mul_rpow (by norm_num) hn0.le
  have hpow : (n : ℝ) * ((n : ℝ) ^ (-(1 + ε)) * n) = (n : ℝ) ^ (1 - ε) := by
    rw [show (1 - ε) = 1 + (-(1 + ε) + 1) by ring, Real.rpow_add hn0, Real.rpow_add hn0,
      Real.rpow_one]
  calc RHTower.Sieve.squarefreeDensity / 3 * (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε)
      = (n : ℝ) * (P * (RHTower.Sieve.squarefreeDensity / 3 * n)) := by rw [hPn, ← hpow]; ring
    _ ≤ (n : ℝ) * (P * ((oddSquarefreeWindow n).card : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcount'.le hP) hn0.le
    _ ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), oddSqfWeight ε d / d :=
        mul_le_mul_of_nonneg_left hsum hn0.le

/-- **The even flip is unpaid** at every `ε ≤ 1/2`: its kernel is `2 − 2^{1−ε} ≠ 0` at the pole. -/
theorem not_receiverBounded_fermiFlipWeight {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ¬ ReceiverBounded (fermiFlipWeight ε) := by
  have hD : 0 < RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  have hκ : 0 < RHTower.Sieve.squarefreeDensity / 3 * (2 : ℝ) ^ (-(1 + ε)) := by positivity
  refine not_receiverBounded_dirichletConv_of_drift hε hε2 (oddSqfWeight_nonneg ε)
    (oddSqfWeight_mem_dampedClass ε) hκ (eventually_oddSqfWeight_drift hε) (J := 2)
    (fun j hj => by simp [flipKernel, show j ≠ 1 by omega, show j ≠ 2 by omega]) ?_
  have ht : (2 : ℝ) ^ (1 - ε) < 2 := by
    calc (2 : ℝ) ^ (1 - ε) < (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hinv : (2 : ℝ) ^ (1 - ε) * (2 : ℝ) ^ (-(1 - ε)) = 1 := by
    rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
  have hk1 : flipKernel ε 1 = 1 - (2 : ℝ) ^ (1 - ε) := by simp [flipKernel]
  have hk2 : flipKernel ε 2 = (2 : ℝ) ^ (1 - ε) := by simp [flipKernel]
  rw [show Icc 1 2 = ({1, 2} : Finset ℕ) by decide, sum_pair (by norm_num), hk1, hk2,
    Nat.cast_one, Real.one_rpow, mul_one, Nat.cast_ofNat, hinv]
  linarith

/-- **The Fermi parity pair.** For `0 < ε ≤ 1/2` the Fermi squarefree weight and its even flip lie
in the damped class, are related by the even flip (`F^♭(d) = F(d) + F(2d)` on odd `d`, `−F(d)` on
even `d`), have identical Ramanujan amplitudes, and have opposite receivers: `F` is paid, `F^♭` is
not. -/
theorem fermi_evenFlip_parityPair {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    DampedClass 3 ε (fermiWeight ε) ∧ DampedClass 3 ε (fermiFlipWeight ε) ∧
    fermiFlipWeight ε =
      (fun d => fermiWeight ε d + localFactorWeight (evenPartWeight (fermiWeight ε)) 2 2 d) ∧
    (∀ e, |weightRamanujanCoeff (fermiFlipWeight ε) e| = |weightRamanujanCoeff (fermiWeight ε) e|) ∧
    ReceiverBounded (fermiWeight ε) ∧ ¬ ReceiverBounded (fermiFlipWeight ε) := by
  refine ⟨fermiWeight_mem_dampedClass ε, fermiFlipWeight_mem_dampedClass hε.le (by linarith),
    fermiFlipWeight_eq ε, fun e => ?_, receiverBounded_fermiWeight hε,
    not_receiverBounded_fermiFlipWeight hε hε2⟩
  rw [weightRamanujanCoeff_fermiFlipWeight hε, abs_mul]
  unfold evenSign
  split_ifs <;> simp

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
