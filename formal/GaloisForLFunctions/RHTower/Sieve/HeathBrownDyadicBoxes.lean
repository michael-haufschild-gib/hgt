import GaloisForLFunctions.RHTower.Sieve.HeathBrownPerronPacket

/-!
# Multiplicative dyadic boxes for finite Heath--Brown cores

Applying Perron to an undecomposed finite core introduces artificial support up to `X^j`.  The
published argument first splits every individual factor into dyadic blocks.  This file performs
that split at coefficient level, expands convolution powers into finite tuples, and proves exact
lower and upper multiplicative support for every resulting `2j`-factor box.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- One dyadic coefficient block of a real arithmetic function. -/
def arithmeticDyadicBlock (F : ArithmeticFunction ℝ) (q : ℕ) : ArithmeticFunction ℝ where
  toFun n := if Nat.log 2 n = q then F n else 0
  map_zero' := by simp

@[simp] theorem arithmeticDyadicBlock_apply
    (F : ArithmeticFunction ℝ) (q n : ℕ) :
    arithmeticDyadicBlock F q n = if Nat.log 2 n = q then F n else 0 := rfl

theorem complexCoeff_arithmeticDyadicBlock
    (F : ArithmeticFunction ℝ) (q : ℕ) :
    complexCoeff (arithmeticDyadicBlock F q) =
      coeffBlock (complexCoeff F) (fun n => Nat.log 2 n) q := by
  funext n
  by_cases hq : Nat.log 2 n = q
  · simp [arithmeticDyadicBlock, coeffBlock, complexCoeff, hq]
  · simp [arithmeticDyadicBlock, coeffBlock, complexCoeff, hq]

theorem arithmeticFinsetSum_apply {ι : Type*} (u : Finset ι)
    (F : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ u, F i) n = ∑ i ∈ u, F i n := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | @insert a u ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ArithmeticFunction.add_apply, ih]

/-- Every finitely supported arithmetic function is the exact sum of its dyadic coefficient
blocks. -/
theorem eq_sum_arithmeticDyadicBlocks
    {F : ArithmeticFunction ℝ} {M : ℕ} (hF : UpperSupported F M) :
    F = ∑ q ∈ Finset.range (Nat.log 2 M + 1), arithmeticDyadicBlock F q := by
  ext n
  rw [arithmeticFinsetSum_apply]
  by_cases hn : F n = 0
  · simp [arithmeticDyadicBlock, hn]
  · have hnmem := hF n hn
    have hlog : Nat.log 2 n ≤ Nat.log 2 M := Nat.log_mono_right (Finset.mem_Icc.mp hnmem).2
    have hqmem : Nat.log 2 n ∈ Finset.range (Nat.log 2 M + 1) := by
      rw [Finset.mem_range]
      omega
    calc
      F n = arithmeticDyadicBlock F (Nat.log 2 n) n := by
        simp [arithmeticDyadicBlock]
      _ = ∑ q ∈ Finset.range (Nat.log 2 M + 1), arithmeticDyadicBlock F q n := by
        symm
        apply Finset.sum_eq_single (Nat.log 2 n)
        · intro q hq hne
          simp [arithmeticDyadicBlock, Ne.symm hne]
        · intro hnot
          exact (hnot hqmem).elim

/-- Admissible tuples of dyadic indices for `r` identical factors supported through `M`. -/
def dyadicChoiceSet (r M : ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset fun _ : Fin r => Finset.range (Nat.log 2 M + 1)

/-- Product of the dyadic blocks selected by one tuple. -/
def dyadicBlockProduct
    (F : ArithmeticFunction ℝ) (r : ℕ) (q : Fin r → ℕ) : ArithmeticFunction ℝ :=
  ∏ i, arithmeticDyadicBlock F (q i)

/-- Exact tuple expansion of a convolution power. -/
theorem pow_eq_sum_dyadicBlockProducts
    {F : ArithmeticFunction ℝ} {M : ℕ} (hF : UpperSupported F M) (r : ℕ) :
    F ^ r = ∑ q ∈ dyadicChoiceSet r M, dyadicBlockProduct F r q := by
  calc
    F ^ r = (∑ q ∈ Finset.range (Nat.log 2 M + 1),
        arithmeticDyadicBlock F q) ^ r :=
      congrArg (fun G : ArithmeticFunction ℝ => G ^ r)
        (eq_sum_arithmeticDyadicBlocks hF)
    _ = ∑ q ∈ dyadicChoiceSet r M, dyadicBlockProduct F r q := by
      simpa [dyadicChoiceSet, dyadicBlockProduct] using
        (Finset.sum_pow' (Finset.range (Nat.log 2 M + 1))
          (fun q => arithmeticDyadicBlock F q) r)

/-- Lower edge of one dyadic block. -/
theorem vanishesBelow_arithmeticDyadicBlock
    (F : ArithmeticFunction ℝ) (q : ℕ) :
    VanishesBelow (arithmeticDyadicBlock F q) (2 ^ q) := by
  intro n hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [arithmeticDyadicBlock]
  · by_cases hq : Nat.log 2 n = q
    · have hpow := Nat.pow_log_le_self 2 hn0
      rw [hq] at hpow
      exact (not_le_of_gt hn hpow).elim
    · simp [arithmeticDyadicBlock, hq]

/-- Upper edge of one dyadic block. -/
theorem upperSupported_arithmeticDyadicBlock
    (F : ArithmeticFunction ℝ) (q : ℕ) :
    UpperSupported (arithmeticDyadicBlock F q) (2 ^ (q + 1)) := by
  intro n hn
  have hq : Nat.log 2 n = q := by
    by_contra h
    exact hn (by simp [arithmeticDyadicBlock, h])
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    exact hn (by simp [arithmeticDyadicBlock])
  have hupper := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  rw [hq] at hupper
  exact Finset.mem_Icc.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr hn0, Nat.le_of_lt hupper⟩

theorem vanishesBelow_dyadicBlockProduct
    (F : ArithmeticFunction ℝ) (r : ℕ) (q : Fin r → ℕ) :
    VanishesBelow (dyadicBlockProduct F r q) (∏ i, 2 ^ q i) := by
  classical
  have hprod : ∀ u : Finset (Fin r),
      VanishesBelow (∏ i ∈ u, arithmeticDyadicBlock F (q i))
        (∏ i ∈ u, 2 ^ q i) := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        simpa using (show VanishesBelow (1 : ArithmeticFunction ℝ) 1 by
          intro n hn
          have hn0 : n = 0 := by omega
          subst n
          simp)
    | @insert a u ha ih =>
        simp only [Finset.prod_insert ha]
        exact vanishesBelow_mul (vanishesBelow_arithmeticDyadicBlock F (q a)) ih
  simpa [dyadicBlockProduct] using hprod Finset.univ

theorem upperSupported_dyadicBlockProduct
    (F : ArithmeticFunction ℝ) (r : ℕ) (q : Fin r → ℕ) :
    UpperSupported (dyadicBlockProduct F r q) (∏ i, 2 ^ (q i + 1)) := by
  classical
  have hprod : ∀ u : Finset (Fin r),
      UpperSupported (∏ i ∈ u, arithmeticDyadicBlock F (q i))
        (∏ i ∈ u, 2 ^ (q i + 1)) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa using upperSupported_one
    | @insert a u ha ih =>
        simp only [Finset.prod_insert ha]
        exact (upperSupported_arithmeticDyadicBlock F (q a)).mul ih
  simpa [dyadicBlockProduct] using hprod Finset.univ

/-- One `2j`-factor dyadic box in a degree-`j` Heath--Brown core. -/
def heathBrownDyadicCoreBox
    (L X j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) :
    ArithmeticFunction ℝ :=
  dyadicBlockProduct (truncatedMoebius L) j a *
    dyadicBlockProduct (coeffTrunc (zeta : ArithmeticFunction ℝ) X) (j - 1) b *
    arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q

/-- **Exact coefficient-level dyadic-box expansion of a positive-degree Heath--Brown core.** -/
theorem heathBrownFiniteCore_eq_sum_dyadicBoxes (L X j : ℕ) :
    heathBrownFiniteCore L X j =
      ∑ q ∈ Finset.range (Nat.log 2 X + 1),
        ∑ b ∈ dyadicChoiceSet (j - 1) X,
          ∑ a ∈ dyadicChoiceSet j L,
            heathBrownDyadicCoreBox L X j a b q := by
  rw [heathBrownFiniteCore,
    pow_eq_sum_dyadicBlockProducts (upperSupported_truncatedMoebius L) j,
    pow_eq_sum_dyadicBlockProducts
      (upperSupported_coeffTrunc (zeta : ArithmeticFunction ℝ) X) (j - 1),
    eq_sum_arithmeticDyadicBlocks
      (upperSupported_coeffTrunc ArithmeticFunction.log X)]
  simp only [Finset.sum_mul, Finset.mul_sum, heathBrownDyadicCoreBox]

/-- Exact lower product edge of one dyadic core box. -/
theorem vanishesBelow_heathBrownDyadicCoreBox
    (L X j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) :
    VanishesBelow (heathBrownDyadicCoreBox L X j a b q)
      (((∏ i, 2 ^ a i) * (∏ i, 2 ^ b i)) * 2 ^ q) := by
  exact vanishesBelow_mul
    (vanishesBelow_mul
      (vanishesBelow_dyadicBlockProduct (truncatedMoebius L) j a)
      (vanishesBelow_dyadicBlockProduct
        (coeffTrunc (zeta : ArithmeticFunction ℝ) X) (j - 1) b))
    (vanishesBelow_arithmeticDyadicBlock
      (coeffTrunc ArithmeticFunction.log X) q)

/-- Exact upper product edge of one dyadic core box. -/
theorem upperSupported_heathBrownDyadicCoreBox
    (L X j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) :
    UpperSupported (heathBrownDyadicCoreBox L X j a b q)
      (((∏ i, 2 ^ (a i + 1)) * (∏ i, 2 ^ (b i + 1))) * 2 ^ (q + 1)) := by
  exact ((upperSupported_dyadicBlockProduct (truncatedMoebius L) j a).mul
    (upperSupported_dyadicBlockProduct
      (coeffTrunc (zeta : ArithmeticFunction ℝ) X) (j - 1) b)).mul
    (upperSupported_arithmeticDyadicBlock
      (coeffTrunc ArithmeticFunction.log X) q)

/-- Multiplicative lower edge of a dyadic core box. -/
def heathBrownDyadicCoreLower
    (j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) : ℕ :=
  ((∏ i, 2 ^ a i) * (∏ i, 2 ^ b i)) * 2 ^ q

/-- Multiplicative upper edge of a dyadic core box. -/
def heathBrownDyadicCoreUpper
    (j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) : ℕ :=
  ((∏ i, 2 ^ (a i + 1)) * (∏ i, 2 ^ (b i + 1))) * 2 ^ (q + 1)

theorem vanishesBelow_heathBrownDyadicCoreBox_lower
    (L X j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) :
    VanishesBelow (heathBrownDyadicCoreBox L X j a b q)
      (heathBrownDyadicCoreLower j a b q) := by
  simpa [heathBrownDyadicCoreLower] using
    vanishesBelow_heathBrownDyadicCoreBox L X j a b q

theorem upperSupported_heathBrownDyadicCoreBox_upper
    (L X j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) :
    UpperSupported (heathBrownDyadicCoreBox L X j a b q)
      (heathBrownDyadicCoreUpper j a b q) := by
  simpa [heathBrownDyadicCoreUpper] using
    upperSupported_heathBrownDyadicCoreBox L X j a b q

/-- Widening every factor from its dyadic lower edge to its upper edge costs exactly `2^r` for
`r` factors. -/
theorem prod_two_pow_succ_eq
    (r : ℕ) (a : Fin r → ℕ) :
    (∏ i, 2 ^ (a i + 1)) = 2 ^ r * ∏ i, 2 ^ a i := by
  simp_rw [pow_add, pow_one]
  rw [Finset.prod_mul_distrib]
  simp [mul_comm]

/-- A positive-degree `2j`-factor dyadic box has upper edge exactly `2^(2j)` times its lower
edge. -/
theorem heathBrownDyadicCoreUpper_eq_twoPow_mul_lower
    {j : ℕ} (hj : 1 ≤ j) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) :
    heathBrownDyadicCoreUpper j a b q =
      2 ^ (2 * j) * heathBrownDyadicCoreLower j a b q := by
  rw [heathBrownDyadicCoreUpper, heathBrownDyadicCoreLower,
    prod_two_pow_succ_eq, prod_two_pow_succ_eq]
  have hcoef : 2 ^ j * 2 ^ (j - 1) * 2 = 2 ^ (2 * j) := by
    calc
      2 ^ j * 2 ^ (j - 1) * 2 = 2 ^ (j + (j - 1) + 1) := by
        rw [pow_add, pow_add, pow_one]
      _ = 2 ^ (2 * j) := by
        congr 1
        omega
  rw [pow_succ]
  calc
    (2 ^ j * ∏ i, 2 ^ a i) * (2 ^ (j - 1) * ∏ i, 2 ^ b i) *
        (2 ^ q * 2) =
      (2 ^ j * 2 ^ (j - 1) * 2) *
        (((∏ i, 2 ^ a i) * ∏ i, 2 ^ b i) * 2 ^ q) := by ring
    _ = 2 ^ (2 * j) * (((∏ i, 2 ^ a i) * ∏ i, 2 ^ b i) * 2 ^ q) := by
      rw [hcoef]

/-- Every dyadic box meeting a prefix through `X` is supported in a constant-factor enlargement
of that prefix; the constant depends only on its fixed degree. -/
theorem heathBrownDyadicCoreUpper_le_of_lower_le
    {j X : ℕ} (hj : 1 ≤ j) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ)
    (hbox : heathBrownDyadicCoreLower j a b q ≤ X) :
    heathBrownDyadicCoreUpper j a b q ≤ 2 ^ (2 * j) * X := by
  rw [heathBrownDyadicCoreUpper_eq_twoPow_mul_lower hj]
  exact Nat.mul_le_mul_left _ hbox

end RHTower.Sieve
