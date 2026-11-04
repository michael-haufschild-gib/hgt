import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheActualNearCenterHasItsSignedFinitePart

/-!
# Terminal weights preserve harmonic gap rows

Abel summation bounds a terminally weighted periodic row independently
of its length and starting point. Ramanujan autocorrelation identifies
the signed mean before summation against the reciprocal gap.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology Set

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence

/-- A bounded Lipschitz terminal weight preserves periodic averaging on every subinterval. -/
theorem abs_sum_range_terminal_weight_sub_mean_le
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hp : ∀ n, p (n + q) = p n)
    {B : ℝ} (hB : ∀ n, |p n| ≤ B)
    {a M N : ℕ} (hN : 1 ≤ N) (haM : a + M ≤ N) :
    |(∑ i ∈ range (M + 1), F (((a + i : ℕ) : ℝ) / N) * p (a + i)) -
      periodicMean p q * ∑ i ∈ range (M + 1), F (((a + i : ℕ) : ℝ) / N)| ≤
      2 * q * B * (BF + LF) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hmem : ∀ i ≤ M, ((a + i : ℕ) : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    refine ⟨by positivity, (div_le_one hN0).mpr ?_⟩
    exact_mod_cast (show a + i ≤ N by omega)
  have hstep : ∀ i ∈ range M,
      |F (((a + (i + 1) : ℕ) : ℝ) / N) - F (((a + i : ℕ) : ℝ) / N)| ≤ LF / N := by
    intro i hi
    have hiM := mem_range.mp hi
    have h := hFL _ (hmem (i + 1) (by omega)) _ (hmem i (by omega))
    have heq : (((a + (i + 1) : ℕ) : ℝ) / N) - (((a + i : ℕ) : ℝ) / N) = 1 / N := by
      push_cast
      ring
    rw [heq, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)] at h
    exact h.trans_eq (by ring)
  have hvariation : (∑ i ∈ range M,
      |F (((a + (i + 1) : ℕ) : ℝ) / N) - F (((a + i : ℕ) : ℝ) / N)|) ≤ LF := by
    calc
      _ ≤ ∑ _i ∈ range M, LF / N := sum_le_sum hstep
      _ = (M : ℝ) * (LF / N) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (LF / N) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (show M ≤ N by omega)) (div_nonneg hLF hN0.le)
      _ = LF := by field_simp
  exact (abs_sum_range_mul_shift_sub_mean_le hq hp hB a
    (fun i => F (((a + i : ℕ) : ℝ) / N)) M).trans
      (mul_le_mul_of_nonneg_left (add_le_add (hF _) hvariation) (by positivity))

/-- The two orientations of a Ramanujan gap have mean twice its diagonal lag coefficient. -/
theorem periodicMean_ramanujan_gapRow {m l : ℕ} (hm : 0 < m) (hl : 0 < l) (h : ℕ) :
    periodicMean (fun n => ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
      ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n) (l * m) =
        2 * (if m = l then ramanujanLagCoefficient m h else 0) := by
  have hq0 : (0 : ℝ) < (l * m : ℕ) := by exact_mod_cast Nat.mul_pos hl hm
  have h₁ := sum_range_lag_mul_lag_add hm hl h
  have h₂ := sum_range_lag_mul_lag_add hl hm h
  rw [Nat.mul_comm m l] at h₂
  unfold periodicMean
  rw [sum_add_distrib]
  have heq : (∑ n ∈ range (l * m),
      ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n) =
      ∑ n ∈ range (l * m), ramanujanLagCoefficient m n * ramanujanLagCoefficient l (n + h) :=
    sum_congr rfl fun _ _ => mul_comm _ _
  rw [heq, h₁, h₂]
  by_cases hml : m = l
  · subst l
    simp only [if_true]
    field_simp [hq0.ne']
    ring
  · simp only [if_neg hml, if_neg (Ne.symm hml), zero_add, zero_div, mul_zero]

/-- A terminally weighted harmonic gap row has an error uniform in its gap and endpoints. -/
theorem abs_sum_range_terminal_ramanujan_gapRow_sub_le
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {m l a M N : ℕ} (hm : 0 < m) (hl : 0 < l)
    (hN : 1 ≤ N) (haM : a + M ≤ N) (h : ℕ) :
    |(∑ i ∈ range (M + 1), F (((a + i : ℕ) : ℝ) / N) *
        (ramanujanLagCoefficient l (a + i) * ramanujanLagCoefficient m (a + i + h) +
          ramanujanLagCoefficient l (a + i + h) * ramanujanLagCoefficient m (a + i))) -
      (2 * (if m = l then ramanujanLagCoefficient m h else 0)) *
        ∑ i ∈ range (M + 1), F (((a + i : ℕ) : ℝ) / N)| ≤
      2 * (l * m : ℕ) *
        (2 * (∑ d ∈ l.divisors, (d : ℝ)) * ∑ d ∈ m.divisors, (d : ℝ)) * (BF + LF) := by
  let p : ℕ → ℝ := fun n =>
    ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
      ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n
  let B : ℝ := 2 * (∑ d ∈ l.divisors, (d : ℝ)) * ∑ d ∈ m.divisors, (d : ℝ)
  have hperL : ∀ n, ramanujanLagCoefficient l (n + l * m) = ramanujanLagCoefficient l n :=
    fun n => ramanujanLagCoefficient_add_mul l n m
  have hperM : ∀ n, ramanujanLagCoefficient m (n + l * m) = ramanujanLagCoefficient m n := by
    intro n
    rw [Nat.mul_comm l m]
    exact ramanujanLagCoefficient_add_mul m n l
  have hp : ∀ n, p (n + l * m) = p n := by
    intro n
    dsimp only [p]
    rw [show n + l * m + h = n + h + l * m by omega,
      hperL n, hperM n, hperL (n + h), hperM (n + h)]
  have hB : ∀ n, |p n| ≤ B := by
    intro n
    dsimp only [p]
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul]
    have hb₁ := mul_le_mul (abs_ramanujanLagCoefficient_le l n)
      (abs_ramanujanLagCoefficient_le m (n + h)) (abs_nonneg _) (by positivity)
    have hb₂ := mul_le_mul (abs_ramanujanLagCoefficient_le l (n + h))
      (abs_ramanujanLagCoefficient_le m n) (abs_nonneg _) (by positivity)
    exact (add_le_add hb₁ hb₂).trans_eq (by dsimp only [B]; ring)
  have hb := abs_sum_range_terminal_weight_sub_mean_le hF hLF hFL (Nat.mul_pos hl hm)
    hp hB hN haM
  rw [periodicMean_ramanujan_gapRow hm hl h] at hb
  exact hb

/-- The same weighted gap estimate includes empty integer intervals. -/
theorem abs_sum_Icc_terminal_ramanujan_gapRow_sub_le
    {F : ℝ → ℝ} {BF LF : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {m l a b N : ℕ} (hm : 0 < m) (hl : 0 < l)
    (hN : 1 ≤ N) (hbN : b ≤ N) (h : ℕ) :
    |(∑ n ∈ Finset.Icc a b, F ((n : ℝ) / N) *
        (ramanujanLagCoefficient l n * ramanujanLagCoefficient m (n + h) +
          ramanujanLagCoefficient l (n + h) * ramanujanLagCoefficient m n)) -
      (2 * (if m = l then ramanujanLagCoefficient m h else 0)) *
        ∑ n ∈ Finset.Icc a b, F ((n : ℝ) / N)| ≤
      2 * (l * m : ℕ) *
        (2 * (∑ d ∈ l.divisors, (d : ℝ)) * ∑ d ∈ m.divisors, (d : ℝ)) * (BF + LF) := by
  by_cases hab : a ≤ b
  · have hreindex (f : ℕ → ℝ) : (∑ n ∈ Finset.Icc a b, f n) =
        ∑ i ∈ range (b - a + 1), f (a + i) := by
      have heq : Finset.Icc a b = Finset.Ico a (b + 1) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [heq, sum_Ico_eq_sum_range, show b + 1 - a = b - a + 1 by omega]
    rw [hreindex, hreindex]
    exact abs_sum_range_terminal_ramanujan_gapRow_sub_le hF hLF hFL hm hl hN
      (show a + (b - a) ≤ N by omega) h
  · rw [Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge hab)]
    simp only [sum_empty, mul_zero, sub_self, abs_zero]
    have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
    positivity

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_sum_range_terminal_ramanujan_gapRow_sub_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_sum_Icc_terminal_ramanujan_gapRow_sub_le
