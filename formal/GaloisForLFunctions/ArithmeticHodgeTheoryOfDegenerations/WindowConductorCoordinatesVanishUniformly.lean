import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonLayerReadsWeilSummands
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeWindows
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorPlancherel

/-!
# Uniform conductor coordinates of a terminal window

Complete-period absolute mass bounds every conductor coordinate of a
bounded terminal window by its horizon logarithm normalization. The
actual conductor frame then controls the entire orthogonal projection.
-/

noncomputable section
set_option autoImplicit false
open Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  SuccessorShellArithmetic CriticalScaleArithmeticRigidity

/-- A Ramanujan prefix has absolute mass at most its length plus one period. -/
theorem sum_Icc_abs_normalizedRamanujanMode_le {m : ℕ} (hm : 0 < m) (N : ℕ) :
    (∑ n ∈ Icc 1 N, |normalizedRamanujanMode m n|) ≤ (N : ℝ) + m := by
  have hper : Function.Periodic (fun n => |normalizedRamanujanMode m n|) m :=
    fun n => congrArg abs (normalizedRamanujanMode_periodic hm n)
  have hIoc (D : ℕ) : Ioc 0 D = Icc 1 D := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  have hperiod := sum_Ioc_periodic_eq hm hper 0
  rw [zero_add, hIoc] at hperiod
  have hmass : (∑ n ∈ Icc 1 m, |normalizedRamanujanMode m n|) ≤ m := by
    rw [hperiod]
    exact sum_range_abs_normalizedRamanujanMode_le hm
  have h := sum_Ioc_le_mul_sum_Icc_of_periodic_pos hm
    (fun n _ => abs_nonneg (normalizedRamanujanMode m n)) (fun n _ => hper n) 0 N
  rw [hIoc, Nat.sub_zero] at h
  calc
    _ ≤ (((N / m + 1 : ℕ) : ℝ)) * ∑ n ∈ Icc 1 m, |normalizedRamanujanMode m n| := h
    _ ≤ (((N / m + 1 : ℕ) : ℝ)) * m :=
      mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg _)
    _ ≤ _ := by
      exact_mod_cast (show (N / m + 1) * m ≤ N + m from by
        calc
          _ = (N / m) * m + m := by ring
          _ ≤ _ := Nat.add_le_add_right (Nat.div_mul_le_self N m) m)

private theorem window_value_div_le {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) :
    |h (Real.log n - Real.log N)| / (n : ℝ) ≤ B * Real.exp A / N := by
  have hB0 : 0 ≤ B := (abs_nonneg (h 0)).trans (hB 0)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hz : h (Real.log n - Real.log N) = 0
  · rw [hz, abs_zero, zero_div]
    positivity
  have hs : Real.log n - Real.log N ∈ Set.Icc (-A) 0 := by
    by_contra hs
    exact hz (hsupp _ hs)
  have hexp := Real.exp_le_exp.mpr hs.1
  rw [Real.exp_sub, Real.exp_log hn0, Real.exp_log hN0] at hexp
  have hleft : (N : ℝ) * Real.exp (-A) ≤ n := by
    simpa only [mul_comm] using (le_div_iff₀ hN0).mp hexp
  have hscale : (N : ℝ) ≤ Real.exp A * n := by
    calc
      _ = Real.exp A * ((N : ℝ) * Real.exp (-A)) := by
        rw [Real.exp_neg]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hleft (Real.exp_pos A).le
  have hinv : 1 / (n : ℝ) ≤ Real.exp A / N := by
    rw [div_le_div_iff₀ hn0 hN0, one_mul]
    exact hscale
  calc
    _ = |h (Real.log n - Real.log N)| * (1 / (n : ℝ)) := by ring
    _ ≤ B * (Real.exp A / N) := mul_le_mul (hB _) hinv (by positivity) hB0
    _ = _ := by ring

/-- The window/conductor coordinate is its literal harmonic sum divided by `sqrt(log N)`. -/
theorem horizon_window_conductor_inner (h : ℝ → ℝ) (m N : ℕ) :
    ⟪horizonProfileVector (horizonWeights h N) N, normalizedRamanujanHorizonVector m N⟫ =
      (∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) * normalizedRamanujanMode m n / n) /
        Real.sqrt (Real.log N) := by
  rw [normalizedRamanujanHorizonVector, real_inner_smul_right,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (Real.sqrt (Real.log N))⁻¹ *
    (∑ n : PrimeHorizonIndex N, ramanujanPoleProfile m n * horizonWeights h N n) = _
  rw [sum_coe_sort (Icc 1 N) (fun n => ramanujanPoleProfile m n * horizonWeights h N n)]
  have hsum : (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * horizonWeights h N n) =
      ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) * normalizedRamanujanMode m n / n := by
    apply sum_congr rfl
    intro n hn
    rw [ramanujanPoleProfile, horizonWeights, div_mul_div_comm, ← sq,
      Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  rw [hsum]
  ring

/-- Every conductor through the horizon has the same inverse-square-root logarithmic bound. -/
theorem abs_horizon_window_conductor_inner_le {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    |⟪horizonProfileVector (horizonWeights h N) N, normalizedRamanujanHorizonVector m N⟫| ≤
      (2 * B * Real.exp A) / Real.sqrt (Real.log N) := by
  have hN : 1 ≤ N := hm.trans_le hmN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB0 : 0 ≤ B := (abs_nonneg (h 0)).trans (hB 0)
  have hpoint : ∀ n ∈ Icc 1 N,
      |h (Real.log n - Real.log N) * normalizedRamanujanMode m n / n| ≤
        (B * Real.exp A / N) * |normalizedRamanujanMode m n| := by
    intro n hn
    rw [abs_div, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
    calc
      _ = (|h (Real.log n - Real.log N)| / n) * |normalizedRamanujanMode m n| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (window_value_div_le hsupp hB hN (mem_Icc.mp hn).1) (abs_nonneg _)
  have hsum : |∑ n ∈ Icc 1 N,
      h (Real.log n - Real.log N) * normalizedRamanujanMode m n / n| ≤ 2 * B * Real.exp A := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, |h (Real.log n - Real.log N) * normalizedRamanujanMode m n / n| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, (B * Real.exp A / N) * |normalizedRamanujanMode m n| :=
        sum_le_sum hpoint
      _ = (B * Real.exp A / N) * ∑ n ∈ Icc 1 N, |normalizedRamanujanMode m n| :=
        (mul_sum _ _ _).symm
      _ ≤ (B * Real.exp A / N) * ((N : ℝ) + m) :=
        mul_le_mul_of_nonneg_left (sum_Icc_abs_normalizedRamanujanMode_le hm N) (by positivity)
      _ ≤ (B * Real.exp A / N) * ((N : ℝ) + N) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_left hmN N) (by positivity)
      _ = _ := by field_simp [hN0.ne']; ring
  rw [horizon_window_conductor_inner, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right hsum (Real.sqrt_nonneg _)

/-- Bounded terminal windows have uniformly bounded physical norm. -/
theorem horizon_window_norm_sq_le {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖horizonProfileVector (horizonWeights h N) N‖ ^ 2 ≤ B ^ 2 * Real.exp A := by
  have hB0 : 0 ≤ B := (abs_nonneg (h 0)).trans (hB 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [horizonProfileVector_norm_sq]
  have hpoint : ∀ n ∈ Icc 1 N, horizonWeights h N n ^ 2 ≤ B ^ 2 * Real.exp A / N := by
    intro n hn
    rw [horizonWeights, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    calc
      _ = |h (Real.log n - Real.log N)| * (|h (Real.log n - Real.log N)| / n) := by
        rw [mul_div_assoc', ← sq, sq_abs]
      _ ≤ B * (B * Real.exp A / N) := mul_le_mul (hB _)
        (window_value_div_le hsupp hB hN (mem_Icc.mp hn).1) (by positivity) hB0
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ Icc 1 N, B ^ 2 * Real.exp A / N := sum_le_sum hpoint
    _ = B ^ 2 * Real.exp A := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      field_simp [hN0.ne']

/-- The actual low-conductor projection of a terminal window has mass `O(Q/log N)`. -/
theorem horizon_window_conductor_projection_sq_le {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {Q N : ℕ} (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log N) :
    ‖(conductorSubspace Q N).starProjection (horizonProfileVector (horizonWeights h N) N)‖ ^ 2 ≤
      2 * (2 * B * Real.exp A) ^ 2 * Q / Real.log N := by
  have hB0 : 0 ≤ B := (abs_nonneg (h 0)).trans (hB 0)
  have hQN' : Q ≤ N := (Nat.le_mul_self Q).trans hQN
  have hpoint : ∀ m ∈ Icc 1 Q,
      ⟪horizonProfileVector (horizonWeights h N) N, normalizedRamanujanHorizonVector m N⟫ ^ 2 ≤
        (2 * B * Real.exp A) ^ 2 / Real.log N := by
    intro m hm
    have h := pow_le_pow_left₀ (abs_nonneg _)
      (abs_horizon_window_conductor_inner_le hsupp hB (mem_Icc.mp hm).1
        ((mem_Icc.mp hm).2.trans hQN')) 2
    simpa only [sq_abs, div_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)] using h
  calc
    _ ≤ 2 * ∑ m ∈ Icc 1 Q,
        ⟪horizonProfileVector (horizonWeights h N) N, normalizedRamanujanHorizonVector m N⟫ ^ 2 :=
      primeCharge_conductor_projection_sq_le hQ hQN hlog _
    _ ≤ 2 * ∑ m ∈ Icc 1 Q, (2 * B * Real.exp A) ^ 2 / Real.log N :=
      mul_le_mul_of_nonneg_left (sum_le_sum hpoint) (by norm_num)
    _ = _ := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_horizon_window_conductor_inner_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.horizon_window_norm_sq_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.horizon_window_conductor_projection_sq_le
