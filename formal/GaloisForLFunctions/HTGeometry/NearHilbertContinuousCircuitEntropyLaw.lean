import GaloisForLFunctions.HTGeometry.UniformProjectiveFixedErrorCircuitHardIntervalLaw

/-!
# Near-Hilbert continuous-circuit entropy law

On `n` qubits, continuous two-qubit circuits with at most
`2^n / (64 (n+1))` gates have fixed-resolution metric entropy strictly below
the anchored Boolean projective carrier.  This reaches Hilbert-space dimension
up to one logarithmic factor, rather than stopping at polynomial gate count.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Gate budget of Hilbert-space dimension divided by one logarithmic factor. -/
def nearHilbertContinuousCircuitBudget (n : ℕ) : ℕ :=
  2 ^ n / (64 * (n + 1))

private theorem four_mul_add_lt_two_pow
    {n : ℕ} (hn : 8 ≤ n) :
    4 * n + 12 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn8 ih =>
      rw [pow_succ]
      have hlarge : 4 ≤ 2 ^ n := by
        have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
        omega
      omega

private theorem le_two_pow_of_four
    {n : ℕ} (hn : 4 ≤ n) : n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn4 ih =>
      rw [pow_succ]
      omega

private theorem nearHilbertContinuousCircuitBudget_entropy_majorant
    {n : ℕ} (hn : 8 ≤ n) :
    atMostQuarterCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) ≤
      (2 : ℝ) ^
        ((34 * n + 160) * nearHilbertContinuousCircuitBudget n + n + 2) := by
  let s := nearHilbertContinuousCircuitBudget n
  let A := 34 * n + 160
  have hs_le : s ≤ 2 ^ n := by
    dsimp [s, nearHilbertContinuousCircuitBudget]
    exact Nat.div_le_self _ _
  have hn_two_pow : n ≤ 2 ^ n := le_two_pow_of_four (by omega)
  have hnn : n * n ≤ 2 ^ (2 * n) := by
    calc
      n * n ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hn_two_pow hn_two_pow
      _ = 2 ^ (2 * n) := by rw [← pow_add]; congr 1; omega
  have hbaseR {R : ℕ} (hR : R ≤ s) :
      1 + 16 * R ≤ 2 ^ (n + 5) := by
    have hRpow : R ≤ 2 ^ n := hR.trans hs_le
    calc
      1 + 16 * R ≤ 32 * 2 ^ n := by omega
      _ = 2 ^ (n + 5) := by
        rw [show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_add]
        congr 1
        omega
  have hterm {R : ℕ} (hRmem : R ∈ Finset.range (s + 1)) :
      1 + ((n * n : ℕ) : ℝ) ^ R *
          (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
        (2 : ℝ) ^ (A * s + 1) := by
    have hR : R ≤ s := by simpa using Finset.mem_range.mp hRmem
    have hfirst :
        ((n * n : ℕ) : ℝ) ^ R ≤ (2 : ℝ) ^ ((2 * n) * R) := by
      have hnnR : (((n * n : ℕ) : ℝ)) ≤ ((2 ^ (2 * n) : ℕ) : ℝ) := by
        exact_mod_cast hnn
      calc
        ((n * n : ℕ) : ℝ) ^ R ≤ (((2 ^ (2 * n) : ℕ) : ℝ)) ^ R :=
          pow_le_pow_left₀ (by positivity) hnnR R
        _ = (2 : ℝ) ^ ((2 * n) * R) := by
          push_cast
          rw [← pow_mul]
    have hsecond :
        (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
          (2 : ℝ) ^ ((n + 5) * (32 * R)) := by
      have hbaseReal :
          (1 : ℝ) + 16 * (R : ℝ) ≤ ((2 ^ (n + 5) : ℕ) : ℝ) := by
        exact_mod_cast hbaseR hR
      calc
        (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
            (((2 ^ (n + 5) : ℕ) : ℝ)) ^ (32 * R) :=
          pow_le_pow_left₀ (by positivity) hbaseReal _
        _ = (2 : ℝ) ^ ((n + 5) * (32 * R)) := by
          push_cast
          rw [← pow_mul]
    have hproduct :
        ((n * n : ℕ) : ℝ) ^ R *
            (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
          (2 : ℝ) ^ (A * s) := by
      calc
        ((n * n : ℕ) : ℝ) ^ R *
              (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
            (2 : ℝ) ^ ((2 * n) * R) *
              (2 : ℝ) ^ ((n + 5) * (32 * R)) :=
          mul_le_mul hfirst hsecond (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (A * R) := by
          rw [← pow_add]
          congr 1
          dsimp [A]
          ring
        _ ≤ (2 : ℝ) ^ (A * s) := by
          exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left A hR)
    calc
      1 + ((n * n : ℕ) : ℝ) ^ R *
            (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
          (2 : ℝ) ^ (A * s) + (2 : ℝ) ^ (A * s) := by
        exact add_le_add (one_le_pow₀ (by norm_num)) hproduct
      _ = (2 : ℝ) ^ (A * s + 1) := by rw [pow_succ]; ring
  have hsum :
      atMostQuarterCircuitEntropyBound n s ≤
        (((s + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (A * s + 1) := by
    rw [atMostQuarterCircuitEntropyBound]
    calc
      ∑ R ∈ Finset.range (s + 1),
          (1 + ((n * n : ℕ) : ℝ) ^ R *
            (1 + 16 * (R : ℝ)) ^ (32 * R)) ≤
          ∑ R ∈ Finset.range (s + 1), (2 : ℝ) ^ (A * s + 1) := by
        exact Finset.sum_le_sum fun R hR => hterm hR
      _ = (((s + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (A * s + 1) := by simp
  have hs_succ : s + 1 ≤ 2 ^ (n + 1) := by
    calc
      s + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right hs_le 1
      _ ≤ 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hs_succ_real : (((s + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (n + 1) := by
    have : (((s + 1 : ℕ) : ℝ)) ≤ (((2 ^ (n + 1) : ℕ) : ℝ)) := by
      exact_mod_cast hs_succ
    simpa using this
  calc
    atMostQuarterCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) =
        atMostQuarterCircuitEntropyBound n s := by rfl
    _ ≤ (((s + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (A * s + 1) := hsum
    _ ≤ (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (A * s + 1) :=
      mul_le_mul_of_nonneg_right hs_succ_real (by positivity)
    _ = (2 : ℝ) ^ (A * s + n + 2) := by
      rw [← pow_add]
      congr 1
      omega

/-- Eventually, all circuits below Hilbert dimension divided by one logarithmic
factor occupy less fixed-resolution entropy than one anchored spectral sign
carrier. -/
theorem eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier :
    ∀ᶠ n : ℕ in Filter.atTop,
      atMostQuarterCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) <
        ((2 ^ (2 ^ n - 1) : ℕ) : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop 8] with n hn
  let s := nearHilbertContinuousCircuitBudget n
  let A := 34 * n + 160
  have hA : A ≤ 48 * (n + 1) := by
    dsimp [A]
    omega
  have hdiv : (64 * (n + 1)) * s ≤ 2 ^ n := by
    dsimp [s, nearHilbertContinuousCircuitBudget]
    exact Nat.mul_div_le _ _
  have hbudget : 4 * (A * s) ≤ 3 * 2 ^ n := by
    calc
      4 * (A * s) ≤ 4 * (48 * (n + 1) * s) := by
        exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right s hA)
      _ = 3 * ((64 * (n + 1)) * s) := by ring
      _ ≤ 3 * 2 ^ n := Nat.mul_le_mul_left 3 hdiv
  have hsmall := four_mul_add_lt_two_pow hn
  have hexponent : A * s + n + 2 < 2 ^ n - 1 := by
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
    omega
  have hmajor := nearHilbertContinuousCircuitBudget_entropy_majorant hn
  have hpowlt :
      (2 : ℝ) ^ (A * s + n + 2) < (2 : ℝ) ^ (2 ^ n - 1) := by
    exact pow_lt_pow_right₀ (by norm_num) hexponent
  calc
    atMostQuarterCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) ≤
        (2 : ℝ) ^ (A * s + n + 2) := by simpa [A, s] using hmajor
    _ < (2 : ℝ) ^ (2 ^ n - 1) := hpowlt
    _ = ((2 ^ (2 ^ n - 1) : ℕ) : ℝ) := by norm_cast

end

end GaloisForLFunctions.HTGeometry
