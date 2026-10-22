import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowSubpowerGate
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Removing the higher-prime-power channel from the dyadic RH window

The von Mangoldt window splits exactly into its prime part and its higher-prime-power part.  On a
dyadic interval the second part is unconditionally at most `2 * sqrt 2 * log n`: the weight
`k⁻¹ᐟ²` is uniformly at most `sqrt 2 * n⁻¹ᐟ²`, while Chebyshev's elementary estimate gives
`psi(n) - theta(n) ≤ 2 * sqrt n * log n`.

Consequently the all-epsilon subpower upper problem for the full von Mangoldt window is exactly
equivalent to the same problem over primes alone.  This removes every repeated prime orbit from
the remaining RH-bearing source obligation without assuming RH or an analytic continuation.
-/

open scoped BigOperators
open Finset ArithmeticFunction

noncomputable section

namespace RHTower

/-- The prime-only part of the dyadic critical-weight window. -/
def dyadicWeightedPrimeOnlyWindow (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc (n / 2) n with k.Prime, Real.log k / Real.sqrt k

/-- The contribution of the proper prime powers in the same window. -/
def dyadicWeightedHigherPrimePowerWindow (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc (n / 2) n,
    Mertens.notPrimeVonMangoldt k / Real.sqrt k

private theorem notPrimeVonMangoldt_nonneg (k : ℕ) :
    0 ≤ Mertens.notPrimeVonMangoldt k := by
  rw [Mertens.notPrimeVonMangoldt]
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- Exact prime/proper-prime-power splitting of the von Mangoldt window. -/
theorem dyadicWeightedPrimeWindow_eq_primeOnly_add_higherPrimePower (n : ℕ) :
    dyadicWeightedPrimeWindow n =
      dyadicWeightedPrimeOnlyWindow n + dyadicWeightedHigherPrimePowerWindow n := by
  rw [dyadicWeightedPrimeWindow, dyadicWeightedPrimeOnlyWindow,
    dyadicWeightedHigherPrimePowerWindow, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hp : k.Prime
  · simp [hp, Mertens.notPrimeVonMangoldt,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [hp, Mertens.notPrimeVonMangoldt]

/-- The proper-prime-power channel is pointwise nonnegative. -/
theorem dyadicWeightedHigherPrimePowerWindow_nonneg (n : ℕ) :
    0 ≤ dyadicWeightedHigherPrimePowerWindow n := by
  rw [dyadicWeightedHigherPrimePowerWindow]
  exact Finset.sum_nonneg fun k _ =>
    div_nonneg (notPrimeVonMangoldt_nonneg k) (Real.sqrt_nonneg k)

/-- **Higher-prime-power logarithmic bound.**  The repeated-prime channel is only logarithmic on
every dyadic interval. -/
theorem dyadicWeightedHigherPrimePowerWindow_le_log
    {n : ℕ} (hn : 1 ≤ n) :
    dyadicWeightedHigherPrimePowerWindow n ≤
      2 * Real.sqrt 2 * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hfactor : 0 ≤ Real.sqrt 2 / Real.sqrt n := by positivity
  rw [dyadicWeightedHigherPrimePowerWindow]
  calc
    (∑ k ∈ Ioc (n / 2) n,
        Mertens.notPrimeVonMangoldt k / Real.sqrt k) ≤
        ∑ k ∈ Ioc (n / 2) n,
          (Real.sqrt 2 / Real.sqrt n) * Mertens.notPrimeVonMangoldt k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k := by
        have := (Finset.mem_Ioc.mp hk).1
        omega
      have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
      have hsqrtk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
      have hnk : n ≤ 2 * k := by
        have := (Finset.mem_Ioc.mp hk).1
        omega
      have hsqrt : Real.sqrt n ≤ Real.sqrt 2 * Real.sqrt k := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hnk)
      have hinv : 1 / Real.sqrt k ≤ Real.sqrt 2 / Real.sqrt n := by
        rw [div_le_div_iff₀ hsqrtk hsqrtn]
        simpa only [one_mul] using hsqrt
      rw [div_eq_mul_inv]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hinv
        (notPrimeVonMangoldt_nonneg k)
    _ = (Real.sqrt 2 / Real.sqrt n) *
        ∑ k ∈ Ioc (n / 2) n, Mertens.notPrimeVonMangoldt k := by
      rw [Finset.mul_sum]
    _ ≤ (Real.sqrt 2 / Real.sqrt n) *
        ∑ k ∈ Icc 1 n, Mertens.notPrimeVonMangoldt k := by
      apply mul_le_mul_of_nonneg_left _ hfactor
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rw [Finset.mem_Ioc] at hk
        rw [Finset.mem_Icc]
        constructor <;> omega
      · intro k hk hnot
        exact notPrimeVonMangoldt_nonneg k
    _ = (Real.sqrt 2 / Real.sqrt n) *
        (Chebyshev.psi n - Chebyshev.theta n) := by
      congr 1
      rw [← Mertens.sum_notPrimeVonMangoldt]
      rw [show Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) by
        ext k
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega]
      rw [Finset.sum_insert (by simp), show Mertens.notPrimeVonMangoldt 0 = 0 by
        simp [Mertens.notPrimeVonMangoldt]]
      ring_nf
    _ ≤ (Real.sqrt 2 / Real.sqrt n) *
        (2 * Real.sqrt n * Real.log n) := by
      exact mul_le_mul_of_nonneg_left
        (Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)) hfactor
    _ = 2 * Real.sqrt 2 * Real.log n := by
      field_simp [hsqrtn.ne']

/-- The repeated-prime contribution is below every fixed positive power, with an explicit
constant. -/
theorem dyadicWeightedHigherPrimePowerWindow_le_subpower
    {n : ℕ} (hn : 1 ≤ n) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    dyadicWeightedHigherPrimePowerWindow n ≤
      (2 * Real.sqrt 2 / epsilon) * (n : ℝ) ^ epsilon := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htail := dyadicWeightedHigherPrimePowerWindow_le_log hn
  have hlog := Mertens.log_le_rpow hnR hepsilon
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  calc
    dyadicWeightedHigherPrimePowerWindow n ≤
        2 * Real.sqrt 2 * Real.log n := htail
    _ ≤ 2 * Real.sqrt 2 * ((1 / epsilon) * (n : ℝ) ^ epsilon) := by
      exact mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num) hsqrt)
    _ = (2 * Real.sqrt 2 / epsilon) * (n : ℝ) ^ epsilon := by ring_nf

/-- Removing the nonnegative proper-prime-power channel can only decrease the window. -/
theorem dyadicWeightedPrimeOnlyWindow_le_window (n : ℕ) :
    dyadicWeightedPrimeOnlyWindow n ≤ dyadicWeightedPrimeWindow n := by
  rw [dyadicWeightedPrimeWindow_eq_primeOnly_add_higherPrimePower]
  linarith [dyadicWeightedHigherPrimePowerWindow_nonneg n]

/-- A prime-only estimate lifts to the von Mangoldt estimate after adding the explicit subpower
cost of the repeated-prime channel. -/
theorem dyadicWeightedPrimeWindow_upper_of_primeOnlyWindow_upper
    {n : ℕ} (hn : 1 ≤ n) {epsilon C : ℝ} (hepsilon : 0 < epsilon)
    (hprime : dyadicWeightedPrimeOnlyWindow n ≤
      2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
        C * (n : ℝ) ^ epsilon) :
    dyadicWeightedPrimeWindow n ≤
      2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
        (C + 2 * Real.sqrt 2 / epsilon) * (n : ℝ) ^ epsilon := by
  rw [dyadicWeightedPrimeWindow_eq_primeOnly_add_higherPrimePower]
  have htail := dyadicWeightedHigherPrimePowerWindow_le_subpower hn hepsilon
  linarith

/-- **Prime-only equivalence.**  The all-epsilon RH-bearing estimate is unchanged after all
proper prime powers are removed. -/
theorem dyadicWeightedPrimeWindowSubpowerUpper_iff_primeOnly
    {N : ℕ} (hN : 1 ≤ N) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        dyadicWeightedPrimeWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            C * (n : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        dyadicWeightedPrimeOnlyWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            C * (n : ℝ) ^ epsilon) := by
  constructor
  · intro hfull epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hfull epsilon hepsilon
    exact ⟨C, hC, fun n hn =>
      (dyadicWeightedPrimeOnlyWindow_le_window n).trans (htail n hn)⟩
  · intro hprime epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hprime epsilon hepsilon
    let D : ℝ := C + 2 * Real.sqrt 2 / epsilon
    have hD : 0 ≤ D := by
      dsimp only [D]
      positivity
    refine ⟨D, hD, fun n hn => ?_⟩
    exact dyadicWeightedPrimeWindow_upper_of_primeOnlyWindow_upper
      (hN.trans hn) hepsilon (htail n hn)

/-- Direct source-facing RH theorem with only genuine prime values in the hypothesis. -/
theorem riemannHypothesis_of_eventually_dyadicWeightedPrimeOnlyWindow_upper
    {N : ℕ} (hN : 1 ≤ N)
    (hprime : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        dyadicWeightedPrimeOnlyWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            C * (n : ℝ) ^ epsilon) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_upper
  exact (dyadicWeightedPrimeWindowSubpowerUpper_iff_primeOnly hN).mpr hprime

/-- Prime coefficient whose cumulative sum is Chebyshev's theta function. -/
def criticalThetaCoefficient (k : ℕ) : ℝ :=
  if k.Prime then Real.log k else 0

/-- The prime coefficient recovers the exact source-defined theta value at every real cutoff. -/
theorem criticalCumulative_thetaCoefficient (x : ℝ) :
    criticalCumulative criticalThetaCoefficient x = Chebyshev.theta x := by
  rw [criticalCumulative, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  simp [criticalThetaCoefficient]

/-- Its critical Mellin error is literally `theta(x) - x`. -/
theorem criticalMellinError_thetaCoefficient (x : ℝ) :
    criticalMellinError criticalThetaCoefficient x = Chebyshev.theta x - x := by
  rw [criticalMellinError, criticalCumulative_thetaCoefficient]

/-- The prime-only window in the critical real-power convention used by Abel summation. -/
theorem dyadicWeightedPrimeOnlyWindow_eq_criticalThetaFloorSum (n : ℕ) :
    dyadicWeightedPrimeOnlyWindow n =
      ∑ k ∈ Ioc (n / 2) n,
        ((k : ℝ) ^ (-1 / 2 : ℝ)) * criticalThetaCoefficient k := by
  rw [dyadicWeightedPrimeOnlyWindow, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hp : k.Prime
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast hp.pos
    simp only [hp, if_true, criticalThetaCoefficient]
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hkpos.le]
    ring_nf
  · simp [hp, criticalThetaCoefficient]

/-- Endpoint-plus-primitive increment of the prime-only Chebyshev error `theta(x) - x` across the
dyadic interval. -/
def dyadicCriticalThetaMellinErrorIncrement (n : ℕ) : ℝ :=
  criticalMellinError criticalThetaCoefficient n / Real.sqrt n -
    criticalMellinError criticalThetaCoefficient ((n : ℝ) / 2) /
      Real.sqrt ((n : ℝ) / 2) +
    (1 / 2 : ℝ) *
      ((∫ t in Set.Ioc (1 : ℝ) n,
          criticalMellinError criticalThetaCoefficient t * t ^ (-3 / 2 : ℝ)) -
        ∫ t in Set.Ioc (1 : ℝ) ((n : ℝ) / 2),
          criticalMellinError criticalThetaCoefficient t * t ^ (-3 / 2 : ℝ))

/-- **Prime-only Abel value relation.**  The dyadic prime sum is its exact square-root main term
plus one endpoint-and-primitive increment of `theta(x) - x`. -/
theorem dyadicWeightedPrimeOnlyWindow_eq_main_add_thetaErrorIncrement
    {n : ℕ} (hn : 2 ≤ n) :
    dyadicWeightedPrimeOnlyWindow n =
      2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
        dyadicCriticalThetaMellinErrorIncrement n := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hhalf : (1 : ℝ) ≤ (n : ℝ) / 2 := by linarith
  have hc0 : criticalThetaCoefficient 0 = 0 := by
    simp [criticalThetaCoefficient]
  have hfull := criticalMellinError_identity criticalThetaCoefficient hc0
    (n : ℝ) (by linarith : (1 : ℝ) ≤ n)
  have hlow := criticalMellinError_identity criticalThetaCoefficient hc0
    ((n : ℝ) / 2) hhalf
  rw [Nat.floor_natCast] at hfull
  have hfloor : ⌊(n : ℝ) / 2⌋₊ = n / 2 := by
    simpa using (Nat.floor_div_eq_div (K := ℝ) n 2)
  rw [hfloor] at hlow
  have hwindow :
      (∑ k ∈ Ioc (n / 2) n,
          ((k : ℝ) ^ (-1 / 2 : ℝ)) * criticalThetaCoefficient k) =
        (∑ k ∈ Icc 0 n,
          ((k : ℝ) ^ (-1 / 2 : ℝ)) * criticalThetaCoefficient k) -
        ∑ k ∈ Icc 0 (n / 2),
          ((k : ℝ) ^ (-1 / 2 : ℝ)) * criticalThetaCoefficient k := by
    let f : ℕ → ℝ := fun k =>
      ((k : ℝ) ^ (-1 / 2 : ℝ)) * criticalThetaCoefficient k
    have hIcc : ∀ m : ℕ, Icc 0 m = range (m + 1) := by
      intro m
      ext k
      simp only [mem_Icc, zero_le, true_and, mem_range]
      omega
    have hIoc : Ioc (n / 2) n = Ico (n / 2 + 1) (n + 1) := by
      ext k
      simp only [mem_Ioc, mem_Ico]
      omega
    change (∑ k ∈ Ioc (n / 2) n, f k) =
      (∑ k ∈ Icc 0 n, f k) - ∑ k ∈ Icc 0 (n / 2), f k
    rw [hIcc, hIcc, hIoc, Finset.sum_Ico_eq_sub f (by omega)]
  rw [dyadicWeightedPrimeOnlyWindow_eq_criticalThetaFloorSum, hwindow,
    hfull, hlow, dyadicCriticalThetaMellinErrorIncrement,
    Real.sqrt_div (Nat.cast_nonneg n)]
  ring_nf

/-- The prime-only upper bound is pointwise equivalent to the subpower upper bound for the theta
error increment. -/
theorem dyadicWeightedPrimeOnlyWindow_upper_iff_thetaErrorIncrement
    {n : ℕ} (hn : 2 ≤ n) (C epsilon : ℝ) :
    dyadicWeightedPrimeOnlyWindow n ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n + C * (n : ℝ) ^ epsilon ↔
      dyadicCriticalThetaMellinErrorIncrement n ≤ C * (n : ℝ) ^ epsilon := by
  rw [dyadicWeightedPrimeOnlyWindow_eq_main_add_thetaErrorIncrement hn]
  constructor <;> intro h <;> linarith

/-- **All-epsilon theta-error reduction.**  From any cutoff at least two, the requested subpower
upper estimate for the full von Mangoldt window is exactly equivalent to the same one-sided
subpower estimate for the endpoint-and-primitive increment of `theta(x) - x`.  Proper prime powers
have already been absorbed at logarithmic cost. -/
theorem dyadicWeightedPrimeWindowSubpowerUpper_iff_thetaErrorIncrement
    {N : ℕ} (hN : 2 ≤ N) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        dyadicWeightedPrimeWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            C * (n : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        dyadicCriticalThetaMellinErrorIncrement n ≤
          C * (n : ℝ) ^ epsilon) := by
  rw [dyadicWeightedPrimeWindowSubpowerUpper_iff_primeOnly (by omega : 1 ≤ N)]
  constructor
  · intro hprime epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hprime epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    exact (dyadicWeightedPrimeOnlyWindow_upper_iff_thetaErrorIncrement
      (hN.trans hn) C epsilon).mp (htail n hn)
  · intro htheta epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := htheta epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    exact (dyadicWeightedPrimeOnlyWindow_upper_iff_thetaErrorIncrement
      (hN.trans hn) C epsilon).mpr (htail n hn)

/-- Direct RH theorem with the remaining hypothesis expressed only through the one-sided dyadic
increment of the prime Chebyshev error `theta(x) - x`. -/
theorem riemannHypothesis_of_eventually_dyadicCriticalThetaMellinErrorIncrement_upper
    {N : ℕ} (hN : 2 ≤ N)
    (htheta : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        dyadicCriticalThetaMellinErrorIncrement n ≤
          C * (n : ℝ) ^ epsilon) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_upper
  exact (dyadicWeightedPrimeWindowSubpowerUpper_iff_thetaErrorIncrement hN).mpr htheta

end RHTower
