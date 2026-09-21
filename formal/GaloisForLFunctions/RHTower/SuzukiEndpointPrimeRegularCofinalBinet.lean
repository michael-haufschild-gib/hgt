import GaloisForLFunctions.RHTower.SuzukiEndpointPrimeRegularAggregate
import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.PNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Cofinal endpoint Binet disposal for Suzuki's actual prime wall

The exact endpoint prime--regular cancellation has a Binet remainder.  This file proves that the
remainder is not an unresolved macroscopic source channel: uniformly over every finite literal
von-Mangoldt subsource and over the half-logarithmic moving endpoint window, it is
`O(N^(-3/4))` and hence vanishes cofinally.

No unsigned replacement is made inside the source sum.  Consequently the surviving endpoint
problem is precisely the Laplace codiagonal left by
`SuzukiEndpointPrimeRegularAggregate`, where prime--continuum cancellation remains RH-bearing.
-/

open Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

private theorem endpoint_prime_regular_error_le_mertens
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ) {q L T : ℝ}
    (hs : ∀ k ∈ s, 0 < k ∧ k ≤ N) (hT : 0 < T)
    (hqL : q ≤ 2 * L) (hTq : T ≤ Real.log (N : ℝ) - q) :
    |(∑ k ∈ s,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
          screwRegularKernel (Real.log (N : ℝ) - q)) -
      ∑ k ∈ s, ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2)| ≤
      ((Real.log 4 + 4) * N) *
        (Real.exp (-3 * Real.log (N : ℝ) + 5 * L) /
          (1 - Real.exp (-2 * T))) := by
  have hsum : (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) ≤
      (Real.log 4 + 4) * N := by
    calc
      (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) ≤
          ∑ k ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr (hs k hk).1, (hs k hk).2⟩
        · intro k _ _
          exact ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ _ := Mertens.sum_vonMangoldt_Icc_le N
  have hbase := abs_sum_endpoint_prime_regular_sub_laplace_le
    (s := s) (q := q) (L := L) (T := T) hN hT hqL hTq
  have hdenpos : 0 < 1 - Real.exp (-2 * T) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by linarith)
  exact hbase.trans (mul_le_mul_of_nonneg_right hsum
    (div_nonneg (Real.exp_pos _).le hdenpos.le))

/-- On the natural half-logarithmic endpoint window, the aggregate Binet remainder of every
literal finite von-Mangoldt subsource has the uniform `N^(-3/4)` bound. -/
theorem endpoint_prime_regular_window_error_le
    {N : ℕ} (hN : 2 ≤ N) (s : Finset ℕ) {q : ℝ}
    (hs : ∀ k ∈ s, 0 < k ∧ k ≤ N)
    (_hq0 : 0 ≤ q) (hq : q ≤ Real.log (N : ℝ) / 2) :
    |(∑ k ∈ s,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
          screwRegularKernel (Real.log (N : ℝ) - q)) -
      ∑ k ∈ s, ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2)| ≤
      2 * (Real.log 4 + 4) * (N : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega) hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hT : 0 < Real.log (N : ℝ) / 2 := by positivity
  have hqL : q ≤ 2 * (Real.log (N : ℝ) / 4) := by linarith
  have hTq : Real.log (N : ℝ) / 2 ≤ Real.log (N : ℝ) - q := by linarith
  have hsum : (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) ≤
      (Real.log 4 + 4) * N := by
    calc
      (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) ≤
          ∑ k ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr (hs k hk).1, (hs k hk).2⟩
        · intro k _ _
          exact ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ _ := Mertens.sum_vonMangoldt_Icc_le N
  have hbase := abs_sum_endpoint_prime_regular_sub_laplace_le
    (s := s) (q := q) (L := Real.log (N : ℝ) / 4)
    (T := Real.log (N : ℝ) / 2) (by omega) hT hqL hTq
  have hden : (1 / 2 : ℝ) ≤
      1 - Real.exp (-2 * (Real.log (N : ℝ) / 2)) := by
    rw [show -2 * (Real.log (N : ℝ) / 2) = -Real.log (N : ℝ) by ring,
      Real.exp_neg, Real.exp_log hNpos]
    rw [one_div]
    apply (le_sub_iff_add_le).mpr
    have hinv : 1 / (N : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hN)
    norm_num at hinv ⊢
    linarith
  have hdenpos : 0 < 1 - Real.exp (-2 * (Real.log (N : ℝ) / 2)) :=
    lt_of_lt_of_le (by norm_num) hden
  have hfactor_nonneg : 0 ≤
      Real.exp (-3 * Real.log (N : ℝ) + 5 * (Real.log (N : ℝ) / 4)) /
        (1 - Real.exp (-2 * (Real.log (N : ℝ) / 2))) := by positivity
  have hfactor :
      Real.exp (-3 * Real.log (N : ℝ) + 5 * (Real.log (N : ℝ) / 4)) /
        (1 - Real.exp (-2 * (Real.log (N : ℝ) / 2))) ≤
        2 * Real.exp (-7 * Real.log (N : ℝ) / 4) := by
    rw [show -3 * Real.log (N : ℝ) + 5 * (Real.log (N : ℝ) / 4) =
      -7 * Real.log (N : ℝ) / 4 by ring]
    apply (div_le_iff₀ hdenpos).mpr
    have hexp : 0 < Real.exp (-7 * Real.log (N : ℝ) / 4) := Real.exp_pos _
    nlinarith
  calc
    |(∑ k ∈ s,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
          screwRegularKernel (Real.log (N : ℝ) - q)) -
      ∑ k ∈ s, ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2)| ≤
        (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) *
          (Real.exp (-3 * Real.log (N : ℝ) + 5 * (Real.log (N : ℝ) / 4)) /
            (1 - Real.exp (-2 * (Real.log (N : ℝ) / 2)))) := hbase
    _ ≤ ((Real.log 4 + 4) * N) *
          (Real.exp (-3 * Real.log (N : ℝ) + 5 * (Real.log (N : ℝ) / 4)) /
            (1 - Real.exp (-2 * (Real.log (N : ℝ) / 2)))) :=
      mul_le_mul_of_nonneg_right hsum hfactor_nonneg
    _ ≤ ((Real.log 4 + 4) * N) *
          (2 * Real.exp (-7 * Real.log (N : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = 2 * (Real.log 4 + 4) * (N : ℝ) ^ (-(3 / 4 : ℝ)) := by
      have hpow : (N : ℝ) * Real.exp (-7 * Real.log (N : ℝ) / 4) =
          (N : ℝ) ^ (-(3 / 4 : ℝ)) := by
        rw [Real.rpow_def_of_pos hNpos]
        calc
          (N : ℝ) * Real.exp (-7 * Real.log (N : ℝ) / 4) =
              Real.exp (Real.log (N : ℝ)) *
                Real.exp (-7 * Real.log (N : ℝ) / 4) := by
                rw [Real.exp_log hNpos]
          _ = Real.exp (Real.log (N : ℝ) * (-(3 / 4 : ℝ))) := by
                rw [← Real.exp_add]
                congr 1
                ring
      rw [show ((Real.log 4 + 4) * (N : ℝ)) *
          (2 * Real.exp (-7 * Real.log (N : ℝ) / 4)) =
          2 * (Real.log 4 + 4) *
            ((N : ℝ) * Real.exp (-7 * Real.log (N : ℝ) / 4)) by ring, hpow]

/-- The explicit uniform endpoint Binet majorant tends to zero. -/
theorem tendsto_endpoint_prime_regular_window_majorant_zero :
    Tendsto (fun N : ℕ =>
      2 * (Real.log 4 + 4) * (N : ℝ) ^ (-(3 / 4 : ℝ))) atTop (nhds 0) := by
  have hreal := Real.tendsto_pow_log_div_pow_atTop (3 / 4 : ℝ) 0 (by norm_num)
  have hcomp := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hmul := hcomp.const_mul (2 * (Real.log 4 + 4))
  have heq : (fun N : ℕ =>
      2 * (Real.log 4 + 4) *
        ((fun x : ℝ => Real.log x ^ (0 : ℝ) / x ^ (3 / 4 : ℝ))
          ((N : ℝ)))) =ᶠ[atTop]
      fun N : ℕ => 2 * (Real.log 4 + 4) * (N : ℝ) ^ (-(3 / 4 : ℝ)) := by
    filter_upwards with N
    rw [Real.rpow_neg (Nat.cast_nonneg N)]
    simp only [Real.rpow_zero, one_div]
  simpa using hmul.congr' heq

/-- The aggregate endpoint Binet error vanishes uniformly on the half-log moving window, even
when the finite subsource is selected adversarially inside the actual aperture. -/
theorem eventually_endpoint_prime_regular_window_error_lt
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ (s : Finset ℕ) (q : ℝ),
      (∀ k ∈ s, 0 < k ∧ k ≤ N) →
      0 ≤ q → q ≤ Real.log (N : ℝ) / 2 →
      |(∑ k ∈ s,
          (ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
            screwRegularKernel (Real.log (N : ℝ) - q)) -
        ∑ k ∈ s, ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2)| < epsilon := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      2 * (Real.log 4 + 4) * (N : ℝ) ^ (-(3 / 4 : ℝ)) < epsilon :=
    (tendsto_order.1 tendsto_endpoint_prime_regular_window_majorant_zero).2 epsilon hepsilon
  filter_upwards [eventually_ge_atTop (2 : ℕ), hsmall] with N hN hbound
  intro s q hs hq0 hq
  exact (endpoint_prime_regular_window_error_le hN s hs hq0 hq).trans_lt hbound

/-- Enlarging the endpoint window to three quarters of logarithmic aperture still leaves a
vanishing uniform Binet error.  The exponent `-1/8` is the exact cost of this wider window under
the unconditional linear Mertens majorant. -/
theorem endpoint_prime_regular_threeQuarter_window_error_le
    {N : ℕ} (hN : 4 ≤ N) (s : Finset ℕ) {q : ℝ}
    (hs : ∀ k ∈ s, 0 < k ∧ k ≤ N)
    (_hq0 : 0 ≤ q) (hq : q ≤ 3 * Real.log (N : ℝ) / 4) :
    |(∑ k ∈ s,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
          screwRegularKernel (Real.log (N : ℝ) - q)) -
      ∑ k ∈ s, ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2)| ≤
      2 * (Real.log 4 + 4) * (N : ℝ) ^ (-(1 / 8 : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega) hN)
  have hT : 0 < Real.log (N : ℝ) / 4 := by
    have hNone : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact div_pos (Real.log_pos hNone) (by norm_num)
  have hqL : q ≤ 2 * (3 * Real.log (N : ℝ) / 8) := by linarith
  have hTq : Real.log (N : ℝ) / 4 ≤ Real.log (N : ℝ) - q := by linarith
  have hbase := endpoint_prime_regular_error_le_mertens
    (by omega) s hs hT hqL hTq
  have hsqrtSq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hsqrtNonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hfour : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrtTwo : (2 : ℝ) ≤ Real.sqrt (N : ℝ) := by nlinarith
  have hden : (1 / 2 : ℝ) ≤
      1 - Real.exp (-2 * (Real.log (N : ℝ) / 4)) := by
    have hsqrt : Real.sqrt (N : ℝ) = Real.exp (Real.log (N : ℝ) / 2) :=
      sqrt_eq_exp_log_div_two hNpos
    rw [show -2 * (Real.log (N : ℝ) / 4) = -Real.log (N : ℝ) / 2 by ring,
      show -Real.log (N : ℝ) / 2 = -(Real.log (N : ℝ) / 2) by ring,
      Real.exp_neg, ← hsqrt]
    rw [one_div]
    apply (le_sub_iff_add_le).mpr
    have hinv : 1 / Real.sqrt (N : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hsqrtTwo
    norm_num at hinv ⊢
    linarith
  have hdenpos : 0 < 1 - Real.exp (-2 * (Real.log (N : ℝ) / 4)) :=
    lt_of_lt_of_le (by norm_num) hden
  have hfactor :
      Real.exp (-3 * Real.log (N : ℝ) + 5 * (3 * Real.log (N : ℝ) / 8)) /
        (1 - Real.exp (-2 * (Real.log (N : ℝ) / 4))) ≤
        2 * Real.exp (-9 * Real.log (N : ℝ) / 8) := by
    rw [show -3 * Real.log (N : ℝ) + 5 * (3 * Real.log (N : ℝ) / 8) =
      -9 * Real.log (N : ℝ) / 8 by ring]
    apply (div_le_iff₀ hdenpos).mpr
    have hexp : 0 < Real.exp (-9 * Real.log (N : ℝ) / 8) := Real.exp_pos _
    nlinarith
  calc
    |(∑ k ∈ s,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
          screwRegularKernel (Real.log (N : ℝ) - q)) -
      ∑ k ∈ s, ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2)| ≤
        ((Real.log 4 + 4) * N) *
          (Real.exp (-3 * Real.log (N : ℝ) + 5 * (3 * Real.log (N : ℝ) / 8)) /
            (1 - Real.exp (-2 * (Real.log (N : ℝ) / 4)))) := hbase
    _ ≤ ((Real.log 4 + 4) * N) *
          (2 * Real.exp (-9 * Real.log (N : ℝ) / 8)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = 2 * (Real.log 4 + 4) * (N : ℝ) ^ (-(1 / 8 : ℝ)) := by
      have hpow : (N : ℝ) * Real.exp (-9 * Real.log (N : ℝ) / 8) =
          (N : ℝ) ^ (-(1 / 8 : ℝ)) := by
        rw [Real.rpow_def_of_pos hNpos]
        calc
          (N : ℝ) * Real.exp (-9 * Real.log (N : ℝ) / 8) =
              Real.exp (Real.log (N : ℝ)) *
                Real.exp (-9 * Real.log (N : ℝ) / 8) := by
                rw [Real.exp_log hNpos]
          _ = Real.exp (Real.log (N : ℝ) * (-(1 / 8 : ℝ))) := by
                rw [← Real.exp_add]
                congr 1
                ring
      rw [show ((Real.log 4 + 4) * (N : ℝ)) *
          (2 * Real.exp (-9 * Real.log (N : ℝ) / 8)) =
          2 * (Real.log 4 + 4) *
            ((N : ℝ) * Real.exp (-9 * Real.log (N : ℝ) / 8)) by ring, hpow]

/-- The three-quarter endpoint majorant still vanishes cofinally. -/
theorem tendsto_endpoint_prime_regular_threeQuarter_window_majorant_zero :
    Tendsto (fun N : ℕ =>
      2 * (Real.log 4 + 4) * (N : ℝ) ^ (-(1 / 8 : ℝ))) atTop (nhds 0) := by
  have hreal := Real.tendsto_pow_log_div_pow_atTop (1 / 8 : ℝ) 0 (by norm_num)
  have hcomp := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hmul := hcomp.const_mul (2 * (Real.log 4 + 4))
  have heq : (fun N : ℕ =>
      2 * (Real.log 4 + 4) *
        ((fun x : ℝ => Real.log x ^ (0 : ℝ) / x ^ (1 / 8 : ℝ))
          ((N : ℝ)))) =ᶠ[atTop]
      fun N : ℕ => 2 * (Real.log 4 + 4) * (N : ℝ) ^ (-(1 / 8 : ℝ)) := by
    filter_upwards with N
    rw [Real.rpow_neg (Nat.cast_nonneg N)]
    simp only [Real.rpow_zero, one_div]
  simpa using hmul.congr' heq

/-- Uniform cofinal disappearance of the Binet error on three quarters of the moving
logarithmic endpoint aperture. -/
theorem eventually_endpoint_prime_regular_threeQuarter_window_error_lt
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ (s : Finset ℕ) (q : ℝ),
      (∀ k ∈ s, 0 < k ∧ k ≤ N) →
      0 ≤ q → q ≤ 3 * Real.log (N : ℝ) / 4 →
      |(∑ k ∈ s,
          (ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
            screwRegularKernel (Real.log (N : ℝ) - q)) -
        ∑ k ∈ s, ArithmeticFunction.vonMangoldt k * Real.exp (-q / 2)| < epsilon := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      2 * (Real.log 4 + 4) * (N : ℝ) ^ (-(1 / 8 : ℝ)) < epsilon :=
    (tendsto_order.1 tendsto_endpoint_prime_regular_threeQuarter_window_majorant_zero).2
      epsilon hepsilon
  filter_upwards [eventually_ge_atTop (4 : ℕ), hsmall] with N hN hbound
  intro s q hs hq0 hq
  exact (endpoint_prime_regular_threeQuarter_window_error_le hN s hs hq0 hq).trans_lt hbound

end

end GaloisForLFunctions.RHTower
