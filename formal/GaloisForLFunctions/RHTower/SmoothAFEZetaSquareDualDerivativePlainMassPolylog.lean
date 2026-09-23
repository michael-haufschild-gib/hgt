import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativeDivisorSquareAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.CriticalDivisorAffineMeanSquare

/-!
# Polylogarithmic plain mass for the square-dual derivative

Splitting at the conductor and applying cumulative divisor-square bounds before pointwise
subpower absorption sharpens the plain coefficient mass from `N^(-399/200)` to
`(1 + log N)^(4 : ℕ) / N^(2 : ℕ)`.  The corresponding affine mean square retains the exact logarithms.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology Finset

namespace RHTower

private theorem dualDerivative_le_low_conductor_polylog
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        min
          (C * Y ^ (1 / 4 : ℝ) /
            (tau * (tau ^ (1 / 4 : ℝ)) ^ 2))
          (C * (1 + tau) / Y))
    {N m : ℕ} {tau : ℝ} (hN : 4 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N)
    (htau : tau ∈ Set.Icc (N : ℝ) (2 * N)) :
    ‖deriv (fun u : ℝ =>
        smoothAFEZetaSquareDualWeight u ((m : ℝ) * N)) tau‖ ≤
      C / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htaupos : 0 < tau := hNpos.trans_le htau.1
  have htau4 : 4 ≤ tau := (by exact_mod_cast hN : (4 : ℝ) ≤ N) |>.trans htau.1
  have hYpos : 0 < (m : ℝ) * N := mul_pos hmpos hNpos
  have hraw := hderiv htau4 hYpos
  have hYle : (m : ℝ) * N ≤ tau ^ 2 := by
    have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
    calc
      (m : ℝ) * N ≤ (N : ℝ) * N :=
        mul_le_mul_of_nonneg_right hmNR hNpos.le
      _ = (N : ℝ) ^ 2 := by ring
      _ ≤ tau ^ 2 := pow_le_pow_left₀ hNpos.le htau.1 2
  have hquarter : ((m : ℝ) * N) ^ (1 / 4 : ℝ) ≤
      (tau ^ (1 / 4 : ℝ)) ^ 2 := by
    calc
      ((m : ℝ) * N) ^ (1 / 4 : ℝ) ≤ (tau ^ 2) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hYpos.le hYle (by norm_num)
      _ = (tau ^ (1 / 4 : ℝ)) ^ 2 := by
        calc
          (tau ^ 2) ^ (1 / 4 : ℝ) = tau ^ ((2 : ℝ) * (1 / 4 : ℝ)) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul htaupos.le]
            norm_num
          _ = tau ^ ((1 / 4 : ℝ) * 2) := by ring_nf
          _ = (tau ^ (1 / 4 : ℝ)) ^ 2 := by
            rw [Real.rpow_mul htaupos.le]
            exact Real.rpow_natCast _ 2
  have hden : 0 < tau * (tau ^ (1 / 4 : ℝ)) ^ 2 := by positivity
  calc
    ‖deriv (fun u : ℝ =>
        smoothAFEZetaSquareDualWeight u ((m : ℝ) * N)) tau‖ ≤
        C * (((m : ℝ) * N) ^ (1 / 4 : ℝ)) /
          (tau * (tau ^ (1 / 4 : ℝ)) ^ 2) := hraw.trans (min_le_left _ _)
    _ ≤ C * (tau ^ (1 / 4 : ℝ)) ^ 2 /
          (tau * (tau ^ (1 / 4 : ℝ)) ^ 2) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hquarter hC) hden.le
    _ = C / tau := by
      have hq : 0 < (tau ^ (1 / 4 : ℝ)) ^ 2 := by positivity
      field_simp [hq.ne', htaupos.ne']
    _ ≤ C / (N : ℝ) := div_le_div_of_nonneg_left hC hNpos htau.1

private theorem dualDerivative_le_high_conductor_polylog
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        min
          (C * Y ^ (1 / 4 : ℝ) /
            (tau * (tau ^ (1 / 4 : ℝ)) ^ 2))
          (C * (1 + tau) / Y))
    {N m : ℕ} {tau : ℝ} (hN : 4 ≤ N) (hm : 1 ≤ m)
    (htau : tau ∈ Set.Icc (N : ℝ) (2 * N)) :
    ‖deriv (fun u : ℝ =>
        smoothAFEZetaSquareDualWeight u ((m : ℝ) * N)) tau‖ ≤
      3 * C / (m : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htau4 : 4 ≤ tau := (by exact_mod_cast hN : (4 : ℝ) ≤ N) |>.trans htau.1
  have hYpos : 0 < (m : ℝ) * N := mul_pos hmpos hNpos
  have hraw := hderiv htau4 hYpos
  have hratio : (1 + tau) / (N : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hNpos]
    nlinarith [htau.2]
  calc
    ‖deriv (fun u : ℝ =>
        smoothAFEZetaSquareDualWeight u ((m : ℝ) * N)) tau‖ ≤
        C * (1 + tau) / ((m : ℝ) * N) := hraw.trans (min_le_right _ _)
    _ = (C / (m : ℝ)) * ((1 + tau) / (N : ℝ)) := by
      field_simp [hmpos.ne', hNpos.ne']
    _ ≤ (C / (m : ℝ)) * 3 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 3 * C / (m : ℝ) := by ring

private theorem dualDerivativeCoefficient_sq_le_of_deriv
    {N n : ℕ} {r t D : ℝ}
    (hderiv : ‖deriv (fun u : ℝ =>
      smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * N)) r‖ ≤ D) :
    ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2 ≤
      (((n + 1).divisors.card : ℝ) ^ 2 / (n + 1 : ℝ)) * D ^ 2 := by
  have hmpos : (0 : ℝ) < n + 1 := by positivity
  rw [norm_smoothAFEZetaSquareDualDerivativeCoefficient]
  have hfac0 : 0 ≤ ((n + 1).divisors.card : ℝ) *
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    positivity
  have hnorm := mul_le_mul_of_nonneg_left hderiv hfac0
  have hsquare := pow_le_pow_left₀ (by positivity :
    0 ≤ ((n + 1).divisors.card : ℝ) * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
      ‖deriv (fun u : ℝ => smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * N)) r‖)
    hnorm 2
  calc
    (((n + 1).divisors.card : ℝ) * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
        ‖deriv (fun u : ℝ => smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * N)) r‖) ^ 2
        ≤ (((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * D) ^ 2 := hsquare
    _ = (((n + 1).divisors.card : ℝ) ^ 2 / (n + 1 : ℝ)) * D ^ 2 := by
      have hpow : ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (n + 1 : ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hmpos.le]
        rw [show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num,
          Real.rpow_neg_one]
        exact inv_eq_one_div _
      rw [mul_pow, mul_pow, hpow]
      ring

theorem exists_tsum_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_polylog :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N : ℕ} {r center : ℝ},
      4 ≤ N → r ∈ Set.Icc (N : ℝ) (2 * N) →
      (∑' n : ℕ,
        ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r center n‖ ^ 2) ≤
          K * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2 := by
  obtain ⟨C, hC, hderiv⟩ := exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_two_sided
  let K : ℝ := 289 * C ^ 2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro N r center hN hr
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hL1 : (1 : ℝ) ≤ 1 + Real.log (N : ℝ) := by
    have := Real.log_nonneg hNreal
    linarith
  have hL3le4 : (1 + Real.log (N : ℝ)) ^ 3 ≤
      (1 + Real.log (N : ℝ)) ^ 4 := pow_le_pow_right₀ hL1 (by omega)
  have hr4 : (4 : ℝ) ≤ r :=
    (by exact_mod_cast hN : (4 : ℝ) ≤ N) |>.trans hr.1
  obtain ⟨hplainSummable, _hweightedSummable⟩ :=
    summable_smoothAFEZetaSquareDualDerivativeCoefficient_masses
      (t := center) hr4 hNpos
  have hhead : ∑ n ∈ Finset.range N,
      ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r center n‖ ^ 2 ≤
        C ^ 2 * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2 := by
    have hpoint : ∀ n ∈ Finset.range N,
        ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r center n‖ ^ 2 ≤
          (C ^ 2 / (N : ℝ) ^ 2) *
            (((n + 1).divisors.card : ℝ) ^ 2 / (n + 1 : ℝ)) := by
      intro n hn
      have hmN : n + 1 ≤ N := by simpa using Finset.mem_range.mp hn
      have hd := dualDerivative_le_low_conductor_polylog hC hderiv hN
        (show 1 ≤ n + 1 by omega) hmN hr
      have hsq := dualDerivativeCoefficient_sq_le_of_deriv
        (N := N) (n := n) (r := r) (t := center)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hd)
      calc
        ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r center n‖ ^ 2 ≤
            (((n + 1).divisors.card : ℝ) ^ 2 / (n + 1 : ℝ)) *
              (C / (N : ℝ)) ^ 2 := hsq
        _ = (C ^ 2 / (N : ℝ) ^ 2) *
            (((n + 1).divisors.card : ℝ) ^ 2 / (n + 1 : ℝ)) := by ring
    calc
      ∑ n ∈ Finset.range N,
          ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r center n‖ ^ 2 ≤
          ∑ n ∈ Finset.range N, (C ^ 2 / (N : ℝ) ^ 2) *
            (((n + 1).divisors.card : ℝ) ^ 2 / (n + 1 : ℝ)) :=
        Finset.sum_le_sum hpoint
      _ = (C ^ 2 / (N : ℝ) ^ 2) *
          ∑ n ∈ Finset.range N,
            (((n + 1).divisors.card : ℝ) ^ 2 / (n + 1 : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ (C ^ 2 / (N : ℝ) ^ 2) *
          (1 + Real.log (N : ℝ)) ^ 4 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hmoment := Sieve.sum_card_divisors_sq_div_le_polylog N hN1
        have heq : ∑ n ∈ Finset.range N,
            (((n + 1).divisors.card : ℝ) ^ 2 / (n + 1 : ℝ)) =
            ∑ m ∈ Finset.Icc 1 N,
              ((m.divisors.card : ℝ) ^ 2 / (m : ℝ)) := by
          rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext m; simp]
          rw [Finset.sum_Ico_eq_sum_range]
          simp [add_comm]
        rw [heq]
        exact hmoment
      _ = C ^ 2 * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2 := by ring
  have htail : ∑' i : ℕ,
      ‖smoothAFEZetaSquareDualDerivativeCoefficient
        (N : ℝ) r center (i + N)‖ ^ 2 ≤
        288 * C ^ 2 * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2 := by
    let base : ℕ → ℝ := fun m =>
      ((m.divisors.card : ℝ) ^ 2) / (m : ℝ) ^ 3
    let shift : ℕ → ℕ := fun i => (i + N) + 1
    let Q : ℕ → ℝ := fun i => 9 * C ^ 2 * base (shift i)
    have hshift : Summable (fun i : ℕ =>
        ‖smoothAFEZetaSquareDualDerivativeCoefficient
          (N : ℝ) r center (i + N)‖ ^ 2) :=
      hplainSummable.comp_injective (fun a b hab => Nat.add_right_cancel hab)
    have hQ : Summable Q := by
      have hinj : Function.Injective shift := by
        intro a b hab
        dsimp only [shift] at hab
        exact Nat.add_right_cancel (Nat.add_right_cancel hab)
      exact (Sieve.summable_divisorSquare_div_cube.comp_injective hinj).mul_left _
    have hpoint : ∀ i : ℕ,
        ‖smoothAFEZetaSquareDualDerivativeCoefficient
          (N : ℝ) r center (i + N)‖ ^ 2 ≤ Q i := by
      intro i
      let m : ℕ := (i + N) + 1
      have hm : 1 ≤ m := by dsimp only [m]; omega
      have hd := dualDerivative_le_high_conductor_polylog hC hderiv hN hm hr
      have hsq := dualDerivativeCoefficient_sq_le_of_deriv
        (N := N) (n := i + N) (r := r) (t := center)
        (by simpa only [m, Nat.cast_add, Nat.cast_one] using hd)
      calc
        ‖smoothAFEZetaSquareDualDerivativeCoefficient
            (N : ℝ) r center (i + N)‖ ^ 2 ≤
            ((((i + N) + 1).divisors.card : ℝ) ^ 2 / ((i + N) + 1 : ℝ)) *
              (3 * C / ((i + N) + 1 : ℝ)) ^ 2 := by
          simpa only [Nat.cast_add, Nat.cast_one] using hsq
        _ = Q i := by
          dsimp only [Q, base, shift]
          norm_num [Nat.cast_add, Nat.cast_one]
          field_simp
          ring
    have hcompare := hshift.tsum_le_tsum hpoint hQ
    have hQsum : (∑' i : ℕ, Q i) =
        9 * C ^ 2 * (∑' i : ℕ, base (shift i)) := by
      dsimp only [Q]
      rw [tsum_mul_left]
    rw [hQsum] at hcompare
    have htailBase := Sieve.tsum_shift_divisorSquare_div_cube_le N hN1
    have htailShift : (∑' i : ℕ, base (shift i)) ≤
        32 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) ^ 2 := by
      convert htailBase using 1
      apply tsum_congr
      intro i
      dsimp only [base, shift]
      rw [show (i + N) + 1 = N + 1 + i by omega]
    calc
      ∑' i : ℕ,
          ‖smoothAFEZetaSquareDualDerivativeCoefficient
            (N : ℝ) r center (i + N)‖ ^ 2 ≤
          9 * C ^ 2 * (∑' i : ℕ, base (shift i)) := hcompare
      _ ≤ 9 * C ^ 2 *
          (32 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left htailShift (by positivity)
      _ ≤ 288 * C ^ 2 *
          (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2 := by
        calc
          9 * C ^ 2 *
              (32 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) ^ 2) =
              288 * C ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 /
                (N : ℝ) ^ 2 := by ring
          _ ≤ 288 * C ^ 2 * (1 + Real.log (N : ℝ)) ^ 4 /
                (N : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hL3le4 (by positivity)) (sq_nonneg _)
  have hsplit := hplainSummable.sum_add_tsum_nat_add N
  calc
    (∑' n : ℕ,
        ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r center n‖ ^ 2) =
      (∑ n ∈ Finset.range N,
        ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r center n‖ ^ 2) +
      ∑' i : ℕ,
        ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r center (i + N)‖ ^ 2 := by
      simpa using hsplit.symm
    _ ≤
        C ^ 2 * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2 +
          288 * C ^ 2 * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2 :=
      add_le_add hhead htail
    _ = K * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2 := by
      dsimp only [K]
      ring

theorem exists_integral_normSq_smoothAFEZetaSquareDualDerivativeLSeries_le_polylog :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
      ∀ {N : ℕ} {r center H : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N) → 1 ≤ H →
        (∫ y in Set.Icc (-H) H,
          ‖LSeries
            (smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
            ((y : ℝ) * I)‖ ^ 2) ≤
          5 * Real.pi * Real.exp 1 *
              (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
            (5 * Real.pi / 2) *
              (A * (1 + Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ 2) * H := by
  obtain ⟨A, hA, hplainMass⟩ :=
    exists_tsum_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_polylog
  obtain ⟨K, hK, hweightedMass⟩ :=
    exists_tsum_weighted_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_logCube
  refine ⟨A, K, hA, hK, ?_⟩
  intro N r center H hN hr hH
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hr4 : (4 : ℝ) ≤ r :=
    (by exact_mod_cast hN : (4 : ℝ) ≤ N) |>.trans hr.1
  obtain ⟨habs, hplain, hweighted⟩ :=
    summable_smoothAFEZetaSquareDualDerivativeNatCoefficient_affine_masses
      (center := center) hr4 hN0
  have hmv :=
    Sieve.integral_Icc_normSq_LSeries_le_general_affine_infinite
      (a := smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
      (smoothAFEZetaSquareDualDerivativeNatCoefficient_zero _ _ _) 0
      (by simpa using habs) (by simpa using hplain) (by simpa using hweighted) hH
  have hmv' :
      (∫ y in Set.Icc (-H) H,
        ‖LSeries
          (smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
          ((y : ℝ) * I)‖ ^ 2) ≤
        5 * Real.pi * Real.exp 1 *
            (∑' k : ℕ, (k : ℝ) *
              ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                (N : ℝ) r center k‖ ^ 2) +
          (5 * Real.pi / 2) *
            (∑' k : ℕ,
              ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                (N : ℝ) r center k‖ ^ 2) * H := by
    simpa using hmv
  have hp := hplainMass (center := center) hN hr
  have hw := hweightedMass (center := center) hN hr
  rw [tsum_norm_smoothAFEZetaSquareDualDerivativeNatCoefficient_sq_eq
    (center := center) hr4 hN0] at hmv'
  rw [tsum_weighted_norm_smoothAFEZetaSquareDualDerivativeNatCoefficient_sq_eq
    (center := center) hr4 hN0] at hmv'
  exact hmv'.trans (by gcongr)

end RHTower
