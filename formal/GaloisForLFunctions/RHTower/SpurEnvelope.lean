/-
R1 envelope layer.

`SpurCumulantBounds` proves the analytic bridge in two pieces: the log-cumulant
tail and the scalar exponential truncation error.  This module packages those
pieces into the single polynomial envelope consumed by the MWM R1 lane.
-/
import GaloisForLFunctions.RHTower.RangeArithmetic
import GaloisForLFunctions.RHTower.CoefficientTail
import GaloisForLFunctions.RHTower.SpurCumulantBounds

namespace RHTower

open Polynomial

noncomputable section

/-- Single-constant half-range R1 envelope.

If the log cumulant is truncated at order `n` with `n + 1 = P`, the product multiplier
and its finite polynomial approximation differ by a constant multiple of `j^(2P)/d^P`
on the half range `2*j <= d`. -/
theorem phi_product_multiplierTruncPoly_abs_bound_half_constant (P n : ℕ) {j d : ℕ}
    (hd : 0 < d) (hj : 1 ≤ j) (hhalf : 2 * j ≤ d) (hnP : n + 1 = P) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)| ≤
      (2 + (n : ℝ) ^ P / (P.factorial : ℝ)) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  have hbase := phi_product_multiplierTruncPoly_abs_bound_half_envelope P n hd hhalf
  have hdpow_pos : 0 < (d : ℝ) ^ P := by positivity
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hexp : n + 2 ≤ 2 * P := by omega
  have hpowj : (j : ℝ) ^ (n + 2) ≤ (j : ℝ) ^ (2 * P) := by
    exact pow_le_pow_right₀ hjR hexp
  have htail_div : (j : ℝ) ^ (n + 2) / (d : ℝ) ^ P ≤
      (j : ℝ) ^ (2 * P) / (d : ℝ) ^ P :=
    div_le_div_of_nonneg_right hpowj (le_of_lt hdpow_pos)
  have htailB : 2 * (j : ℝ) ^ (n + 2) / (d : ℝ) ^ (n + 1) ≤
      2 * ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
    rw [hnP]
    calc
      2 * (j : ℝ) ^ (n + 2) / (d : ℝ) ^ P
          = 2 * ((j : ℝ) ^ (n + 2) / (d : ℝ) ^ P) := by ring
      _ ≤ 2 * ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
          exact mul_le_mul_of_nonneg_left htail_div (by norm_num : (0 : ℝ) ≤ 2)
  have htrunc_eq :
      ((n : ℝ) * ((j : ℝ) ^ 2 / d)) ^ P / (P.factorial : ℝ) =
        ((n : ℝ) ^ P / (P.factorial : ℝ)) *
          ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
    rw [mul_pow, div_pow]
    rw [← pow_mul]
    ring
  calc
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)|
        ≤ 2 * (j : ℝ) ^ (n + 2) / (d : ℝ) ^ (n + 1) +
            ((n : ℝ) * ((j : ℝ) ^ 2 / d)) ^ P / (P.factorial : ℝ) := hbase
    _ ≤ 2 * ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) +
          ((n : ℝ) ^ P / (P.factorial : ℝ)) *
            ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
      exact add_le_add htailB (le_of_eq htrunc_eq)
    _ = (2 + (n : ℝ) ^ P / (P.factorial : ℝ)) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by ring

/-- R1's usual `n = P - 1` specialization of the single-constant envelope. -/
theorem phi_product_multiplierTruncPoly_abs_bound_half_order (P : ℕ) {j d : ℕ}
    (hd : 0 < d) (hj : 1 ≤ j) (hhalf : 2 * j ≤ d) (hP : 1 ≤ P) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        (multiplierTruncPoly P (P - 1) j).eval ((d : ℝ)⁻¹)| ≤
      (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ)) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  exact phi_product_multiplierTruncPoly_abs_bound_half_constant P (P - 1) hd hj hhalf (by omega)

/-- R1's single-constant envelope on the paper range `j^3 <= d^2`.

The hypothesis `j^3 <= d^2` is the arithmetic replacement for `j <= d^(2/3)`;
the small threshold `8 <= d` converts it to the half-range used by the log-tail
estimate. -/
theorem phi_product_multiplierTruncPoly_abs_bound_cube_square_order (P : ℕ) {j d : ℕ}
    (hd : 8 ≤ d) (hj : 1 ≤ j) (hjd : j ^ 3 ≤ d ^ 2) (hP : 1 ≤ P) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        (multiplierTruncPoly P (P - 1) j).eval ((d : ℝ)⁻¹)| ≤
      (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ)) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 8) hd
  have hhalf : 2 * j ≤ d := two_mul_le_of_cube_le_square hjd hd
  exact phi_product_multiplierTruncPoly_abs_bound_half_order P hdpos hj hhalf hP

/-- Coefficient-sum form of the half-range R1 envelope.

This rewrites the polynomial evaluation as an explicit finite sum of the coefficient
carrier `multiplierCoeff`; it is the form consumed by Lemma R's finite-order
coefficient bookkeeping. -/
theorem phi_product_multiplierCoeff_sum_abs_bound_half_constant (P n : ℕ) {j d : ℕ}
    (hd : 0 < d) (hj : 1 ≤ j) (hhalf : 2 * j ≤ d) (hnP : n + 1 = P) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        ∑ p ∈ Finset.range (P * n + 1),
          multiplierCoeff P n j p * ((d : ℝ)⁻¹) ^ p| ≤
      (2 + (n : ℝ) ^ P / (P.factorial : ℝ)) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  have h := phi_product_multiplierTruncPoly_abs_bound_half_constant P n hd hj hhalf hnP
  rw [eval_multiplierTruncPoly_coeff_sum P n j ((d : ℝ)⁻¹)] at h
  exact h

/-- Usual-order coefficient-sum form of R1 on the half range. -/
theorem phi_product_multiplierCoeff_sum_abs_bound_half_order (P : ℕ) {j d : ℕ}
    (hd : 0 < d) (hj : 1 ≤ j) (hhalf : 2 * j ≤ d) (hP : 1 ≤ P) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        ∑ p ∈ Finset.range (P * (P - 1) + 1),
          multiplierCoeff P (P - 1) j p * ((d : ℝ)⁻¹) ^ p| ≤
      (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ)) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  exact phi_product_multiplierCoeff_sum_abs_bound_half_constant P (P - 1) hd hj hhalf (by omega)

/-- Paper-range coefficient-sum form of R1.

This is the closest formal shape to doc 34's R1 statement currently exposed in Lean:
the actual multiplier is controlled by an explicit finite coefficient sum on
`j^3 <= d^2`. -/
theorem phi_product_multiplierCoeff_sum_abs_bound_cube_square_order (P : ℕ) {j d : ℕ}
    (hd : 8 ≤ d) (hj : 1 ≤ j) (hjd : j ^ 3 ≤ d ^ 2) (hP : 1 ≤ P) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        ∑ p ∈ Finset.range (P * (P - 1) + 1),
          multiplierCoeff P (P - 1) j p * ((d : ℝ)⁻¹) ^ p| ≤
      (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ)) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 8) hd
  have hhalf : 2 * j ≤ d := two_mul_le_of_cube_le_square hjd hd
  exact phi_product_multiplierCoeff_sum_abs_bound_half_order P hdpos hj hhalf hP

/-- R1 against the retained low-degree jet, with the discarded tail isolated as an exact
`T^P` factor.

The first term is the proven product-to-full-polynomial envelope.  The second term names
the remaining coefficient-tail task needed to turn the jet into the bare
`Σ_{p<P} e_p(j)/d^p` statement. -/
theorem phi_product_multiplierJet_abs_bound_with_tail_half_constant (P n : ℕ) {j d : ℕ}
    (hd : 0 < d) (hj : 1 ≤ j) (hhalf : 2 * j ≤ d) (hnP : n + 1 = P) :
    ∃ Q : ℝ[X],
      |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
          (multiplierJetPoly P n j).eval ((d : ℝ)⁻¹)| ≤
        (2 + (n : ℝ) ^ P / (P.factorial : ℝ)) *
          ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) +
        |((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹)| := by
  obtain ⟨Q, hQ⟩ := exists_eval_multiplierTailPoly P n j ((d : ℝ)⁻¹)
  refine ⟨Q, ?_⟩
  have hfull := phi_product_multiplierTruncPoly_abs_bound_half_constant P n hd hj hhalf hnP
  have htri : |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
          (multiplierJetPoly P n j).eval ((d : ℝ)⁻¹)| ≤
      |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
          (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)| +
        |((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹)| := by
    rw [hQ]
    calc
      |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
          (multiplierJetPoly P n j).eval ((d : ℝ)⁻¹)|
          = |((∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
              ((multiplierJetPoly P n j).eval ((d : ℝ)⁻¹) +
                ((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹))) +
              ((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹)| := by
                congr 1
                ring
      _ ≤ |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
              ((multiplierJetPoly P n j).eval ((d : ℝ)⁻¹) +
                ((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹))| +
            |((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹)| := abs_add_le _ _
  linarith

/-- Usual-order jet-tail split on the half range. -/
theorem phi_product_multiplierJet_abs_bound_with_tail_half_order (P : ℕ) {j d : ℕ}
    (hd : 0 < d) (hj : 1 ≤ j) (hhalf : 2 * j ≤ d) (hP : 1 ≤ P) :
    ∃ Q : ℝ[X],
      |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
          (multiplierJetPoly P (P - 1) j).eval ((d : ℝ)⁻¹)| ≤
        (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ)) *
          ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) +
        |((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹)| := by
  exact phi_product_multiplierJet_abs_bound_with_tail_half_constant P (P - 1) hd hj hhalf (by omega)

/-- Paper-range jet-tail split for R1. -/
theorem phi_product_multiplierJet_abs_bound_with_tail_cube_square_order (P : ℕ) {j d : ℕ}
    (hd : 8 ≤ d) (hj : 1 ≤ j) (hjd : j ^ 3 ≤ d ^ 2) (hP : 1 ≤ P) :
    ∃ Q : ℝ[X],
      |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
          (multiplierJetPoly P (P - 1) j).eval ((d : ℝ)⁻¹)| ≤
        (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ)) *
          ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) +
        |((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹)| := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 8) hd
  have hhalf : 2 * j ≤ d := two_mul_le_of_cube_le_square hjd hd
  exact phi_product_multiplierJet_abs_bound_with_tail_half_order P hdpos hj hhalf hP

/-- Paper-range low-sum form of R1 with the exact polynomial tail isolated.

This is the Lean-facing version of doc 34's `Σ_{p<P} e_p(j)/d^p` statement before
the final coefficient-tail estimate is supplied. -/
theorem phi_product_multiplierCoeff_low_sum_abs_bound_with_tail_cube_square_order
    (P : ℕ) {j d : ℕ} (hd : 8 ≤ d) (hj : 1 ≤ j) (hjd : j ^ 3 ≤ d ^ 2) (hP : 1 ≤ P) :
    ∃ Q : ℝ[X],
      |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
          ∑ p ∈ Finset.range P, multiplierCoeff P (P - 1) j p * ((d : ℝ)⁻¹) ^ p| ≤
        (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ)) *
          ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) +
        |((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹)| := by
  obtain ⟨Q, hQ⟩ := phi_product_multiplierJet_abs_bound_with_tail_cube_square_order P hd hj hjd hP
  refine ⟨Q, ?_⟩
  rw [eval_multiplierJetPoly] at hQ
  exact hQ

/-- Paper-range low-sum R1 once the coefficient-tail provider is supplied. -/
theorem phi_product_multiplierCoeff_low_sum_abs_bound_of_tail_bound_cube_square_order
    (K : ℝ) (P : ℕ) {j d : ℕ}
    (hd : 8 ≤ d) (hj : 1 ≤ j) (hjd : j ^ 3 ≤ d ^ 2) (hP : 1 ≤ P)
    (hTail : multiplierJetTailEvalBound K P (P - 1) j d) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        ∑ p ∈ Finset.range P, multiplierCoeff P (P - 1) j p * ((d : ℝ)⁻¹) ^ p| ≤
      (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ) + K) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 8) hd
  obtain ⟨Q, hQeq, hQtail⟩ :=
    tail_term_bound_of_multiplierJetTailEvalBound (K := K) (P := P)
      (n := P - 1) (j := j) (d := d) hdpos hTail
  have hfull := phi_product_multiplierTruncPoly_abs_bound_cube_square_order P hd hj hjd hP
  have hjet_eval : (multiplierJetPoly P (P - 1) j).eval ((d : ℝ)⁻¹) =
      ∑ p ∈ Finset.range P, multiplierCoeff P (P - 1) j p * ((d : ℝ)⁻¹) ^ p := by
    rw [eval_multiplierJetPoly]
  have htri : |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        ∑ p ∈ Finset.range P, multiplierCoeff P (P - 1) j p * ((d : ℝ)⁻¹) ^ p| ≤
      |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
          (multiplierTruncPoly P (P - 1) j).eval ((d : ℝ)⁻¹)| +
        |((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹)| := by
    rw [← hjet_eval]
    have hdecomp :
        (∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
            (multiplierJetPoly P (P - 1) j).eval ((d : ℝ)⁻¹) =
          ((∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
            (multiplierTruncPoly P (P - 1) j).eval ((d : ℝ)⁻¹)) +
            ((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹) := by
      rw [hQeq]
      ring
    rw [hdecomp]
    exact abs_add_le _ _
  have hsum := add_le_add hfull hQtail
  calc
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        ∑ p ∈ Finset.range P, multiplierCoeff P (P - 1) j p * ((d : ℝ)⁻¹) ^ p|
        ≤ |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
          (multiplierTruncPoly P (P - 1) j).eval ((d : ℝ)⁻¹)| +
        |((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹)| := htri
    _ ≤ (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ)) *
          ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) +
        K * ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := hsum
    _ = (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ) + K) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by ring

/-- Paper-range low-sum R1 from a concrete finite high-coefficient tail bound. -/
theorem phi_product_multiplierCoeff_low_sum_abs_bound_of_coeff_sum_bound_cube_square_order
    (K : ℝ) (P : ℕ) {j d : ℕ}
    (hd : 8 ≤ d) (hj : 1 ≤ j) (hjd : j ^ 3 ≤ d ^ 2) (hP : 1 ≤ P)
    (hCoeff :
      ∑ r ∈ Finset.range (P * (P - 1) + 1),
        |multiplierCoeff P (P - 1) j (P + r)| * |((d : ℝ)⁻¹)| ^ r ≤
          K * (j : ℝ) ^ (2 * P)) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        ∑ p ∈ Finset.range P, multiplierCoeff P (P - 1) j p * ((d : ℝ)⁻¹) ^ p| ≤
      (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ) + K) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  exact phi_product_multiplierCoeff_low_sum_abs_bound_of_tail_bound_cube_square_order K P
    hd hj hjd hP (multiplierJetTailEvalBound_of_coeff_sum_bound (K := K) P hCoeff)

/-- Paper-range low-sum R1 from the sharper cumulant-power high-tail provider. -/
theorem phi_product_multiplierCoeff_low_sum_abs_bound_of_cumulant_power_tail_bound_cube_square_order
    (K : ℝ) (P : ℕ) {j d : ℕ}
    (hd : 8 ≤ d) (hj : 1 ≤ j) (hjd : j ^ 3 ≤ d ^ 2) (hP : 1 ≤ P)
    (hPower : cumulantPowerTailCoeffBound K P j d) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        ∑ p ∈ Finset.range P, multiplierCoeff P (P - 1) j p * ((d : ℝ)⁻¹) ^ p| ≤
      (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ) + K) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  exact phi_product_multiplierCoeff_low_sum_abs_bound_of_tail_bound_cube_square_order K P
    hd hj hjd hP
      (multiplierJetTailEvalBound_of_cumulant_power_tail_bound (K := K) P hPower)

/-- Paper-range low-sum R1 with the high-tail provider discharged by an explicit
finite constant depending only on `P`. -/
theorem phi_product_multiplierCoeff_low_sum_abs_bound_explicit_cube_square_order
    (P : ℕ) {j d : ℕ}
    (hd : 8 ≤ d) (hj : 1 ≤ j) (hjd : j ^ 3 ≤ d ^ 2) (hP : 1 ≤ P) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        ∑ p ∈ Finset.range P, multiplierCoeff P (P - 1) j p * ((d : ℝ)⁻¹) ^ p| ≤
      (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ) +
          cumulantPowerTailConstant P) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  exact phi_product_multiplierCoeff_low_sum_abs_bound_of_tail_bound_cube_square_order
    (cumulantPowerTailConstant P) P hd hj hjd hP
    (multiplierJetTailEvalBound_explicit P hd hj hjd)

/-- Paper-range low-sum R1 from an unweighted high-coefficient tail bound. -/
theorem phi_product_multiplierCoeff_low_sum_abs_bound_of_coeff_abs_sum_bound_cube_square_order
    (K : ℝ) (P : ℕ) {j d : ℕ}
    (hd : 8 ≤ d) (hj : 1 ≤ j) (hjd : j ^ 3 ≤ d ^ 2) (hP : 1 ≤ P)
    (hCoeff :
      ∑ r ∈ Finset.range (P * (P - 1) + 1),
        |multiplierCoeff P (P - 1) j (P + r)| ≤ K * (j : ℝ) ^ (2 * P)) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        ∑ p ∈ Finset.range P, multiplierCoeff P (P - 1) j p * ((d : ℝ)⁻¹) ^ p| ≤
      (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ) + K) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 8) hd
  exact phi_product_multiplierCoeff_low_sum_abs_bound_of_tail_bound_cube_square_order K P
    hd hj hjd hP (multiplierJetTailEvalBound_of_coeff_abs_sum_bound (K := K) P hdpos hCoeff)

end

end RHTower
