import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusGradientCoercivityAndRenormalizedDefect
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ComplementaryQuotientAndSecondOctaveLaw

/-!
# Cofinal linear-window Möbius energy and defect bounds

Complementary quotient compression bounds the literal truncated Möbius source by the
number of quotient bands: `|s_N(k)| <= B` when `1 <= k <= (B+1)N`, for `N,B >= 1`.
Consequently `E_N(M) <= 4 B^2 M` and `|R_N(M)| <= 2 B^2 M` whenever the final
endpoint stays in that window.

Together with odd-squarefree edge coercivity, every fixed linear window
`2N <= M <= A N`, `A >= 2`, eventually has the two-sided estimates
`(2/pi^2) N <= E_N(M) <= 4 A^3 N` and
`-2 A^3 N <= R_N(M) <= -N/(2*pi^2)`.
These bounds apply to the actual arithmetic source with no assumed receiver budget.
They settle its order on each fixed linear window; constants are not claimed sharp,
and the upper bounds do not remain uniform when `A` tends to infinity.
-/

open Finset Filter
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators Topology


namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- Complementary quotients give a cutoff-independent pointwise bound on each fixed collection of bands. -/
theorem abs_sieveSeq_moebiusReal_le_band_width {N B k : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B) (hk : 1 ≤ k) (hhi : k ≤ (B + 1) * N) :
    |sieveSeq N moebiusReal k| ≤ (B : ℝ) := by
  classical
  by_cases hk1 : k = 1
  · subst k
    rw [sieveSeq_moebiusReal_eq_ite_of_le le_rfl hN, if_pos rfl, abs_one]
    exact_mod_cast hB
  rw [sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail N hk,
    sum_divisors_moebiusReal_eq_ite_one hk, if_neg hk1, zero_sub, abs_neg,
    complementaryQuotientTail_eq_sum_Icc_of_le_mul hhi]
  calc
    _ ≤ ∑ q ∈ (Finset.Icc 1 B).filter (fun q => q ∣ k ∧ N < k / q),
        |moebiusReal (k / q)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ (Finset.Icc 1 B).filter (fun q => q ∣ k ∧ N < k / q), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q _
      unfold moebiusReal
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k / q))
    _ = (((Finset.Icc 1 B).filter (fun q => q ∣ k ∧ N < k / q)).card : ℝ) := by simp
    _ ≤ ((Finset.Icc 1 B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun q => q ∣ k ∧ N < k / q) _)
    _ = (B : ℝ) := by simp

private theorem abs_moebius_gradient_le_twice_band_width {N B M k : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B) (hM : M + 1 ≤ (B + 1) * N)
    (hk : k ∈ Finset.Icc 1 M) :
    |sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k| ≤ 2 * B := by
  obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
  have h0 := abs_sieveSeq_moebiusReal_le_band_width hN hB hk1 (by omega : k ≤ (B + 1) * N)
  have h1 := abs_sieveSeq_moebiusReal_le_band_width hN hB (by omega : 1 ≤ k + 1)
    (by omega : k + 1 ≤ (B + 1) * N)
  rw [abs_le] at h0 h1 ⊢
  constructor <;> linarith

/-- The full unsigned Möbius gradient energy is at most linear in the horizon on every fixed collection of bands. -/
theorem moebius_gradient_energy_le_band_width {N B M : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B) (hM : M + 1 ≤ (B + 1) * N) :
    (∑ k ∈ Finset.Icc 1 M,
      (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) ^ 2) ≤
      4 * (B : ℝ) ^ 2 * M := by
  calc
    _ ≤ ∑ _k ∈ Finset.Icc 1 M, (4 * (B : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have h := pow_le_pow_left₀ (abs_nonneg _)
        (abs_moebius_gradient_le_twice_band_width hN hB hM hk) 2
      rw [sq_abs] at h
      nlinarith only [h]
    _ = _ := by simp; ring

/-- The renormalized defect has a two-sided finite arithmetic bound with no cancellation assumption. -/
theorem abs_moebiusRenormalizedDefect_le_band_width {N B M : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B) (hM : M + 1 ≤ (B + 1) * N) :
    |sieveRenormalizedPrefixDefect N M moebiusReal| ≤ 2 * (B : ℝ) ^ 2 * M := by
  rw [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 M,
        |sieveSeq N moebiusReal k *
          (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 M, (2 * (B : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
      have h0 := abs_sieveSeq_moebiusReal_le_band_width hN hB hk1
        (by omega : k ≤ (B + 1) * N)
      have h1 := abs_moebius_gradient_le_twice_band_width hN hB hM hk
      rw [abs_mul]
      calc
        _ ≤ (B : ℝ) * (2 * B) := mul_le_mul h0 h1 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ = _ := by simp; ring

/-- Every fixed linear trans-horizon window has gradient energy of linear order in the cutoff, uniformly throughout the window. -/
theorem eventually_moebius_gradient_energy_linear_window_bounds (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ M ∈ Finset.Icc (2 * N) ((r + 2) * N),
      (2 / Real.pi ^ 2) * N ≤
          (∑ k ∈ Finset.Icc 1 M,
            (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) ^ 2) ∧
        (∑ k ∈ Finset.Icc 1 M,
          (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) ^ 2) ≤
          4 * ((r : ℝ) + 2) ^ 3 * N := by
  filter_upwards [eventually_moebius_gradient_energy_ge_linear,
    eventually_ge_atTop (1 : ℕ)] with N hfloor hN
  intro M hM
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hM
  constructor
  · have h := hfloor M hlo
    have hc : squarefreeDensity / 3 = 2 / Real.pi ^ 2 := by
      rw [squarefreeDensity_eq]
      ring
    rwa [hc] at h
  · have hwindow : M + 1 ≤ (r + 2 + 1) * N := by nlinarith
    have h := moebius_gradient_energy_le_band_width hN (by omega : 1 ≤ r + 2) hwindow
    have hreal : (M : ℝ) ≤ ((r : ℝ) + 2) * N := by exact_mod_cast hhi
    calc
      _ ≤ 4 * ((r : ℝ) + 2) ^ 2 * M := by simpa only [Nat.cast_add, Nat.cast_ofNat] using h
      _ ≤ 4 * ((r : ℝ) + 2) ^ 2 * (((r : ℝ) + 2) * N) :=
        mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = _ := by ring

/-- Every fixed linear trans-horizon window has negative renormalized defect of linear order in the cutoff, uniformly throughout the window. -/
theorem eventually_moebiusRenormalizedDefect_linear_window_bounds (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ M ∈ Finset.Icc (2 * N) ((r + 2) * N),
      -(2 * ((r : ℝ) + 2) ^ 3 * N) ≤ sieveRenormalizedPrefixDefect N M moebiusReal ∧
        sieveRenormalizedPrefixDefect N M moebiusReal ≤ -(N : ℝ) / (2 * Real.pi ^ 2) := by
  filter_upwards [eventually_moebiusRenormalizedDefect_polynomial_cofinal_bound 0,
    eventually_ge_atTop (r + 2)] with N hnegative hN
  intro M hM
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hM
  constructor
  · have hwindow : M + 1 ≤ (r + 2 + 1) * N := by nlinarith
    have h := abs_moebiusRenormalizedDefect_le_band_width (by omega : 1 ≤ N)
      (by omega : 1 ≤ r + 2) hwindow
    have hreal : (M : ℝ) ≤ ((r : ℝ) + 2) * N := by exact_mod_cast hhi
    have hb : |sieveRenormalizedPrefixDefect N M moebiusReal| ≤
        2 * ((r : ℝ) + 2) ^ 3 * N := calc
      _ ≤ 2 * ((r : ℝ) + 2) ^ 2 * M := by simpa only [Nat.cast_add, Nat.cast_ofNat] using h
      _ ≤ 2 * ((r : ℝ) + 2) ^ 2 * (((r : ℝ) + 2) * N) :=
        mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = _ := by ring
    exact (abs_le.mp hb).1
  · apply hnegative M
    apply Finset.mem_Icc.mpr
    refine ⟨hlo, ?_⟩
    have hmul := Nat.mul_le_mul_right N hN
    simpa only [zero_add, pow_two] using hhi.trans hmul

end
end GaloisForLFunctions.BezoutValuationIncidence
