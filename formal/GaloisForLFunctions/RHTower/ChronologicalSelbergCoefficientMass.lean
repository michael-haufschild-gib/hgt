import GaloisForLFunctions.RHTower.Sieve.TotientCubicMean
import GaloisForLFunctions.RHTower.NicolasTotientLandau
import GaloisForLFunctions.RHTower.Sieve.SquarefreeGlobalCount
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDensityBound
import GaloisForLFunctions.BezoutValuationIncidence.ExactFinitePrefixDiscrepancyDualityAndReturnTimes

/-!
# Selberg energy controls mean absolute coefficient mass

Finite multiples inversion and a uniform cubic mean for `n / φ(n)` give
`(Σ_{d≤N} |c_d|)² ≤ 16384 N² Q_N(c)` for every real row. Thus a row with
an exact Möbius prefix of fixed positive relative length cannot have vanishing
Selberg energy. The estimate imposes no coefficient bound or harmonic condition.

This concerns the positive Selberg diagonal. It does not bound chronological
error: the signed fractional-part defect is a separate term in that error.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The inverse multiples transform has uniformly bounded weighted total mass. -/
theorem sum_sigma_sq_div_totient_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((sigma 1 n : ℕ) : ℝ)^2 / (Nat.totient n : ℝ) ≤
      16384 * (N : ℝ)^2 := by
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      ((sigma 1 n : ℕ) : ℝ)^2 / (Nat.totient n : ℝ) ≤
        (N : ℝ) * ((n : ℝ) / (Nat.totient n : ℝ))^3 := by
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hφ : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.mpr hnpos
    have hσ : ((sigma 1 n : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) / (Nat.totient n : ℝ)) := by
      have h := (div_le_iff₀ hnR).mp (sigma_div_le_div_totient hnpos.ne')
      nlinarith
    calc
      _ ≤ ((n : ℝ) * ((n : ℝ) / (Nat.totient n : ℝ)))^2 /
          (Nat.totient n : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hσ 2) hφ.le
      _ = (n : ℝ) * ((n : ℝ) / (Nat.totient n : ℝ))^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (by positivity)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (N : ℝ) * ((n : ℝ) / (Nat.totient n : ℝ))^3 :=
      Finset.sum_le_sum hterm
    _ = (N : ℝ) * ∑ n ∈ Icc 1 N, ((n : ℝ) / (Nat.totient n : ℝ))^3 :=
      (Finset.mul_sum ..).symm
    _ ≤ (N : ℝ) * (16384 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (Sieve.sum_totientRatio_cube_le N) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Absolute coefficient mass is bounded by the divisor-sum weighted inverse coordinates. -/
theorem sum_abs_coeff_le_sigma_selbergCoords (N : ℕ) (c : ℕ → ℝ) :
    ∑ d ∈ Icc 1 N, |c d| ≤
      ∑ e ∈ Icc 1 N, ((sigma 1 e : ℕ) : ℝ) * |selbergMultiplesCoord N c e| := by
  have hterm (d : ℕ) (hd : d ∈ Icc 1 N) :
      |c d| ≤ ∑ m ∈ Icc 1 (N / d), (d : ℝ) * |selbergMultiplesCoord N c (d * m)| := by
    rw [← ramanujan_inverse_selbergCoords_eq N c d hd]
    unfold pmRamanujanResidueCoeff
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
    calc
      _ ≤ (d : ℝ) * ∑ m ∈ Icc 1 (N / d),
          |(moebius m : ℝ) * selbergMultiplesCoord N c (d * m)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg d)
      _ = ∑ m ∈ Icc 1 (N / d),
          (d : ℝ) * |(moebius m : ℝ) * selbergMultiplesCoord N c (d * m)| :=
        Finset.mul_sum ..
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m hm
        rw [abs_mul]
        have hμ : |(moebius m : ℝ)| ≤ 1 := by
          rcases moebius_eq_or m with h | h | h <;> simp [h]
        exact mul_le_mul_of_nonneg_left
          (by simpa using mul_le_mul_of_nonneg_right hμ
            (abs_nonneg (selbergMultiplesCoord N c (d * m)))) (Nat.cast_nonneg d)
  calc
    _ ≤ ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
        (d : ℝ) * |selbergMultiplesCoord N c (d * m)| := Finset.sum_le_sum hterm
    _ = ∑ e ∈ Icc 1 N, ∑ d ∈ e.divisors,
        (d : ℝ) * |selbergMultiplesCoord N c (d * (e / d))| :=
      (Sieve.sum_divisors_swap N (fun d m =>
        (d : ℝ) * |selbergMultiplesCoord N c (d * m)|)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      calc
        _ = ∑ d ∈ e.divisors, (d : ℝ) * |selbergMultiplesCoord N c e| :=
          Finset.sum_congr rfl fun d hd => by
            rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
        _ = (∑ d ∈ e.divisors, (d : ℝ)) * |selbergMultiplesCoord N c e| :=
          (Finset.sum_mul ..).symm
        _ = _ := by simp [sigma_apply]

/-- A cutoff-independent coercivity estimate for every real coefficient row. -/
theorem sum_abs_coeff_sq_le_selberg (N : ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, |c d|)^2 ≤
      16384 * (N : ℝ)^2 * selbergTotientDiagonalForm N c := by
  have hmass := sum_abs_coeff_le_sigma_selbergCoords N c
  have hcs : (∑ e ∈ Icc 1 N,
      ((sigma 1 e : ℕ) : ℝ) * |selbergMultiplesCoord N c e|)^2 ≤
      selbergTotientDiagonalForm N c *
        ∑ e ∈ Icc 1 N, ((sigma 1 e : ℕ) : ℝ)^2 / (Nat.totient e : ℝ) := by
    unfold selbergTotientDiagonalForm
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro e he
      exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    · intro e he
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    · intro e he
      have hφ : (Nat.totient e : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (Finset.mem_Icc.mp he).1).ne'
      apply le_of_eq
      rw [mul_pow, sq_abs]
      field_simp
  calc
    _ ≤ (∑ e ∈ Icc 1 N,
        ((sigma 1 e : ℕ) : ℝ) * |selbergMultiplesCoord N c e|)^2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun d _ => abs_nonneg (c d)) hmass 2
    _ ≤ _ := hcs
    _ ≤ selbergTotientDiagonalForm N c * (16384 * (N : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (sum_sigma_sq_div_totient_le N)
        (selbergTotientDiagonalForm_nonneg N c)
    _ = _ := by ring

/-- Nonzero mean coefficient mass requires nonzero Selberg energy. -/
theorem coefficient_density_sq_le_selberg {N : ℕ} (hN : 0 < N)
    (c : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmass : δ * (N : ℝ) ≤ ∑ d ∈ Icc 1 N, |c d|) :
    δ^2 ≤ 16384 * selbergTotientDiagonalForm N c := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := (pow_le_pow_left₀ (mul_nonneg hδ hN0.le) hmass 2).trans
    (sum_abs_coeff_sq_le_selberg N c)
  rw [mul_pow] at hs
  exact (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hN0)).mp (by nlinarith [hs])

/-- An explicit positive density of nonzero Möbius coefficients beyond a fixed threshold. -/
theorem quarter_le_moebius_coefficient_mass {M : ℕ} (hM : 1024 ≤ M) :
    (M : ℝ) / 4 ≤ ∑ d ∈ Icc 1 M, |(moebius d : ℝ)| := by
  have hMR : (1024 : ℝ) ≤ M := by exact_mod_cast hM
  have hroot : (32 : ℝ) ≤ Real.sqrt M :=
    (Real.le_sqrt (by norm_num) (Nat.cast_nonneg M)).mpr (by norm_num; exact hMR)
  have hroot0 := Real.sqrt_nonneg (M : ℝ)
  have hroot_sq := Real.sq_sqrt (Nat.cast_nonneg M)
  have hroot_mul := mul_le_mul_of_nonneg_right hroot hroot0
  have hcount := (abs_le.mp (Sieve.abs_sum_moebius_sq_Icc_sub_le M)).1
  have hdensity := mul_le_mul_of_nonneg_left Sieve.squarefreeDensity_ge (Nat.cast_nonneg M)
  have hsum : (∑ d ∈ Icc 1 M, (moebius d : ℝ)^2) =
      ∑ d ∈ Icc 1 M, |(moebius d : ℝ)| := by
    apply Finset.sum_congr rfl
    intro d hd
    rcases moebius_eq_or d with h | h | h <;> simp [h]
  rw [hsum] at hcount
  nlinarith

/-- Retaining an exact Möbius prefix has a quantitative Selberg-energy cost. -/
theorem moebius_prefix_mass_sq_le_selberg {M N : ℕ} (hM : 1024 ≤ M) (hMN : M ≤ N)
    (c : ℕ → ℝ) (hhead : ∀ d ∈ Icc 1 M, c d = (moebius d : ℝ)) :
    (M : ℝ)^2 ≤ 262144 * (N : ℝ)^2 * selbergTotientDiagonalForm N c := by
  have hsub : (Icc 1 M : Finset ℕ) ⊆ Icc 1 N := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans hMN⟩
  have hmass : (M : ℝ) / 4 ≤ ∑ d ∈ Icc 1 N, |c d| := by
    calc
      _ ≤ ∑ d ∈ Icc 1 M, |(moebius d : ℝ)| := quarter_le_moebius_coefficient_mass hM
      _ = ∑ d ∈ Icc 1 M, |c d| := Finset.sum_congr rfl fun d hd => by rw [hhead d hd]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => abs_nonneg (c d)
  have hs := (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (M : ℝ) / 4) hmass 2).trans
    (sum_abs_coeff_sq_le_selberg N c)
  nlinarith [hs]

/-- The half-prefix source family cannot simultaneously have vanishing Selberg diagonal. -/
theorem half_moebius_prefix_selberg_floor {N : ℕ} (hN : 3072 ≤ N)
    (c : ℕ → ℝ) (hhead : ∀ d ∈ Icc 1 (N / 2), c d = (moebius d : ℝ)) :
    (1 : ℝ) / 2359296 ≤ selbergTotientDiagonalForm N c := by
  have hM : 1024 ≤ N / 2 := by omega
  have hthird : N ≤ 3 * (N / 2) := by omega
  have hmass : (1 / 12 : ℝ) * (N : ℝ) ≤ ∑ d ∈ Icc 1 N, |c d| := by
    have hMR : (N : ℝ) ≤ 3 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hthird
    have hsub : (Icc 1 (N / 2) : Finset ℕ) ⊆ Icc 1 N := by
      intro d hd
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
        (Finset.mem_Icc.mp hd).2.trans (Nat.div_le_self N 2)⟩
    calc
      _ ≤ ((N / 2 : ℕ) : ℝ) / 4 := by linarith
      _ ≤ ∑ d ∈ Icc 1 (N / 2), |(moebius d : ℝ)| := quarter_le_moebius_coefficient_mass hM
      _ = ∑ d ∈ Icc 1 (N / 2), |c d| := Finset.sum_congr rfl fun d hd => by rw [hhead d hd]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => abs_nonneg (c d)
  have h := coefficient_density_sq_le_selberg (by omega : 0 < N) c
    (by norm_num : (0 : ℝ) ≤ 1 / 12) hmass
  norm_num at h ⊢
  linarith

end

end RHTower
