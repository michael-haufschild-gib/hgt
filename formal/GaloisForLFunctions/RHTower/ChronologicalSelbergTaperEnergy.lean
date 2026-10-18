import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusHarmonicDifference
import GaloisForLFunctions.RHTower.Sieve.SelbergWeightedConvolutionModel
import GaloisForLFunctions.RHTower.EulerDeletionAveragedDivisorCovariance
import GaloisForLFunctions.BiScaleUncertainty.SignedLcmFractionalDefectAndCompleteFibreCollapse

/-!
# Selberg energy of a moving logarithmic taper

The inner Möbius prefix may move arbitrarily close to the outer cutoff on the
logarithmic scale. The energy bound depends on `log (N / M)` rather than on
the individual logarithms. The two cutoffs are subtracted inside the exact
Euler-correction convolution before any absolute-value estimate.
-/

open Finset
open scoped BigOperators

namespace RHTower

open Sieve DeletionCutoffAverage DeletionAveragedDivisor
open GaloisForLFunctions.BiScaleUncertainty

noncomputable section

private theorem taper_eq_log_difference {M N d : ℕ}
    (hM : 1 ≤ M) (hMN : M < N) (hd : 0 < d) :
    taper M N d =
      (Real.log ((N : ℝ) / d) -
        if d ≤ M then Real.log ((M : ℝ) / d) else 0) /
          (Real.log N - Real.log M) := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  by_cases hdM : d ≤ M
  · rw [taper, max_eq_left hdM, if_pos hdM,
      Real.log_div hN0 hd0, Real.log_div hM0 hd0]
    congr 1
    ring
  · rw [taper, max_eq_right (le_of_not_ge hdM), if_neg hdM,
      Real.log_div hN0 hd0, sub_zero]

/-- The finite Möbius transform of the taper is the difference of the two
logarithmic Möbius cutoffs, with their common normalization. -/
theorem selbergMoebiusWeightedSum_taper {M N q : ℕ}
    (hM : 1 ≤ M) (hMN : M < N) (hq : 0 < q) :
    selbergMoebiusWeightedSum (taper M N) N q =
      (coprimeLogMoebius 1 ((N : ℝ) / q) - coprimeLogMoebius 1 ((M : ℝ) / q)) /
        (Real.log N - Real.log M) := by
  have hfilter : (Finset.Icc 1 (N / q)).filter (fun u : ℕ => q * u ≤ M) =
      Finset.Icc 1 (M / q) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hu, hqu⟩
      exact ⟨hu.1, (Nat.le_div_iff_mul_le hq).mpr (by simpa [Nat.mul_comm] using hqu)⟩
    · intro hu
      exact ⟨⟨hu.1, hu.2.trans (Nat.div_le_div_right hMN.le)⟩,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp hu.2⟩
  have hinner :
      (∑ u ∈ Finset.Icc 1 (N / q), selbergMoebiusReciprocalCoeff u *
        (if q * u ≤ M then Real.log ((M : ℝ) / (q * u : ℕ)) else 0)) =
      coprimeLogMoebius 1 ((M : ℝ) / q) := by
    rw [coprimeLogMoebius_one_nat_ratio M q hq, ← hfilter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp
  calc
    selbergMoebiusWeightedSum (taper M N) N q =
        ((∑ u ∈ Finset.Icc 1 (N / q), selbergMoebiusReciprocalCoeff u *
          Real.log ((N : ℝ) / (q * u : ℕ))) -
        (∑ u ∈ Finset.Icc 1 (N / q), selbergMoebiusReciprocalCoeff u *
          (if q * u ≤ M then Real.log ((M : ℝ) / (q * u : ℕ)) else 0))) /
            (Real.log N - Real.log M) := by
      rw [selbergMoebiusWeightedSum, ← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u hu
      rw [taper_eq_log_difference hM hMN (Nat.mul_pos hq (Finset.mem_Icc.mp hu).1)]
      ring
    _ = _ := by rw [hinner, ← coprimeLogMoebius_one_nat_ratio N q hq]

/-- The ordinary Möbius/gcd kernel is exactly the Selberg form of a weighted
Möbius row; no coefficient-budget assumption enters this identity. -/
theorem selbergTotientDiagonalForm_moebius_mul_weight (N : ℕ) (w : ℕ → ℝ) :
    selbergTotientDiagonalForm N (fun d => (ArithmeticFunction.moebius d : ℝ) * w d) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        selbergOriginalCoeff m n * (w m * w n) := by
  rw [← sum_div_lcm_eq_selbergTotientDiagonalForm, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hm0 : m ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hm).1
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hlR : (Nat.lcm m n : ℝ) ≠ 0 := by exact_mod_cast Nat.lcm_ne_zero hm0 hn0
  have hprod : (Nat.gcd m n : ℝ) * (Nat.lcm m n : ℝ) = (m : ℝ) * n := by
    exact_mod_cast Nat.gcd_mul_lcm m n
  have hratio : (1 : ℝ) / Nat.lcm m n = (Nat.gcd m n : ℝ) / ((m : ℝ) * n) := by
    field_simp
    simpa [mul_comm] using hprod.symm
  rw [selbergOriginalCoeff]
  calc
    _ = ((ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ) *
        (w m * w n)) * (1 / (Nat.lcm m n : ℝ)) := by ring
    _ = _ := by rw [hratio]; ring

private theorem exists_taper_transform_harmonic_energy_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N a L : ℕ, 1 ≤ M → M < N → 0 < a →
      (∑ d ∈ Finset.Icc 1 L,
        selbergMoebiusWeightedSum (taper M N) N (a * d) ^ 2 / d) ≤
        C * (1 + (Real.log N - Real.log M)) / (Real.log N - Real.log M) ^ 2 := by
  obtain ⟨C, hC, hbase⟩ := exists_sum_sq_coprimeLogMoebius_difference_div_le
  refine ⟨C, hC, fun M N a L hM hMN ha => ?_⟩
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hMNreal : (M : ℝ) ≤ N := by exact_mod_cast hMN.le
  have hscaled := hbase ((M : ℝ) / a) ((N : ℝ) / a) (div_pos hM0 ha0)
    (div_le_div_of_nonneg_right hMNreal ha0.le) L
  have hratio : ((N : ℝ) / a) / ((M : ℝ) / a) = (N : ℝ) / M := by
    field_simp
  rw [hratio, Real.log_div hN0.ne' hM0.ne'] at hscaled
  have heq :
      (∑ d ∈ Finset.Icc 1 L,
        selbergMoebiusWeightedSum (taper M N) N (a * d) ^ 2 / d) =
      (∑ d ∈ Finset.Icc 1 L,
        (coprimeLogMoebius 1 (((N : ℝ) / a) / d) -
          coprimeLogMoebius 1 (((M : ℝ) / a) / d)) ^ 2 / d) /
        (Real.log N - Real.log M) ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    rw [selbergMoebiusWeightedSum_taper hM hMN
      (Nat.mul_pos ha (Finset.mem_Icc.mp hd).1)]
    simp only [Nat.cast_mul, ← div_div, div_pow]
    ring
  rw [heq]
  exact div_le_div_of_nonneg_right hscaled (sq_nonneg _)

private theorem exists_abs_taper_principal_model_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N a b : ℕ, 1 ≤ M → M < N → 0 < a → 0 < b →
      |∑ d ∈ Finset.Icc 1 (min (N / a) (N / b)),
        selbergMoebiusWeightedSum (taper M N) N (a * d) *
          selbergMoebiusWeightedSum (taper M N) N (b * d) / d| ≤
        C * (1 + (Real.log N - Real.log M)) / (Real.log N - Real.log M) ^ 2 := by
  obtain ⟨C, hC, henergy⟩ := exists_taper_transform_harmonic_energy_le
  refine ⟨C, hC, fun M N a b hM hMN ha hb => ?_⟩
  let L := min (N / a) (N / b)
  let F := fun q => selbergMoebiusWeightedSum (taper M N) N q
  have hA := henergy M N a L hM hMN ha
  have hB := henergy M N b L hM hMN hb
  have hpoint : ∀ d ∈ Finset.Icc 1 L,
      |F (a * d) * F (b * d) / d| ≤
        (F (a * d) ^ 2 / d + F (b * d) ^ 2 / d) / 2 := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hs : 2 * |F (a * d) * F (b * d)| ≤ F (a * d) ^ 2 + F (b * d) ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|F (a * d)| - |F (b * d)|),
        sq_abs (F (a * d)), sq_abs (F (b * d))]
    have h := div_le_div_of_nonneg_right hs hd0.le
    rw [abs_div, abs_of_pos hd0]
    simp only [add_div, mul_div_assoc] at h
    linarith
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hsum
  have habs := Finset.abs_sum_le_sum_abs
    (fun d => F (a * d) * F (b * d) / d) (Finset.Icc 1 L)
  change |∑ d ∈ Finset.Icc 1 L, F (a * d) * F (b * d) / d| ≤ _
  change (∑ d ∈ Finset.Icc 1 L, F (a * d) ^ 2 / d) ≤ _ at hA
  change (∑ d ∈ Finset.Icc 1 L, F (b * d) ^ 2 / d) ≤ _ at hB
  linarith

/-- The existing logarithmic cutoff-average row has energy at most an absolute
constant divided by its logarithmic width, uniformly in both moving cutoffs. -/
theorem exists_selberg_arithmeticCoeff_le_inv_log_span :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M N : ℕ, 1 ≤ M → M < N →
      1 ≤ Real.log N - Real.log M →
      selbergTotientDiagonalForm N (arithmeticCoeff M N) ≤
        K / (Real.log N - Real.log M) := by
  obtain ⟨C, hC, hmodel⟩ := exists_abs_taper_principal_model_le
  have hsummable : Summable (fun p : ℕ × ℕ => |selbergEulerCorrectionCoeff p.1 p.2|) := by
    simpa [Real.norm_eq_abs] using summable_selbergEulerCorrectionCoeff.norm
  let D := ∑' p : ℕ × ℕ, |selbergEulerCorrectionCoeff p.1 p.2|
  have hD : 0 ≤ D := tsum_nonneg (fun _ => abs_nonneg _)
  refine ⟨2 * D * C, by positivity, fun M N hM hMN hH => ?_⟩
  let H := Real.log N - Real.log M
  let E := C * (1 + H) / H ^ 2
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have heq : selbergTotientDiagonalForm N (arithmeticCoeff M N) =
      selbergTotientDiagonalForm N
        (fun d => (ArithmeticFunction.moebius d : ℝ) * taper M N d) := by
    unfold selbergTotientDiagonalForm selbergMultiplesCoord
    apply Finset.sum_congr rfl
    intro e _
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    rw [arithmeticCoeff, if_pos (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2]
    ring
  rw [heq, selbergTotientDiagonalForm_moebius_mul_weight,
    selbergOriginalCoeff_weighted_eq_correction_harmonic_model]
  have hpoint : ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N,
      selbergEulerCorrectionCoeff a b *
        (∑ d ∈ Finset.Icc 1 (min (N / a) (N / b)),
          selbergMoebiusWeightedSum (taper M N) N (a * d) *
            selbergMoebiusWeightedSum (taper M N) N (b * d) / d) ≤
      |selbergEulerCorrectionCoeff a b| * E := by
    intro a ha b hb
    have h := hmodel M N a b hM hMN (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1
    calc
      _ ≤ |selbergEulerCorrectionCoeff a b *
          (∑ d ∈ Finset.Icc 1 (min (N / a) (N / b)),
            selbergMoebiusWeightedSum (taper M N) N (a * d) *
              selbergMoebiusWeightedSum (taper M N) N (b * d) / d)| := le_abs_self _
      _ ≤ _ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have hmass := hsummable.sum_le_tsum ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))
    (fun _ _ => abs_nonneg _)
  rw [Finset.sum_product] at hmass
  have hsum := Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (hpoint a ha))
  simp only [← Finset.sum_mul] at hsum
  have htotal : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      selbergEulerCorrectionCoeff a b *
        (∑ d ∈ Finset.Icc 1 (min (N / a) (N / b)),
          selbergMoebiusWeightedSum (taper M N) N (a * d) *
            selbergMoebiusWeightedSum (taper M N) N (b * d) / d)) ≤ D * E :=
    hsum.trans (mul_le_mul_of_nonneg_right hmass hE)
  have hscale : E ≤ 2 * C / H := by
    calc
      E ≤ C * (2 * H) / H ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : 1 + H ≤ 2 * H) hC)
          (sq_nonneg H)
      _ = _ := by field_simp
  exact htotal.trans (by
    have h := mul_le_mul_of_nonneg_left hscale hD
    convert h using 1; ring)

end

end RHTower
