import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.MixedPolarCancellation

/-!
# The polar channel on two-conductor top-band packets

The actual shell–pole coefficient is bilinear, with both mixed orientations
retained. On the span of the constant profile and one nonpolar Ramanujan
mode, removing the polar–polar entry leaves a bound independent of overlap.
-/

open MeasureTheory Finset
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
noncomputable section

theorem horizonDivisorCoefficient_linear (a b : ℕ → ℝ) (α β : ℝ) (N ℓ : ℕ) :
    horizonDivisorCoefficient (fun n => α * a n + β * b n) N ℓ =
      α * horizonDivisorCoefficient a N ℓ + β * horizonDivisorCoefficient b N ℓ := by
  unfold horizonDivisorCoefficient
  calc
    _ = ∑ d ∈ ℓ.divisors.filter (fun d => ℓ / d ≤ N),
        (α * ((ArithmeticFunction.vonMangoldt d : ℝ) * a (ℓ / d)) +
          β * ((ArithmeticFunction.vonMangoldt d : ℝ) * b (ℓ / d))) := by
      apply sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]

theorem shellCoefficientRow_linear (g : ℝ → ℝ) (a b : ℕ → ℝ) (α β : ℝ)
    (N : ℕ) (w : ℝ) (n : ℕ) :
    shellCoefficientRow g (fun k => α * a k + β * b k) N w n =
      α * shellCoefficientRow g a N w n + β * shellCoefficientRow g b N w n := by
  unfold shellCoefficientRow
  simp_rw [horizonDivisorCoefficient_linear]
  calc
    _ = ∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
        (α * (poleVector ℓ * horizonDivisorCoefficient a N ℓ *
          (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n))) +
        β * (poleVector ℓ * horizonDivisorCoefficient b N ℓ *
          (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)))) := by
      apply sum_congr rfl
      intro ℓ _
      ring
    _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]

theorem shellTopCoefficient_linear_left (g : ℝ → ℝ) (a b ψ : ℕ → ℝ)
    (α β : ℝ) (N : ℕ) (w : ℝ) :
    shellTopCoefficient g (fun n => α * a n + β * b n) ψ N w =
      α * shellTopCoefficient g a ψ N w + β * shellTopCoefficient g b ψ N w := by
  unfold shellTopCoefficient
  simp_rw [shellCoefficientRow_linear]
  calc
    _ = ∑ n ∈ topBand N w,
        (α * (poleVector n * ψ n * shellCoefficientRow g a N w n) +
          β * (poleVector n * ψ n * shellCoefficientRow g b N w n)) := by
      apply sum_congr rfl
      intro n _
      ring
    _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]

theorem shellTopCoefficient_linear_right (g : ℝ → ℝ) (a ψ χ : ℕ → ℝ)
    (α β : ℝ) (N : ℕ) (w : ℝ) :
    shellTopCoefficient g a (fun n => α * ψ n + β * χ n) N w =
      α * shellTopCoefficient g a ψ N w + β * shellTopCoefficient g a χ N w := by
  unfold shellTopCoefficient
  calc
    _ = ∑ n ∈ topBand N w,
        (α * (poleVector n * ψ n * shellCoefficientRow g a N w n) +
          β * (poleVector n * χ n * shellCoefficientRow g a N w n)) := by
      apply sum_congr rfl
      intro n _
      ring
    _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]

theorem jointTopCoefficient_linear_left (g : ℝ → ℝ) (a b ψ : ℕ → ℝ)
    (α β : ℝ) (N : ℕ) (w : ℝ) :
    jointTopCoefficient g (fun n => α * a n + β * b n) ψ N w =
      α * jointTopCoefficient g a ψ N w + β * jointTopCoefficient g b ψ N w := by
  simp only [jointTopCoefficient, shellTopCoefficient_linear_left,
    add_div, mul_div_assoc, sum_add_distrib, ← mul_sum]
  ring

theorem jointTopCoefficient_linear_right (g : ℝ → ℝ) (a ψ χ : ℕ → ℝ)
    (α β : ℝ) (N : ℕ) (w : ℝ) :
    jointTopCoefficient g a (fun n => α * ψ n + β * χ n) N w =
      α * jointTopCoefficient g a ψ N w + β * jointTopCoefficient g a χ N w := by
  simp only [jointTopCoefficient, shellTopCoefficient_linear_right,
    add_div, mul_div_assoc, sum_add_distrib, ← mul_sum]
  ring

/-- The nonsymmetric shell coefficient retains both mixed orientations. -/
theorem jointTopCoefficient_two_mode (g : ℝ → ℝ) (a b : ℕ → ℝ)
    (α β : ℝ) (N : ℕ) (w : ℝ) :
    jointTopCoefficient g (fun n => α * a n + β * b n)
        (fun n => α * a n + β * b n) N w - α ^ 2 * jointTopCoefficient g a a N w =
      α * β * (jointTopCoefficient g a b N w + jointTopCoefficient g b a N w) +
        β ^ 2 * jointTopCoefficient g b b N w := by
  rw [jointTopCoefficient_linear_left, jointTopCoefficient_linear_right,
    jointTopCoefficient_linear_right]
  ring

/-- Removing the polar entry leaves a logarithmically bounded two-conductor packet. -/
theorem exists_abs_ramanujan_packet_sub_polar_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ (α β c : ℝ) (N : ℕ),
      1 ≤ c → 8 ≤ N → 4 * c ≤ N →
      |jointTopCoefficient (atomDilate φ (c / N))
          (fun n => α + β * normalizedRamanujanMode m n)
          (fun n => α + β * normalizedRamanujanMode m n) N (c / N) -
        α ^ 2 * jointTopCoefficient (atomDilate φ (c / N)) (fun _ => 1) (fun _ => 1) N (c / N)| ≤
        K * m * (|α * β| * (2 * Real.sqrt (m.totient : ℝ) + ramanujanJetAmplitude m) +
          β ^ 2 * m.totient) * (∫ u, atomDilate φ (c / N) u ^ 2) * (1 + Real.log N) := by
  obtain ⟨K₁, hK₁, hperiodic⟩ := exists_abs_jointTopCoefficient_le_uniform_overlap hφ hsupp hM
  obtain ⟨K₂, hK₂, hmixed⟩ := exists_abs_ramanujan_polar_jointTopCoefficient_le hφ hsupp hM
  set K := max K₁ K₂
  have hK : 0 < K := hK₁.trans_le (le_max_left _ _)
  refine ⟨K, hK, fun m hm α β c N hc hN hNc => ?_⟩
  set g := atomDilate φ (c / N)
  set U := Real.sqrt (m.totient : ℝ)
  set V := ramanujanJetAmplitude m
  set G := ∫ u, g u ^ 2
  set L := 1 + Real.log N
  have hm0 : 0 < m := by omega
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hV : 0 ≤ V := by
    exact div_nonneg (add_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
      ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)
  have hG : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hL : 0 ≤ L := add_nonneg zero_le_one (Real.log_natCast_nonneg N)
  have hmode : ∀ n, |normalizedRamanujanMode m n| ≤ U :=
    SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hm0
  have h1 : |jointTopCoefficient g (fun _ => 1) (normalizedRamanujanMode m) N (c / N)| ≤
      K * m * U * G * L := by
    have h := hperiodic m (by omega) (fun _ => 1) (normalizedRamanujanMode m) 1 U
      (fun _ => by norm_num) (normalizedRamanujanMode_periodic hm0)
      (sum_range_normalizedRamanujanMode hm) hmode c N hc hN hNc
    simp only [mul_one] at h
    exact h.trans (by
      have h' := mul_le_mul_of_nonneg_right (le_max_left K₁ K₂)
        (show 0 ≤ (m : ℝ) * U * G * L by positivity)
      nlinarith only [h'])
  have h2 : |jointTopCoefficient g (normalizedRamanujanMode m) (fun _ => 1) N (c / N)| ≤
      K * m * (U + V) * G * L := by
    have h := hmixed m hm c N hc hN hNc
    exact h.trans (by
      have h' := mul_le_mul_of_nonneg_right (le_max_right K₁ K₂)
        (show 0 ≤ (m : ℝ) * (U + V) * G * L by positivity)
      nlinarith only [h'])
  have h3 : |jointTopCoefficient g (normalizedRamanujanMode m)
      (normalizedRamanujanMode m) N (c / N)| ≤ K * m * m.totient * G * L := by
    have h := hperiodic m (by omega) (normalizedRamanujanMode m) (normalizedRamanujanMode m)
      U U hmode (normalizedRamanujanMode_periodic hm0)
      (sum_range_normalizedRamanujanMode hm) hmode c N hc hN hNc
    have hUsq : U ^ 2 = (m.totient : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    have he : K₁ * U * m * U * G * L = K₁ * m * m.totient * G * L := by
      calc
        _ = K₁ * m * U ^ 2 * G * L := by ring
        _ = _ := by rw [hUsq]
    rw [he] at h
    exact h.trans (by
      have h' := mul_le_mul_of_nonneg_right (le_max_left K₁ K₂)
        (show 0 ≤ (m : ℝ) * m.totient * G * L by positivity)
      nlinarith only [h'])
  have hexp := jointTopCoefficient_two_mode g (fun _ => 1) (normalizedRamanujanMode m) α β N (c / N)
  simp only [mul_one] at hexp
  rw [hexp]
  calc
    _ ≤ |α * β| * (|jointTopCoefficient g (fun _ => 1) (normalizedRamanujanMode m) N (c / N)| +
        |jointTopCoefficient g (normalizedRamanujanMode m) (fun _ => 1) N (c / N)|) +
        β ^ 2 * |jointTopCoefficient g (normalizedRamanujanMode m) (normalizedRamanujanMode m) N (c / N)| := by
      refine (abs_add_le _ _).trans ?_
      simp only [abs_mul, abs_of_nonneg (sq_nonneg β)]
      exact add_le_add (mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)) le_rfl
    _ ≤ |α * β| * (K * m * U * G * L + K * m * (U + V) * G * L) +
        β ^ 2 * (K * m * m.totient * G * L) :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h3 (sq_nonneg β))
    _ = _ := by ring

#print axioms jointTopCoefficient_two_mode
#print axioms exists_abs_ramanujan_packet_sub_polar_le
end
end GaloisForLFunctions.SuccessorShellArithmetic
