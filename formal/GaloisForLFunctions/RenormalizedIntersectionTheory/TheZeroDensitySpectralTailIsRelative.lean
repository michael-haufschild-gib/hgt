import GaloisForLFunctions.RenormalizedIntersectionTheory.TheSparseFlipHasRelativeProjectedMass

/-!
# Relative spectral tails at zero prime density

Projected mass grows at most as the square root of the logarithmic prime cutoff,
relative to the actual global harmonic correlation. Rough Poincaré loses one
logarithm. Along squared cutoffs the resulting quarter-power decay is geometric.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- At zero prime density, the spectral tail above cutoff `T` is small relative
to the actual harmonic correlation, with quarter-power decay in `log T`. -/
theorem exists_eventually_relative_spectralTail_bound (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ T : ℕ, 3 ≤ T → T ≤ N → ∀ u : EuclideanSpace ℝ (PrimeHorizonIndex N),
        |⟪u, gaugeVector N (primeSetFlip P) -
          (smoothFibreSpace T N).starProjection (gaugeVector N (primeSetFlip P))⟫| ≤
          (K₁ * (gaugeHarmonicSum (primeSetFlip P) N ^ (2 : ℕ) / Real.log N) ^ (1 / 2 : ℝ) *
            Real.log T ^ (-(1 / 4 : ℝ)) + K₂) * Real.sqrt (poleDefect N (horizonExtend u)) := by
  obtain ⟨Kp, hKp, hPoinc⟩ := exists_norm_sub_starProjection_sq_le
  obtain ⟨K', hK', hmass⟩ := exists_eventually_relative_projectedMass_le_sqrt_log P hP
  let r := (2 : ℝ) ^ (-(1 / 4 : ℝ))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  refine ⟨Real.sqrt (2 * K' * Kp) * (r / (1 - r)), 2 * Real.sqrt Kp,
    mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hr0 (by linarith only [hr1])), by positivity, ?_⟩
  filter_upwards [hmass] with N hmassN T hT hTN u
  let ω := gaugeVector N (primeSetFlip P)
  let D := poleDefect N (horizonExtend u)
  let L := Real.log T
  let R := gaugeHarmonicSum (primeSetFlip P) N ^ (2 : ℕ) / Real.log N
  have hD : 0 ≤ D := poleDefect_nonneg N _
  have hL1 : 1 ≤ L := one_le_log_of_three_le hT
  have hLN1 : 1 ≤ Real.log N := one_le_log_of_three_le (hT.trans hTN)
  have hR : 0 ≤ R := div_nonneg (sq_nonneg _) (zero_le_one.trans hLN1)
  have hXhalf : (R ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = R := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR]
    norm_num
  have hXquarter : (R ^ (2 : ℕ)) ^ (1 / 4 : ℝ) = R ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR]
    norm_num
  let K : ℕ → Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)) :=
    fun j => smoothFibreSpace (T ^ 2 ^ j) N
  have hKmono : ∀ j, K j ≤ K (j + 1) := fun j =>
    smoothFibreSpace_mono (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_succ j)))
  let J := Nat.log 2 (Nat.log T N)
  have hlogTN : Nat.log T N ≠ 0 := (Nat.log_pos (by omega) hTN).ne'
  have hscaleN : ∀ j, j ≤ J → T ^ 2 ^ j ≤ N := fun j hj =>
    (Nat.pow_le_pow_right (by omega) ((Nat.pow_le_pow_right (by norm_num) hj).trans
      (Nat.pow_log_le_self 2 hlogTN))).trans (Nat.pow_log_le_self T (by omega))
  have htop : (N : ℝ) < (T : ℝ) ^ 2 ^ (J + 1) := by
    have h1 := Nat.lt_pow_succ_log_self (show 1 < T by omega) N
    have h2 := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (Nat.log T N)
    exact_mod_cast h1.trans_le (Nat.pow_le_pow_right (by omega) h2)
  have hlogQ : ∀ j, Real.log ((T ^ 2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j * L := fun j => by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have hK0 : K 0 = smoothFibreSpace T N := by simp [K]
  have htel := abs_inner_sub_starProjection_le K hKmono ω u J
  rw [hK0] at htel
  refine htel.trans ?_
  have hterm : ∀ j ∈ range J, ‖(K (j + 1)).starProjection ω‖ * ‖u - (K j).starProjection u‖ ≤
      Real.sqrt (2 * K' * Kp) * R ^ (1 / 2 : ℝ) * L ^ (-(1 / 4 : ℝ)) *
        r ^ (j + 1) * Real.sqrt D := by
    intro j hj
    have hjJ : j + 1 ≤ J := mem_range.mp hj
    have hQ3 : 3 ≤ T ^ 2 ^ (j + 1) := hT.trans (Nat.le_self_pow (by positivity) T)
    have hQ2 : 2 ≤ T ^ 2 ^ j := le_trans (by omega) (Nat.le_self_pow (by positivity) T)
    have hlam : 0 < (2 : ℝ) ^ (j + 1) * L := by positivity
    have hPb : ‖(K (j + 1)).starProjection ω‖ ^ (2 : ℕ) ≤
        K' * (R ^ (2 : ℕ)) ^ (1 / 2 : ℝ) *
          ((2 : ℝ) ^ (j + 1) * L) ^ (1 - (1 / 2 : ℝ)) := by
      have h := hmassN (T ^ 2 ^ (j + 1)) hQ3 (hscaleN (j + 1) hjJ)
      rw [hlogQ] at h
      rw [hXhalf, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      exact h
    have hWb : ‖u - (K j).starProjection u‖ ^ (2 : ℕ) ≤
        Kp / ((2 : ℝ) ^ (j + 1) * L / 2) * D := by
      have h := hPoinc (T ^ 2 ^ j) N hQ2 u
      rw [hlogQ] at h
      rw [show (2 : ℝ) ^ (j + 1) * L / 2 = 2 ^ j * L by ring]
      exact h
    have h := mul_le_of_scale (norm_nonneg _) (norm_nonneg _) hK' hKp (sq_nonneg R) hlam hD hPb hWb
    rw [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num, hXquarter,
      two_pow_mul_rpow (show 0 ≤ L by linarith only [hL1])] at h
    exact h.trans_eq (by dsimp only [r]; ring)
  have hlast : ‖ω‖ * ‖u - (K J).starProjection u‖ ≤ 2 * Real.sqrt Kp * Real.sqrt D := by
    have hω2 : ‖ω‖ ^ (2 : ℕ) ≤ 2 * Real.log N := by
      dsimp only [ω]
      rw [norm_gaugeVector_sq]
      have h := hsum_le N
      unfold hsum at h
      simp only [one_div]
      linarith only [h, hLN1]
    have hQJ : 2 ≤ T ^ 2 ^ J := le_trans (by omega) (Nat.le_self_pow (by positivity) T)
    have hW := hPoinc (T ^ 2 ^ J) N hQJ u
    rw [hlogQ] at hW
    have hlamJ : Real.log N / 2 ≤ (2 : ℝ) ^ J * L := by
      have h := Real.log_lt_log (by exact_mod_cast (show 0 < N by omega)) htop
      rw [Real.log_pow] at h
      push_cast at h
      rw [pow_succ] at h
      linarith only [h]
    have hW' : ‖u - (K J).starProjection u‖ ^ (2 : ℕ) ≤ 2 * Kp / Real.log N * D := by
      refine hW.trans (mul_le_mul_of_nonneg_right ?_ hD)
      rw [div_le_div_iff₀ (by positivity) (by linarith only [hLN1])]
      nlinarith only [mul_le_mul_of_nonneg_left hlamJ hKp]
    have hrhs : 0 ≤ 2 * Real.sqrt Kp * Real.sqrt D := by positivity
    rw [← pow_le_pow_iff_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hrhs two_ne_zero,
      mul_pow, mul_pow, mul_pow, Real.sq_sqrt hKp, Real.sq_sqrt hD]
    calc
      ‖ω‖ ^ (2 : ℕ) * ‖u - (K J).starProjection u‖ ^ (2 : ℕ) ≤
          2 * Real.log N * (2 * Kp / Real.log N * D) :=
        mul_le_mul hω2 hW' (sq_nonneg _) (by linarith only [hLN1])
      _ = 2 ^ (2 : ℕ) * Kp * D := by field_simp
  have hgeo := sum_range_pow_succ_le hr0 hr1 J
  have hpos : 0 ≤ Real.sqrt (2 * K' * Kp) * R ^ (1 / 2 : ℝ) *
      L ^ (-(1 / 4 : ℝ)) * Real.sqrt D := by positivity
  calc
    _ ≤ ∑ j ∈ range J, Real.sqrt (2 * K' * Kp) * R ^ (1 / 2 : ℝ) *
        L ^ (-(1 / 4 : ℝ)) * r ^ (j + 1) * Real.sqrt D + 2 * Real.sqrt Kp * Real.sqrt D :=
      add_le_add (sum_le_sum hterm) hlast
    _ = Real.sqrt (2 * K' * Kp) * R ^ (1 / 2 : ℝ) * L ^ (-(1 / 4 : ℝ)) *
        Real.sqrt D * ∑ j ∈ range J, r ^ (j + 1) + 2 * Real.sqrt Kp * Real.sqrt D := by
      rw [mul_sum]
      congr 1
      exact sum_congr rfl fun j _ => by ring
    _ ≤ Real.sqrt (2 * K' * Kp) * R ^ (1 / 2 : ℝ) * L ^ (-(1 / 4 : ℝ)) *
        Real.sqrt D * (r / (1 - r)) + 2 * Real.sqrt Kp * Real.sqrt D :=
      add_le_add (mul_le_mul_of_nonneg_left hgeo hpos) le_rfl
    _ = _ := by ring

end GaloisForLFunctions.RenormalizedIntersectionTheory

