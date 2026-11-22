import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimitiveZeroReciprocalMass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.NormalizedZeroTruncation

/-! Truncate the primitive zero sum by real part and height while retaining its multiplicities. -/

open Complex Finset
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

namespace QH.PrimeProgressions

/-- The normalized Cesàro zero sum loses at most a power term on the left and a
logarithmic tail at large height. -/
theorem primitive_zero_truncation :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      χ.IsPrimitive → ∀ (y κ T : ℝ), 1 ≤ y → 0 < κ → 2 ≤ T →
        ‖∑' q : LZero χ,
          if 1 - κ < q.point.re ∧ |q.point.im| ≤ T then 0 else QH.zeroKernel y q.point‖ ≤
          C * ((N : ℝ) ^ 3 * y ^ (-κ) + Real.log ((N : ℝ) * T) ^ 2 / T) := by
  obtain ⟨C₀, hC₀, hmass⟩ := primitive_zero_reciprocal_mass
  refine ⟨max C₀ 100000, lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro N _ χ hχ hp y κ T hy _ hT
  obtain ⟨hs, hsum⟩ := hmass N χ hχ hp
  have hcount (F : Finset (LZero χ)) (n : ℕ) :
      ((F.filter (fun q => ⌊|q.point.im|⌋₊ = n)).card : ℝ) ≤ 4 * localCountConst N * Real.log ((n : ℝ) + 3) := by
    obtain ⟨hf, hc⟩ := ncard_zeros_floor_le hχ hp n
    have hsub : (↑(F.filter fun q => ⌊|q.point.im|⌋₊ = n) : Set (LZero χ)) ⊆
        {q : LZero χ | ⌊|q.point.im|⌋₊ = n} := fun _ hq => (mem_filter.mp hq).2
    have h := Set.ncard_le_ncard hsub hf
    rw [Set.ncard_coe_finset] at h
    exact (Nat.cast_le.mpr h).trans hc
  have h := normalized_zero_truncation (fun q : LZero χ => q.point)
    (fun q => (zero_re_mem hχ hp q).2.le) hs hsum
    (by positivity [localCountConst_nonneg (NeZero.pos N)] : 0 ≤ 4 * localCountConst N)
    hcount (κ := κ) hy hT
  refine h.trans ?_
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogT : (1 : ℝ) / 2 ≤ Real.log T :=
    (by linarith [Real.log_two_gt_d9] : (1 : ℝ) / 2 ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hT)
  have hlog : Real.log ((N : ℝ) * T) = Real.log N + Real.log T :=
    Real.log_mul hN0.ne' (by linarith)
  have hM : 4 * localCountConst N ≤ 1120 * Real.log ((N : ℝ) * T) := by
    rw [hlog]
    linarith [localCountConst_le (NeZero.pos N), Real.log_nonneg hN]
  have hTL : Real.log T ≤ Real.log ((N : ℝ) * T) := by
    rw [hlog]
    linarith [Real.log_nonneg hN]
  have hH : 4 * localCountConst N * (48 * Real.log T / T) ≤
      100000 * (Real.log ((N : ℝ) * T) ^ 2 / T) := by
    calc 4 * localCountConst N * (48 * Real.log T / T)
        ≤ (1120 * Real.log ((N : ℝ) * T)) * (48 * Real.log ((N : ℝ) * T) / T) := by
          have hnonneg : 0 ≤ Real.log ((N : ℝ) * T) := by linarith
          have := localCountConst_nonneg (NeZero.pos N)
          gcongr
      _ = (1120 * 48) * (Real.log ((N : ℝ) * T) ^ 2 / T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  rw [mul_add]
  exact add_le_add
    (by rw [← mul_assoc]; gcongr; exact le_max_left _ _)
    (hH.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))

end QH.PrimeProgressions
