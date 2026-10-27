import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaMetric
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceApertureMovingTail

/-!
# Finite arithmetic metrics on growing source apertures

One finite theta reading approximates every compact test with bounded C²
source size in a logarithmically growing support interval. Physical support
and Hecke displacement share the same aperture allowance. Normalization by
the moment order makes the estimate uniform over the entire family.
-/

open Complex MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- Whole-plane aperture growth is absorbed into the quartic current envelope. -/
lemma source_aperture_exp_window_le {a : ℝ} (ha : 0 ≤ a) (n : ℕ)
    (haN : a ≤ 2 * Real.log ((n : ℝ) + 1)) :
    Real.exp (2 * (a ^ 2 + a)) *
        Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) ≤
      Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) + 1)
    linarith only [h]
  have han : a ≤ 2 * (n : ℝ) := by linarith only [haN, hlog]
  have hasq := pow_le_pow_left₀ ha han 2
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hasq, han, sq_nonneg ((n : ℝ) - 1 / 2)]

/-- The growing-aperture quartic envelope tends to zero. -/
lemma tendsto_sourceApertureWindowError (B : ℝ) :
    Tendsto (fun n : ℕ => B *
      Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have h := (RiemannGaussian.tendsto_exp_neg_quadratic_add_linear_atTop
    (ε := 1) zero_lt_one 0 68 66).comp ht
  have he : Tendsto (fun n : ℕ =>
      Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66)) atTop (𝓝 0) := by
    apply h.congr'
    filter_upwards with n
    change Real.exp (-1 * ((n : ℝ) ^ 2 - 0) ^ 2 + 68 * (n : ℝ) ^ 2 + 66) =
      Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66)
    congr 1
    ring
  simpa only [mul_zero] using he.const_mul B

/-- A single source constant controls every test, order, and motion in the growing aperture. -/
theorem exists_finiteThetaSource_aperture_error_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ (f : CompactTest) (a : ℝ),
      0 ≤ a → (∀ u, f.1 u ≠ 0 → |u| ≤ a) → ∀ (j : ℕ) (L τ : ℝ),
      |τ| ≤ (n : ℝ) / 2 → a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |finiteThetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| / 4 ^ j ≤
      sourceTestSize f ^ 2 *
        (B * Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66) +
          40 * sourceReferenceTail n) := by
  obtain ⟨C, hC, hlocal⟩ := exists_explicitSourceLocalError_bound
  let B : ℝ := (2 * Real.pi)⁻¹ * 4 *
    (4 * Real.pi * finiteThetaPotentialConstant + 2 * Real.pi + 8 * C)
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hF := finiteThetaPotentialConstant_nonneg
    positivity
  refine ⟨B, hB, ?_⟩
  intro n hn f a ha hsupp j L τ hτ hwindow
  let A : ℝ := sourceTestSize f * Real.exp (a ^ 2 + a)
  have hA0 : 0 ≤ A := mul_nonneg (sourceTestSize_nonneg f) (Real.exp_pos _).le
  have hAsq : A ^ 2 = sourceTestSize f ^ 2 * Real.exp (2 * (a ^ 2 + a)) := by
    dsimp only [A]
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
  have hA := norm_tr_le_apertureGaussian f ha hsupp
  have hτ' : |τ| ≤ (n : ℝ) := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hτ, hn0]
  have hL : (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    linarith only [ha, hwindow]
  have haN : a ≤ 2 * Real.log ((n : ℝ) + 1) := by
    linarith only [hwindow, mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (abs_nonneg L)]
  have hfinite := finiteThetaSourceReading_error_le_window f hA0 hA j hn L τ hτ' hL
  have hsource := explicitSourceMomentCurrentError_le_window f hA0 hA hC.le
    j n L τ (hlocal n hn) hτ' hL
  have hcurrent := xiCurrentPairing_eq_trace
    (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)
    ((sourceCutoff n).contDiff.mul (contDiff_sourceDepthKernel (sourceTwist τ f) L j))
    (sourceCutoff n).hasCompactSupport.mul_right
  rw [hcurrent] at hsource
  have htail := sourceAperture_moving_trace_tail_le f ha hsupp j n L τ hτ hwindow
  have htriangle1 := dist_triangle
    (finiteThetaSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n)
    (explicitSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n)
    (zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
  have htriangle2 := dist_triangle
    (finiteThetaSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n)
    (zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))
  simp only [Real.dist_eq] at htriangle1 htriangle2
  rw [abs_sub_comm
    (zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))] at htriangle2
  have hcoef : 0 ≤ (4 : ℝ) ^ j * sourceTestSize f ^ 2 * B := by positivity
  have hcombined :
      |finiteThetaSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
        zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
      (4 : ℝ) ^ j * sourceTestSize f ^ 2 *
        (B * Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66)) := by
    refine (htriangle1.trans (add_le_add hfinite hsource)).trans ?_
    calc
      (((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) *
          (4 * Real.pi * finiteThetaPotentialConstant)) *
          Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) +
        (((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) * (2 * Real.pi + 8 * C)) *
          Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) =
        ((4 : ℝ) ^ j * sourceTestSize f ^ 2 * B) *
          (Real.exp (2 * (a ^ 2 + a)) *
            Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62)) := by
        simp only [hAsq, pow_succ (4 : ℝ) j, B]
        ring
      _ ≤ ((4 : ℝ) ^ j * sourceTestSize f ^ 2 * B) *
          Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66) :=
        mul_le_mul_of_nonneg_left (source_aperture_exp_window_le ha n haN) hcoef
      _ = _ := by ring
  have htail' :
      |zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j) -
        zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
      (4 : ℝ) ^ j * sourceTestSize f ^ 2 * (40 * sourceReferenceTail n) := by
    refine htail.trans ?_
    have hp : (2 : ℝ) ^ j ≤ 4 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have hm := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (sq_nonneg (sourceTestSize f))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40) (sourceReferenceTail_nonneg n)))
    nlinarith only [hm]
  rw [finiteThetaSourceMomentReading, ← zetaSourceTrace_depthKernel_eq]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ j)).2
  refine (htriangle2.trans (add_le_add hcombined htail')).trans_eq ?_
  ring

/-- The uniform test-class error is bounded entirely by arithmetic constants and the stage. -/
theorem exists_finiteThetaSource_aperture_logarithmic_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ (f : CompactTest) (a : ℝ),
      0 ≤ a → (∀ u, f.1 u ≠ 0 → |u| ≤ a) → ∀ (j : ℕ) (L τ : ℝ),
      |τ| ≤ (n : ℝ) / 2 → a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |finiteThetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| / 4 ^ j ≤
      sourceTestSize f ^ 2 *
        (B * Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66) +
          (640 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4))) := by
  obtain ⟨B, hB, hb⟩ := exists_finiteThetaSource_aperture_error_bound
  refine ⟨B, hB, fun n hn f a ha hsupp j L τ hτ hwindow =>
    (hb n hn f a ha hsupp j L τ hτ hwindow).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply add_le_add le_rfl
  have h := mul_le_mul_of_nonneg_left (sourceReferenceTail_le_log_div hn)
    (by norm_num : (0 : ℝ) ≤ 40)
  convert h using 1
  ring

/-- The cutoff threshold precedes all test, aperture, order, and motion choices. -/
theorem finiteThetaSource_uniform_test_aperture_moments :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ (f : CompactTest) (a : ℝ),
      sourceTestSize f ≤ 1 → 0 ≤ a → (∀ u, f.1 u ≠ 0 → |u| ≤ a) →
      ∀ (j : ℕ) (L τ : ℝ), |τ| ≤ (n : ℝ) / 2 →
      a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |finiteThetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| / 4 ^ j < ε := by
  obtain ⟨B, hB, hb⟩ := exists_finiteThetaSource_aperture_error_bound
  have ht : Tendsto (fun n : ℕ =>
      B * Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66) +
        40 * sourceReferenceTail n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_sourceApertureWindowError B).add (tendsto_sourceReferenceTail.const_mul 40)
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht ε hε
  refine ⟨max 1 N, fun n hn f a hS ha hsupp j L τ hτ hwindow => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnonneg : 0 ≤ B * Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66) +
      40 * sourceReferenceTail n :=
    add_nonneg (mul_nonneg hB (Real.exp_pos _).le)
      (mul_nonneg (by norm_num) (sourceReferenceTail_nonneg n))
  have hsmall := hN n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hsmall
  have hSsq : sourceTestSize f ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (sourceTestSize_nonneg f) hS 2
  exact ((hb n hn1 f a ha hsupp j L τ hτ hwindow).trans
    (mul_le_of_le_one_left hnonneg hSsq)).trans_lt hsmall

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_finiteThetaSource_aperture_error_bound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_finiteThetaSource_aperture_logarithmic_bound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.finiteThetaSource_uniform_test_aperture_moments
