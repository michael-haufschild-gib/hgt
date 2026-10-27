import GaloisForLFunctions.ConjugateDiagonalGeometry.PolynomialThetaReadingError
import GaloisForLFunctions.ConjugateDiagonalGeometry.StripSourceTail
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceReferenceTailArithmetic
import GaloisForLFunctions.ConjugateDiagonalGeometry.MovingSourceMetric

/-!
# The full collided metric from polynomial integer theta prefixes

One prescribed finite arithmetic source recovers all normalized tests in a
growing physical and Hecke aperture. Its integer prefix is polynomial in
height. The positive reading retains multiplicities and the full collided
trace; it imposes no critical-line or zero-separation assumption.
-/

open Complex MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- Positive moment reading from the prescribed polynomial integer prefix. -/
def polynomialThetaSourceMomentReading (f : CompactTest) (L : ℝ) (j n : ℕ) : ℝ :=
  polynomialThetaSourceReading (sourceDepthKernel f L j) n

lemma polynomialThetaSourceMomentReading_nonneg (f : CompactTest) (L : ℝ) (j n : ℕ) :
    0 ≤ polynomialThetaSourceMomentReading f L j n := by
  apply mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
  apply integral_nonneg
  intro z
  exact mul_nonneg (mul_nonneg (stripSourceCutoff_nonneg n z)
    (mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (depthKernel_nonneg _ _) j)))
    (finiteThetaSourceCurvature_nonneg (polynomialSourceRegulator_pos n).le _ z)

/-- The finite-source estimate is uniform before every test, order, aperture and motion choice. -/
theorem exists_polynomialThetaSource_aperture_error_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ (f : CompactTest) (a : ℝ),
      0 ≤ a → (∀ u, f.1 u ≠ 0 → |u| ≤ a) → ∀ (j : ℕ) (L τ : ℝ),
      |τ| ≤ (n : ℝ) / 2 → a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |polynomialThetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| / 4 ^ j ≤
      sourceTestSize f ^ 2 * (B / ((n : ℝ) + 1) ^ 2 + 40 * sourceReferenceTail n) := by
  obtain ⟨E, hE, hsourceBound⟩ := exists_polynomialSourceMomentCurrentError_bound
  let B : ℝ := 242 * stripThetaPotentialConstant + E
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hC := stripThetaPotentialConstant_nonneg
    positivity
  refine ⟨B, hB, ?_⟩
  intro n hn f a ha hsupp j L τ hτ hwindow
  have hfinite := polynomialThetaSourceReading_error_le f ha hsupp L τ j n hwindow
  have hsource := hsourceBound n hn f a ha hsupp j L τ hwindow
  have hcurrent := xiCurrentPairing_eq_trace
    (fun z => stripSourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)
    ((contDiff_stripSourceCutoff n).mul (contDiff_sourceDepthKernel (sourceTwist τ f) L j))
    (hasCompactSupport_stripSourceCutoff n).mul_right
  rw [hcurrent] at hsource
  have htail := stripSource_aperture_moving_trace_tail_le f ha hsupp j n L τ hτ hwindow
  have htriangle1 := dist_triangle
    (polynomialThetaSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n)
    (polynomialSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n)
    (zetaSourceTrace (fun z => stripSourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
  have htriangle2 := dist_triangle
    (polynomialThetaSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n)
    (zetaSourceTrace (fun z => stripSourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))
  simp only [Real.dist_eq] at htriangle1 htriangle2
  rw [abs_sub_comm
    (zetaSourceTrace (fun z => stripSourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))] at htriangle2
  have hpow : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 6 := by
    have h4 : 1 ≤ ((n : ℝ) + 1) ^ 4 := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) n))
    have h := le_mul_of_one_le_right (by positivity : 0 ≤ ((n : ℝ) + 1) ^ 2) h4
    simpa only [← pow_add] using h
  have hfinite' :
      |polynomialThetaSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
        polynomialSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n| ≤
      (4 : ℝ) ^ j * sourceTestSize f ^ 2 *
        (242 * stripThetaPotentialConstant / ((n : ℝ) + 1) ^ 2) := by
    refine hfinite.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 242) stripThetaPotentialConstant_nonneg)
      (by positivity) hpow
  have hcombined :
      |polynomialThetaSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
        zetaSourceTrace (fun z => stripSourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
      (4 : ℝ) ^ j * sourceTestSize f ^ 2 * (B / ((n : ℝ) + 1) ^ 2) := by
    refine (htriangle1.trans (add_le_add hfinite' hsource)).trans_eq ?_
    dsimp only [B]
    ring
  have htail' :
      |zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j) -
        zetaSourceTrace (fun z => stripSourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
      (4 : ℝ) ^ j * sourceTestSize f ^ 2 * (40 * sourceReferenceTail n) := by
    refine htail.trans ?_
    have hp : (2 : ℝ) ^ j ≤ 4 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have hm := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (sq_nonneg (sourceTestSize f))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40) (sourceReferenceTail_nonneg n)))
    nlinarith only [hm]
  rw [polynomialThetaSourceMomentReading, ← zetaSourceTrace_depthKernel_eq]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ j)).2
  refine (htriangle2.trans (add_le_add hcombined htail')).trans_eq ?_
  ring

/-- A universal arithmetic error certificate for the polynomial finite-prefix metric. -/
theorem exists_polynomialThetaSource_aperture_logarithmic_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ (f : CompactTest) (a : ℝ),
      0 ≤ a → (∀ u, f.1 u ≠ 0 → |u| ≤ a) → ∀ (j : ℕ) (L τ : ℝ),
      |τ| ≤ (n : ℝ) / 2 → a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |polynomialThetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| / 4 ^ j ≤
      sourceTestSize f ^ 2 *
        (B / ((n : ℝ) + 1) ^ 2 +
          (640 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4))) := by
  obtain ⟨B, hB, hb⟩ := exists_polynomialThetaSource_aperture_error_bound
  refine ⟨B, hB, fun n hn f a ha hsupp j L τ hτ hwindow =>
    (hb n hn f a ha hsupp j L τ hτ hwindow).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply add_le_add le_rfl
  have h := mul_le_mul_of_nonneg_left (sourceReferenceTail_le_log_div hn)
    (by norm_num : (0 : ℝ) ≤ 40)
  convert h using 1
  ring

lemma tendsto_polynomialSourceWindowError (B : ℝ) :
    Tendsto (fun n : ℕ => B / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
  have hi := tendsto_inv_atTop_zero.comp ht
  simpa [div_eq_mul_inv] using (hi.pow 2).const_mul B

/-- One finite-source stage works for the entire normalized growing test family. -/
theorem polynomialThetaSource_uniform_test_aperture_moments :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ (f : CompactTest) (a : ℝ),
      sourceTestSize f ≤ 1 → 0 ≤ a → (∀ u, f.1 u ≠ 0 → |u| ≤ a) →
      ∀ (j : ℕ) (L τ : ℝ), |τ| ≤ (n : ℝ) / 2 →
      a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |polynomialThetaSourceMomentReading (sourceTwist τ f) L j n -
        ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (sourceTwist τ f) ρ * depthKernel L (zetaDepth ρ) ^ j| / 4 ^ j < ε := by
  obtain ⟨B, hB, hb⟩ := exists_polynomialThetaSource_aperture_error_bound
  have ht : Tendsto (fun n : ℕ =>
      B / ((n : ℝ) + 1) ^ 2 + 40 * sourceReferenceTail n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_polynomialSourceWindowError B).add (tendsto_sourceReferenceTail.const_mul 40)
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht ε hε
  refine ⟨max 1 N, fun n hn f a hS ha hsupp j L τ hτ hwindow => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnonneg : 0 ≤ B / ((n : ℝ) + 1) ^ 2 + 40 * sourceReferenceTail n :=
    add_nonneg (div_nonneg hB (sq_nonneg _))
      (mul_nonneg (by norm_num) (sourceReferenceTail_nonneg n))
  have hsmall := hN n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hsmall
  have hSsq : sourceTestSize f ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (sourceTestSize_nonneg f) hS 2
  exact ((hb n hn1 f a ha hsupp j L τ hτ hwindow).trans
    (mul_le_of_le_one_left hnonneg hSsq)).trans_lt hsmall

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.polynomialThetaSourceMomentReading_nonneg
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_polynomialThetaSource_aperture_error_bound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_polynomialThetaSource_aperture_logarithmic_bound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.polynomialThetaSource_uniform_test_aperture_moments
