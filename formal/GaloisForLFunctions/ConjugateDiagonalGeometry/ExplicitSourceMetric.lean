import GaloisForLFunctions.ConjugateDiagonalGeometry.XiExpRegulatorError
import GaloisForLFunctions.ConjugateDiagonalGeometry.ExplicitSourceWindowBounds
import GaloisForLFunctions.ConjugateDiagonalGeometry.MovingSourceMetric

/-!
# Uniform xi source readings with a prescribed regulator

The scalar potential estimate and the moving Laplacian bound give a quartic
exponential current error. The actual divisor's summable reference tail then
removes the cutoff uniformly in ordinate and logarithmic Hecke motion.
-/

open Complex MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Laplacian Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- A positive source reading with a prescribed exponential regulator. -/
def explicitSourceReading (φ : ℂ → ℝ) (n : ℕ) : ℝ :=
  Real.pi⁻¹ * ∫ z, sourceCutoff n z * φ z * xiCurvatureDensity (explicitSourceRegulator n) z

lemma abs_explicitSourceReading_sub_current_le (φ : ℂ → ℝ) (hp : ContDiff ℝ 2 φ)
    (n : ℕ) {B : ℝ}
    (hb : ∀ z ∈ closedBall (0 : ℂ) |(n : ℝ) + 2|,
      |Δ (fun w => sourceCutoff n w * φ w) z| ≤ B) :
    |explicitSourceReading φ n - xiCurrentPairing (fun z => sourceCutoff n z * φ z)| ≤
      (2 * Real.pi)⁻¹ * B * xiLocalPotentialError (explicitSourceRegulator n) 0 ((n : ℝ) + 2) := by
  have h := abs_xiCurvatureReading_sub_current_le_of_pos
    (fun z => sourceCutoff n z * φ z) ((sourceCutoff n).contDiff.mul hp)
    (sourceCutoff n).hasCompactSupport.mul_right 0 ((n : ℝ) + 2) B
    (sourceCutoff_laplacian_eq_zero_outside n φ hp) hb (explicitSourceRegulator_pos n)
  have he : explicitSourceReading φ n - xiCurrentPairing (fun z => sourceCutoff n z * φ z) =
      Real.pi⁻¹ * ((∫ z, (sourceCutoff n z * φ z) * xiCurvatureDensity (explicitSourceRegulator n) z) -
        (1 / 2 : ℝ) * ∫ z, Real.log ‖xi z‖ * Δ (fun w => sourceCutoff n w * φ w) z) := by
    unfold explicitSourceReading xiCurrentPairing
    ring
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr Real.pi_pos)]
  calc
    Real.pi⁻¹ * |(∫ z, (sourceCutoff n z * φ z) * xiCurvatureDensity (explicitSourceRegulator n) z) -
        (1 / 2 : ℝ) * ∫ z, Real.log ‖xi z‖ * Δ (fun w => sourceCutoff n w * φ w) z| ≤
        Real.pi⁻¹ * ((1 / 2 : ℝ) * B *
          xiLocalPotentialError (explicitSourceRegulator n) 0 ((n : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by ring

lemma explicitSourceMomentCurrentError_le (f : CompactTest) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ z : ℂ, ‖tr f.1 z‖ ≤ A * Real.exp (‖z‖ ^ 2))
    (j n : ℕ) (L τ : ℝ) :
    |explicitSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
      xiCurrentPairing (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
    ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) *
      Real.exp (2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2))) *
      (sourceCutoffControl n * xiLocalPotentialError (explicitSourceRegulator n) 0 ((n : ℝ) + 2)) := by
  have hb : ∀ z ∈ closedBall (0 : ℂ) |(n : ℝ) + 2|,
      |Δ (fun w => sourceCutoff n w * sourceDepthKernel (sourceTwist τ f) L j w) z| ≤
        4 ^ j * sourceSquareEnvelope A n τ ((j : ℝ) * |L|) := by
    intro z hz
    have hz' : ‖z‖ ≤ (n : ℝ) + 2 := by
      simpa only [mem_closedBall, dist_zero_right,
        abs_of_pos (by positivity : 0 < (n : ℝ) + 2)] using hz
    simpa only [sourceTranslate_zero, abs_zero, zero_add] using
      abs_laplacian_cutoff_moving_moment_le f hA0 hA L j n 0 τ hz'
  refine (abs_explicitSourceReading_sub_current_le _
    (contDiff_sourceDepthKernel (sourceTwist τ f) L j) n hb).trans_eq ?_
  unfold sourceSquareEnvelope
  rw [pow_succ (4 : ℝ) j]
  ring

/-- The actual local error propagates through the full moving C² envelope. -/
lemma explicitSourceMomentCurrentError_le_window (f : CompactTest) {A C : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ z : ℂ, ‖tr f.1 z‖ ≤ A * Real.exp (‖z‖ ^ 2))
    (hC : 0 ≤ C) (j n : ℕ) (L τ : ℝ)
    (hlocal : sourceCutoffControl n *
        xiLocalPotentialError (explicitSourceRegulator n) 0 ((n : ℝ) + 2) ≤
      (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 + 8 * C * ((n : ℝ) + 1) ^ 6) *
        Real.exp (-(((n : ℝ) + 1) ^ 4)))
    (hτ : |τ| ≤ (n : ℝ)) (hL : (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1)) :
    |explicitSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
      xiCurrentPairing (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
    (((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) * (2 * Real.pi + 8 * C)) *
      Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
  have hcoef : 0 ≤ (2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2 := by positivity
  refine (explicitSourceMomentCurrentError_le f hA0 hA j n L τ).trans ?_
  calc
    ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) *
        Real.exp (2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2))) *
        (sourceCutoffControl n * xiLocalPotentialError (explicitSourceRegulator n) 0 ((n : ℝ) + 2)) ≤
      ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) *
        Real.exp (2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2))) *
        ((Real.pi * ((n : ℝ) + 2) ^ 2 / 2 + 8 * C * ((n : ℝ) + 1) ^ 6) *
          Real.exp (-(((n : ℝ) + 1) ^ 4))) :=
      mul_le_mul_of_nonneg_left hlocal (mul_nonneg hcoef (Real.exp_pos _).le)
    _ = ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) *
        ((Real.pi * ((n : ℝ) + 2) ^ 2 / 2 + 8 * C * ((n : ℝ) + 1) ^ 6) *
          Real.exp (-(((n : ℝ) + 1) ^ 4) +
            2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2)))) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (source_poly_exp_window_le hC j n L τ hτ hL) hcoef

/-- The prescribed arithmetic regulator controls every compact moment in the joint window. -/
theorem explicitSourceReading_uniform_cutoff_current (f : CompactTest) (j : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |explicitSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
          xiCurrentPairing (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| < ε := by
  obtain ⟨A, hA1, hA⟩ := norm_tr_le_sourceGaussian f
  obtain ⟨C, hC, hlocal⟩ := exists_explicitSourceLocalError_bound
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_explicitWindowError (((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) *
      (2 * Real.pi + 8 * C))) ε hε
  refine ⟨max 1 N, fun n hn L τ hτ hL => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hsmall : (((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) * (2 * Real.pi + 8 * C)) *
      Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) < ε := by
    have h := hN n ((le_max_right _ _).trans hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
    exact h
  exact (explicitSourceMomentCurrentError_le_window f (by linarith only [hA1]) hA hC.le
    j n L τ (hlocal n hn1) hτ hL).trans_lt hsmall

/-- One prescribed regulator evaluates the full actual collided moment uniformly in both motions. -/
theorem explicitSourceReading_uniform_moving_moments (f : CompactTest) (j : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L τ : ℝ,
      |τ| ≤ (n : ℝ) / 2 → (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |explicitSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
          zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j)| < ε := by
  intro ε hε
  obtain ⟨Ns, hs⟩ := explicitSourceReading_uniform_cutoff_current f j (ε / 2) (by positivity)
  obtain ⟨Nt, ht⟩ := uniform_moving_depth_trace_tail f j (ε / 2) (by positivity)
  refine ⟨max Ns Nt, fun n hn L τ hτ hL => ?_⟩
  have hτ' : |τ| ≤ (n : ℝ) := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hτ, hn0]
  have hsource := hs n ((le_max_left _ _).trans hn) L τ hτ' hL
  have htail := ht n ((le_max_right _ _).trans hn) L τ hτ hL
  have hcurrent := xiCurrentPairing_eq_trace
    (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)
    ((sourceCutoff n).contDiff.mul (contDiff_sourceDepthKernel (sourceTwist τ f) L j))
    (sourceCutoff n).hasCompactSupport.mul_right
  rw [hcurrent] at hsource
  have htriangle := dist_triangle
    (explicitSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n)
    (zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))
  simp only [Real.dist_eq] at htriangle
  rw [abs_sub_comm
    (zetaSourceTrace (fun z => sourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z))
    (zetaSourceTrace (sourceDepthKernel (sourceTwist τ f) L j))] at htriangle
  linarith only [hsource, htail, htriangle]

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.explicitSourceReading_uniform_moving_moments
