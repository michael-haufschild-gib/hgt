import GaloisForLFunctions.BiScaleUncertainty.AnnularSourceRegularity
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicGaugeChebyshevEnergyRepresentation

/-!
# Chebyshev mean-square packet control for compact continuous sources

The actual collar source supplies its own C¹ regularity and compact gauge
derivative. The remaining source is controlled with its exact coherent chord
energy. Weighted packet splitting gives a source-only upper bound and transfers
it to global signed Chebyshev transport with an independent transport collar.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open ChebyshevGauge
noncomputable section
set_option autoImplicit false

/-- Exact source linearity of the actual mixed signed packet. -/
theorem signedSource_sub_apply (f g : C_c(ℝ, ℝ)) (N : ℕ) (u : ℝ) :
    signedSource (f-g) N u = signedSource f N u - signedSource g N u := by
  have hf : IntegrableOn (fun t => polarDensity t * f (u+t)) (Icc 0 (cutoff N)) :=
    (continuous_polarDensity.mul (f.continuous.comp (continuous_const.add continuous_id))).integrableOn_Icc
  have hg : IntegrableOn (fun t => polarDensity t * g (u+t)) (Icc 0 (cutoff N)) :=
    (continuous_polarDensity.mul (g.continuous.comp (continuous_const.add continuous_id))).integrableOn_Icc
  change (∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * (f-g) (u + Real.log n)) -
      (∫ t in Icc 0 (cutoff N), polarDensity t * (f-g) (u+t)) =
    ((∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * f (u + Real.log n)) -
      ∫ t in Icc 0 (cutoff N), polarDensity t * f (u+t)) -
    ((∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * g (u + Real.log n)) -
      ∫ t in Icc 0 (cutoff N), polarDensity t * g (u+t))
  simp only [CompactlySupportedContinuousMap.sub_apply, mul_sub, Finset.sum_sub_distrib,
    integral_sub hf hg]
  ring

private theorem weighted_square (x y c : ℝ) :
    (x+y)^2 ≤ (1+Real.exp c)*x^2 + (1+1/Real.exp c)*y^2 := by
  have hn := div_nonneg (sq_nonneg (Real.exp c * x - y)) (Real.exp_pos c).le
  have he : (1+Real.exp c)*x^2 + (1+1/Real.exp c)*y^2 - (x+y)^2 =
      (Real.exp c * x - y)^2 / Real.exp c := by
    field_simp
    ring
  rw [← he] at hn
  linarith only [hn]

/-- Adjustable splitting of the actual packet, with both source pieces admitted. -/
theorem packetEnergy_le_weighted_split (f g : C_c(ℝ, ℝ)) (N : ℕ) (c : ℝ) :
    packetEnergy f N ≤ (1+Real.exp c)*packetEnergy g N +
      (1+1/Real.exp c)*packetEnergy (f-g) N := by
  have energy (q : C_c(ℝ, ℝ)) : packetEnergy q N = ∫ u, signedSource q N u ^ 2 :=
    (integral_sq_eq_autocorr_zero (signedSource q N)).symm
  have hf := integrable_sq (g := (signedSource f N : ℝ → ℝ))
    (signedSource f N).continuous (signedSource f N).hasCompactSupport
  have hg := integrable_sq (g := (signedSource g N : ℝ → ℝ))
    (signedSource g N).continuous (signedSource g N).hasCompactSupport
  have hr := integrable_sq (g := (signedSource (f-g) N : ℝ → ℝ))
    (signedSource (f-g) N).continuous (signedSource (f-g) N).hasCompactSupport
  have hmajor : Integrable (fun u => (1+Real.exp c)*signedSource g N u ^ 2 +
      (1+1/Real.exp c)*signedSource (f-g) N u ^ 2) :=
    (hg.const_mul _).add (hr.const_mul _)
  rw [energy f, energy g, energy (f-g)]
  calc
    _ ≤ ∫ u, (1+Real.exp c)*signedSource g N u ^ 2 +
        (1+1/Real.exp c)*signedSource (f-g) N u ^ 2 := by
      apply integral_mono hf hmajor
      intro u
      have he : signedSource f N u = signedSource g N u + signedSource (f-g) N u := by
        rw [signedSource_sub_apply]
        ring
      dsimp only
      rw [he]
      exact weighted_square _ _ c
    _ = _ := by
      rw [integral_add (hg.const_mul _) (hr.const_mul _), integral_const_mul, integral_const_mul]

/-- The supplied gauge source is exactly the derivative gauge of the actual collar. -/
theorem gaugeDerivative_collarSource (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    gaugeDerivative (collarSource f a b : ℝ → ℝ) = (collarGaugeSource f a b : ℝ → ℝ) := by
  funext u
  unfold gaugeDerivative
  rw [deriv_collarSource]
  rfl

/-- Smooth packet control applies to the constructed collar without a source premise. -/
theorem collar_packetEnergy_le_gauge (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    packetEnergy (collarSource f a b) N ≤
      3 * (10 + normalizedLogError (cutoff N)^2) * collarEnergy f a b +
        3 * collarGaugeL1 f a b ^ 2 *
          ∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2 := by
  have hs := packetEnergy_le_chebyshev_mean_square
    (collarSource f a b) (contDiff_collarSource f a b) N
  rw [gaugeDerivative_collarSource] at hs
  exact hs

/-- The roughness term keeps the original source's exact coherent remainder. -/
theorem remainder_packetEnergy_le (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    packetEnergy (collarRemainderSource f a b) N ≤ mass N ^ 2 * collarChordEnergy f a b := by
  have hs := packetEnergy_le_mass_sq (collarRemainderSource f a b) N
  rwa [autocorr_collarRemainderSource_zero] at hs

/-- Mean-square Chebyshev upper control for every original compact continuous source. -/
theorem packetEnergy_le_weighted_collarGauge (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) :
    packetEnergy f N ≤
      3 * (1+Real.exp c) * (10+normalizedLogError (cutoff N)^2) * collarEnergy f a b +
      3 * (1+Real.exp c) * collarGaugeL1 f a b ^ 2 *
        (∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2) +
      (1+1/Real.exp c) * mass N ^ 2 * collarChordEnergy f a b := by
  have hs := packetEnergy_le_weighted_split f (collarSource f a b) N c
  have hg := collar_packetEnergy_le_gauge f a b N
  have hr := remainder_packetEnergy_le f a b N
  change packetEnergy f N ≤ (1+Real.exp c)*packetEnergy (collarSource f a b) N +
    (1+1/Real.exp c)*packetEnergy (collarRemainderSource f a b) N at hs
  calc
    _ ≤ _ := hs
    _ ≤ (1+Real.exp c) *
        (3 * (10+normalizedLogError (cutoff N)^2) * collarEnergy f a b +
          3 * collarGaugeL1 f a b ^ 2 * ∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2) +
        (1+1/Real.exp c) * (mass N ^ 2 * collarChordEnergy f a b) :=
      add_le_add (mul_le_mul_of_nonneg_left hg (by positivity))
        (mul_le_mul_of_nonneg_left hr (by positivity))
    _ = _ := by ring

/-- Explicit fixed-constant budget with the original-source roughness retained. -/
def roughGaugeBound (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) : ℝ :=
  6 * (10+normalizedLogError (cutoff N)^2) * collarEnergy f a b +
    6 * collarGaugeL1 f a b ^ 2 * (∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2) +
    2 * mass N ^ 2 * collarChordEnergy f a b

theorem packetEnergy_le_roughGaugeBound (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    packetEnergy f N ≤ roughGaugeBound f a b N := by
  have hs := packetEnergy_le_weighted_collarGauge f a b 0 N
  norm_num only [Real.exp_zero, one_div_one] at hs
  exact hs

theorem roughGaugeBound_nonneg (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    0 ≤ roughGaugeBound f a b N :=
  (packetEnergy_nonneg f N).trans (packetEnergy_le_roughGaugeBound f a b N)

/-- Both quantitative integrals are admitted on their actual domains. -/
theorem roughGaugeBound_integrals_admissible (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    Integrable (fun u => |collarGaugeSource f a b u|) ∧
      IntegrableOn (fun t => normalizedLogError t ^ 2) (Icc 0 (cutoff N)) :=
  ⟨integrable_abs_collarGaugeSource f a b, integrableOn_normalizedLogError_sq (cutoff N)⟩

/-- Smoothing and global transport collars may be chosen independently. -/
theorem fullPairing_sub_work_sq_le_roughGauge (f : C_c(ℝ, ℝ)) (a b u v : ℝ) (K : ℕ) :
    (fullPairing (autocorr f) - fullChebyshevWork f u v)^2 ≤
      roughGaugeBound f a b (sourceCutoff f + K) * collarChordEnergy f u v :=
  (fullPairing_sub_work_sq_le_coherent f u v K).trans
    (mul_le_mul_of_nonneg_right (packetEnergy_le_roughGaugeBound f a b _)
      (collarChordEnergy_nonneg f u v))

/-- Global signed transport with explicit rough-source Chebyshev control and the
exact reciprocal Lévy–sinh penalty. Every parameter is unconstrained. -/
theorem abs_fullPairing_sub_work_le_roughGauge_levy (f : C_c(ℝ, ℝ))
    (a b u v c : ℝ) (K : ℕ) :
    |fullPairing (autocorr f) - fullChebyshevWork f u v| ≤
      Real.exp c * (∫ y in Real.exp u..Real.exp u + Real.exp v,
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
      roughGaugeBound f a b (sourceCutoff f + K) / (2 * Real.exp c * Real.exp v ^ 2) *
        ∫ y in Real.exp u..Real.exp u + Real.exp v, Real.exp (-y / 2) * Real.sinh y := by
  have hi : 0 ≤ ∫ y in Real.exp u..Real.exp u + Real.exp v,
      Real.exp (-y / 2) * Real.sinh y := by
    apply intervalIntegral.integral_nonneg (le_add_of_nonneg_right (Real.exp_pos v).le)
    intro y hy
    rw [← inv_archLevySinhWeight_eq]
    exact inv_nonneg.mpr (archLevySinhWeight_pos ((Real.exp_pos u).trans_le hy.1)).le
  apply (abs_fullPairing_sub_fullChebyshevWork_le_packet_levy f u v c K).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ hi
  exact div_le_div_of_nonneg_right (packetEnergy_le_roughGaugeBound f a b _) (by positivity)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
