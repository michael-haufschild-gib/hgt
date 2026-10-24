import GaloisForLFunctions.ArithmeticDefectRigidity.TheForcingSplitsIntoAPowerAndAnAdmittedRemainder
import GaloisForLFunctions.HTGeometry.SubexponentialSqrtSummable
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverReadsTheDirichletSeriesAtTheCriticalPoint

/-!
# The actual receiver has an absolute trace at the cofactor pole

The actual VK bound makes `A(n) n^(ε-2)` absolutely summable. The Mellin-cell pairing therefore
extends continuously to `σ = 1-ε`. Approaching from the absolutely convergent Dirichlet-series
side identifies its value: the trace divided by `1-ε` is exactly the forcing power coefficient.

This supplies a source-defined linear boundary observable. It does not bound receiver energy.
-/

open Finset Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.TransHorizonIncidenceMechanics
  (mellinCell mellinCell_bounds mellinCell_nonneg dampedDensity
   hasSum_pmPowerDampedRealWeight_div pmPowerDampedRealWeight_mem_dampedClass
   mellinPairing_eq_zeta_mul subHalfZetaCoeff)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- An absolute envelope for the actual receiver's trace at the cofactor pole. -/
def poleTraceEnvelope (ε : ℝ) (n : ℕ) : ℝ :=
  |pmPowerDampedCenteredDivisorPrefix ε n| * (n : ℝ) ^ (ε - 2)

theorem poleTraceEnvelope_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ poleTraceEnvelope ε n := by
  unfold poleTraceEnvelope
  positivity

/-- The actual arithmetic saving pays the endpoint Mellin envelope absolutely. -/
theorem summable_poleTraceEnvelope (ε : SubcriticalDamping) :
    Summable (poleTraceEnvelope ε) := by
  obtain ⟨K, hK, N₁, hsource⟩ := exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk_all_pos
  have hmajorant : Summable (fun n : ℕ => K / (ε : ℝ) *
      Real.exp (-((1 / 120 : ℝ) * Real.sqrt (Real.log n))) / n) := by
    simpa only [mul_div_assoc] using
      (GaloisForLFunctions.HTGeometry.summable_exp_neg_sqrt_log_div
        (by norm_num : (0 : ℝ) < 1 / 120)).mul_left (K / (ε : ℝ))
  have hbound : ∀ᶠ n : ℕ in atTop, poleTraceEnvelope ε n ≤ K / (ε : ℝ) *
      Real.exp (-((1 / 120 : ℝ) * Real.sqrt (Real.log n))) / n := by
    filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop 1,
      tendsto_natCast_atTop_atTop.eventually (eventually_vk_conditions one_pos 0)] with n hn h1 hvk
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hA := hsource ε ε.property.1 ε.property.2.le n hn
    rw [weightCenteredPrefix_pmPowerDamped_eq] at hA
    have hs := hvk.2.2.2.2.1
    rw [log_vkHeight] at hs
    have he : Real.exp (-(vkKappa * vkScale n / 240)) ≤
        Real.exp (-((1 / 120 : ℝ) * Real.sqrt (Real.log n))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hp : (n : ℝ) ^ (1 - (ε : ℝ)) * (n : ℝ) ^ ((ε : ℝ) - 2) =
        (n : ℝ)⁻¹ := by
      rw [← Real.rpow_add hn0, show 1 - (ε : ℝ) + ((ε : ℝ) - 2) = -1 by ring,
        Real.rpow_neg_one]
    calc
      poleTraceEnvelope ε n ≤
          (K / (ε : ℝ) * (n : ℝ) ^ (1 - (ε : ℝ)) *
            Real.exp (-(vkKappa * vkScale n / 240))) * (n : ℝ) ^ ((ε : ℝ) - 2) :=
        mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hn0.le _)
      _ = K / (ε : ℝ) * Real.exp (-(vkKappa * vkScale n / 240)) / n := by
        calc
          _ = K / (ε : ℝ) * Real.exp (-(vkKappa * vkScale n / 240)) *
            ((n : ℝ) ^ (1 - (ε : ℝ)) * (n : ℝ) ^ ((ε : ℝ) - 2)) := by ring
          _ = _ := by rw [hp, div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (div_nonneg hK ε.property.1.le)) hn0.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  rw [← summable_nat_add_iff N]
  refine ((summable_nat_add_iff N).mpr hmajorant).of_norm_bounded fun n => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (poleTraceEnvelope_nonneg ε (n + N))]
  exact hN (n + N) (by omega)

/-- The Mellin-cell trace itself is absolutely summable at the endpoint. -/
theorem summable_receiver_mul_poleMellinCell (ε : SubcriticalDamping) :
    Summable (fun n => pmPowerDampedCenteredDivisorPrefix ε n *
      mellinCell (1 - (ε : ℝ)) n) := by
  have hα : 0 < 1 - (ε : ℝ) := by linarith [ε.property.2]
  refine ((summable_poleTraceEnvelope ε).mul_left (1 - (ε : ℝ))).of_norm_bounded fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
      zero_mul, norm_zero]
    exact mul_nonneg hα.le (poleTraceEnvelope_nonneg ε 0)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mellinCell_nonneg hα hn)]
    calc
      _ ≤ |pmPowerDampedCenteredDivisorPrefix (ε : ℝ) n| *
          ((1 - (ε : ℝ)) * (n : ℝ) ^ (-(1 - (ε : ℝ)) - 1)) :=
        mul_le_mul_of_nonneg_left (mellinCell_bounds hα hn).2 (abs_nonneg _)
      _ = _ := by
        rw [show -(1 - (ε : ℝ)) - 1 = (ε : ℝ) - 2 by ring]
        unfold poleTraceEnvelope
        ring

/-- The source boundary functional at the positive cofactor pole. -/
def actualPoleTrace (ε : ℝ) : ℝ :=
  (∑' n, pmPowerDampedCenteredDivisorPrefix ε n * mellinCell (1 - ε) n) / (1 - ε)

private def traceGap (ε : SubcriticalDamping) (k : ℕ) : ℝ :=
  (ε : ℝ) / ((k + 2 : ℕ) : ℝ)

private def traceApproach (ε : SubcriticalDamping) (k : ℕ) : ℝ :=
  1 - (ε : ℝ) + traceGap ε k

private theorem traceGap_pos (ε : SubcriticalDamping) (k : ℕ) : 0 < traceGap ε k := by
  unfold traceGap
  exact div_pos ε.property.1 (by positivity)

private theorem traceGap_lt (ε : SubcriticalDamping) (k : ℕ) : traceGap ε k < (ε : ℝ) := by
  unfold traceGap
  have hden : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k + 2 by omega)
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [ε.property.1]

private theorem traceApproach_bounds (ε : SubcriticalDamping) (k : ℕ) :
    0 < traceApproach ε k ∧ 1 - (ε : ℝ) < traceApproach ε k ∧ traceApproach ε k < 1 := by
  have hpos := traceGap_pos ε k
  have hlt := traceGap_lt ε k
  unfold traceApproach
  exact ⟨by linarith [ε.property.2], by linarith, by linarith⟩

private theorem tendsto_traceGap_zero (ε : SubcriticalDamping) :
    Tendsto (traceGap ε) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))

private theorem tendsto_traceApproach (ε : SubcriticalDamping) :
    Tendsto (traceApproach ε) atTop (𝓝 (1 - (ε : ℝ))) := by
  simpa only [traceApproach, add_zero] using
    (tendsto_const_nhds.add (tendsto_traceGap_zero ε))

private theorem traceApproach_mellin_bound (ε : SubcriticalDamping) (k n : ℕ) :
    ‖pmPowerDampedCenteredDivisorPrefix ε n * mellinCell (traceApproach ε k) n‖ ≤
      poleTraceEnvelope ε n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
      zero_mul, norm_zero]
    exact poleTraceEnvelope_nonneg ε 0
  · obtain ⟨hσ0, hασ, hσ1⟩ := traceApproach_bounds ε k
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : (n : ℝ) ^ (-traceApproach ε k - 1) ≤ (n : ℝ) ^ ((ε : ℝ) - 2) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hcell : mellinCell (traceApproach ε k) n ≤ (n : ℝ) ^ ((ε : ℝ) - 2) := by
      calc
        _ ≤ traceApproach ε k * (n : ℝ) ^ (-traceApproach ε k - 1) :=
          (mellinCell_bounds hσ0 hn).2
        _ ≤ 1 * (n : ℝ) ^ ((ε : ℝ) - 2) :=
          mul_le_mul hσ1.le hp (Real.rpow_nonneg (Nat.cast_nonneg n) _) zero_le_one
        _ = _ := one_mul _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mellinCell_nonneg hσ0 hn)]
    exact mul_le_mul_of_nonneg_left hcell (abs_nonneg _)

private theorem tendsto_tracePairing (ε : SubcriticalDamping) :
    Tendsto (fun k => ∑' n, pmPowerDampedCenteredDivisorPrefix ε n *
      mellinCell (traceApproach ε k) n) atTop
      (𝓝 (∑' n, pmPowerDampedCenteredDivisorPrefix ε n * mellinCell (1 - (ε : ℝ)) n)) := by
  refine tendsto_tsum_of_dominated_convergence (summable_poleTraceEnvelope ε) (fun n => ?_)
    (Filter.Eventually.of_forall fun k n => traceApproach_mellin_bound ε k n)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero,
      zero_mul]
    exact tendsto_const_nhds
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hpow : ∀ x : ℝ, 0 < x →
        Tendsto (fun k => x ^ (-traceApproach ε k)) atTop (𝓝 (x ^ (-(1 - (ε : ℝ))))) := by
      intro x hx
      simp_rw [Real.rpow_def_of_pos hx]
      exact Real.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_traceApproach ε).neg.const_mul (Real.log x))
    exact ((hpow n hn0).sub (hpow ((n : ℝ) + 1) (by positivity))).const_mul
      (pmPowerDampedCenteredDivisorPrefix (ε : ℝ) n)

private theorem traceDirichletSeries_eq_density (ε : SubcriticalDamping) (k : ℕ) :
    (∑' n : ℕ, pmPowerDampedRealWeight ε n * (n : ℝ) ^ (-traceApproach ε k)) =
      dampedDensity (traceGap ε k) := by
  calc
    _ = ∑' n : ℕ, pmPowerDampedRealWeight (traceGap ε k) n / n := by
      apply tsum_congr
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [pmPowerDampedRealWeight, moebiusReal]
      · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        have he : -(ε : ℝ) + -traceApproach ε k = -traceGap ε k - 1 := by
          unfold traceApproach
          ring
        unfold pmPowerDampedRealWeight
        rw [mul_assoc, ← Real.rpow_add hn0, mul_div_assoc, ← Real.rpow_sub_one hn0.ne', he]
    _ = _ := (hasSum_pmPowerDampedRealWeight_div (traceGap_pos ε k)).tsum_eq

private theorem tracePairing_eq_zeta_density (ε : SubcriticalDamping) (k : ℕ) :
    (∑' n, pmPowerDampedCenteredDivisorPrefix ε n * mellinCell (traceApproach ε k) n) =
      (riemannZeta ((traceApproach ε k : ℝ) : ℂ)).re *
        (dampedDensity (traceGap ε k) - dampedDensity ε) := by
  obtain ⟨hσ0, hασ, hσ1⟩ := traceApproach_bounds ε k
  have h := mellinPairing_eq_zeta_mul ε.property.1
    (pmPowerDampedRealWeight_mem_dampedClass (ε : ℝ)) hσ0 hασ hσ1
  have hmean : (∑' d : ℕ, pmPowerDampedRealWeight ε d / d) = dampedDensity ε :=
    (hasSum_pmPowerDampedRealWeight_div ε.property.1).tsum_eq
  rw [hmean, traceDirichletSeries_eq_density] at h
  simp only [weightCenteredPrefix_pmPowerDamped_eq] at h
  simpa only [Complex.ofReal_re, Complex.re_mul_ofReal] using congrArg Complex.re h

/-- The actual boundary trace equals the coefficient of the forcing's positive power. -/
theorem actualPoleTrace_eq_forcingPowerCoefficient (ε : SubcriticalDamping) :
    actualPoleTrace ε = forcingPowerCoefficient ε := by
  have hgap : Tendsto (traceGap ε) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_traceGap_zero ε,
      Filter.Eventually.of_forall (traceGap_pos ε)⟩
  have hdensity :=
    GaloisForLFunctions.BezoutValuationIncidence.tendsto_pmPowerDampedDivisorDensity_re_zero.comp hgap
  have hne : (((1 - (ε : ℝ) : ℝ)) : ℂ) ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at hr
    linarith [ε.property.1]
  have hz := (differentiableAt_riemannZeta hne).continuousAt.tendsto.comp
    (Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_traceApproach ε))
  have hzr := Complex.continuous_re.continuousAt.tendsto.comp hz
  have hlim := hzr.mul (hdensity.sub (tendsto_const_nhds (x := dampedDensity (ε : ℝ))))
  have hlim' : Tendsto (fun k => ∑' n, pmPowerDampedCenteredDivisorPrefix ε n *
      mellinCell (traceApproach ε k) n) atTop
      (𝓝 ((riemannZeta (((1 - (ε : ℝ) : ℝ)) : ℂ)).re * (0 - dampedDensity ε))) := by
    exact hlim.congr fun k => (tracePairing_eq_zeta_density ε k).symm
  have heq := tendsto_nhds_unique (tendsto_tracePairing ε) hlim'
  rw [actualPoleTrace, heq, forcingPowerCoefficient, subHalfZetaCoeff]
  ring

theorem actualPoleTrace_pos (ε : SubcriticalDamping) : 0 < actualPoleTrace ε := by
  rw [actualPoleTrace_eq_forcingPowerCoefficient]
  exact forcingPowerCoefficient_pos ε

end GaloisForLFunctions.ArithmeticDefectRigidity
