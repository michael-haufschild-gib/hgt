import GaloisForLFunctions.BezoutValuationIncidence.PronicPotentialSelfCancellationAndInteriorGradientConservation
import GaloisForLFunctions.BezoutValuationIncidence.UniformRenormalizedInteriorEnergyRemainder
import GaloisForLFunctions.RHTower.AdmissionBelowHalfDampingAboveTheZeroWidth
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.AdmissionTranslatesZerosWithMultiplicityUpToTheBoundary

/-!
# The Receiver Equivalence and Zero-Width Law in Bézout–Valuation Incidence

In non-circular interior coordinates, the power-damped Möbius receiver admits three formulations at
each damping `ε > 0`:
1. Uniform boundedness of the actual discrete pronic energy `E_T(ε)`
   (`pmPowerDampedDivisorDiscreteEnergy ε T`);
2. Uniform boundedness of the pure-interior pronic energy `E_T^{int}(ε)`
   (`pmBezoutInteriorPronicEnergy ε T`);
3. Strict interior contraction of the Bézout interior martingale `M_T^{int}(ε)` against the
   active-deleted diagonal budget:
   `2 M_T^{int}(ε) + 2 c^{int}(ε) H_T^{comp} ≤ (1 − δ) E_T(ε) + C`.

This module establishes the sharp horizon-by-horizon comparison between `E_T(ε)` and `E_T^{int}(ε)`,
the `O_ε(1)` remainder bound for the non-circular interior conservation law, the pointwise-in-`ε`
equivalence of all receiver formulations, their unconditional admission on the exact zero-width
half-line `ε > Θ − ½`, their common damping rate `Θ − ½`, iterated zero translation with
multiplicity up to the boundary lines `Re ρ = ½ + kε`, and necessary-and-sufficient equivalences
with `RiemannHypothesis`.

## Main results

* **Sharp square-root comparison (`abs_sqrt_pmBezoutInteriorPronicEnergy_sub_sqrt_le_half`,
  `abs_pmBezoutInteriorPronicEnergy_sub_discreteEnergy_le`)**:
  Because `F_ε(n) = F_ε^{int}(n) + I_ε(n)` and the active-pair pronic energy satisfies
  `E_T^{pair}(ε) ≤ ¼`, Cauchy–Schwarz in the pronic `ℓ²` norm gives at every `ε ≥ 0` and `T : ℕ`
  `|\sqrt{E_T^{int}(ε)} − \sqrt{E_T(ε)}| ≤ ½` and
  `|E_T^{int}(ε) − E_T(ε)| ≤ \sqrt{E_T(ε)} + ¼`.
* **Uniform `O_ε(1)` conservation-law remainder
  (`exists_pmBezoutInteriorGradient_add_localImpulse_compensated_bound`,
  `exists_pmBezoutInteriorPronicEnergy_sub_compensated_martingale_le_sqrt_add`)**:
  For every `ε > 0`, the interior gradient plus twice the local-impulse cross sum tracks
  `2 c^{int}(ε) H_T^{comp}` to `O_ε(1)` uniformly in `T ≥ 1`, and `E_T^{int}(ε)` tracks the
  compensated interior bracket `2 M_T^{int}(ε) + 2 c^{int}(ε) H_T^{comp}` up to
  `\sqrt{E_T(ε)} + O_ε(1)`.
* **Pointwise equivalence of the receiver formulations
  (`interiorReceiverDampings_eq_receiverDampings`,
  `strictContractionDampings_eq_receiverDampings`,
  `strictInteriorContractionDampings_eq_receiverDampings`,
  `compensatedMartingaleDampings_eq_receiverDampings`)**:
  At every `ε > 0`, bounded `E_T(ε)`, bounded `E_T^{int}(ε)`, strict contraction against `E_T(ε)`,
  strict contraction against `E_T^{int}(ε)`, and boundedness of the compensated interior bracket
  are equivalent.
* **Exact zero-width admission and damping rate
  (`exists_pmBezoutInteriorPronicEnergy_budget_of_zetaZeroAbscissa_lt`,
  `exists_pmInterior_strict_contraction_of_zetaZeroAbscissa_lt`,
  `sInf_derivedSet_interiorReceiverDampings_eq_zetaZeroAbscissa_sub_half`)**:
  Every receiver formulation holds unconditionally for all `ε > Θ − ½`, and the infimum of the
  accumulation points of each admissible damping set is `Θ − ½`.
* **Iterated zero translation with multiplicity and full `RiemannHypothesis` equivalences
  (`analyticOrderAt_le_analyticOrderAt_sub_nat_mul_of_mem_interiorReceiverDampings`,
  `riemannHypothesis_iff_forall_pos_pmBezoutInteriorPronicEnergy_bounded`,
  `riemannHypothesis_iff_cofinal_pmBezoutInteriorPronicEnergy_bounded`,
  `riemannHypothesis_iff_forall_pos_pmInterior_strict_contraction`,
  `riemannHypothesis_iff_cofinal_pmInterior_strict_contraction_iff`)**.
-/

open Complex Set Filter Topology MeasureTheory Finset
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin
open RHTower RHTower.Sieve GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

/-! ## §1. Sharp Coefficient-One Square-Root Comparison Between `E_T(ε)` and `E_T^{int}(ε)` -/

/-- `pmPowerDampedDivisorDiscreteEnergy ε T` is non-negative for all `ε : ℝ` and `T : ℕ`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_nonneg (ε : ℝ) (T : ℕ) :
    0 ≤ pmPowerDampedDivisorDiscreteEnergy ε T := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq]
  exact sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Exact pronic polarization identity between the actual discrete energy `E_T(ε)` and the
pure-interior pronic energy `E_T^{int}(ε)`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_sub_interiorPronic_eq (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T - pmBezoutInteriorPronicEnergy ε T =
      2 * (∑ n ∈ Icc 1 T,
        (pmBezoutInteriorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) *
          (addDiff (pmActiveSawtoothComponent ε) n / Real.sqrt (pronicSeq n : ℝ))) +
      pmActivePairPronicEnergy ε T := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq]
  unfold pmBezoutInteriorPronicEnergy pmActivePairPronicEnergy
  rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  have hpr : (0 : ℝ) ≤ (pronicSeq n : ℝ) := Nat.cast_nonneg _
  have hsq : Real.sqrt (pronicSeq n : ℝ) * Real.sqrt (pronicSeq n : ℝ) = (pronicSeq n : ℝ) :=
    Real.mul_self_sqrt hpr
  have hsplit := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
  rw [div_mul_div_comm, hsq, hsplit]
  ring

/-- Cauchy–Schwarz bound on the pronic cross-pairing between the pure-interior prefix and the
active-pair impulse. -/
theorem abs_sum_interior_mul_activePair_le
    {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    |∑ n ∈ Icc 1 T,
      (pmBezoutInteriorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) *
        (addDiff (pmActiveSawtoothComponent ε) n / Real.sqrt (pronicSeq n : ℝ))| ≤
      (1 / 2) * Real.sqrt (pmBezoutInteriorPronicEnergy ε T) := by
  set S := ∑ n ∈ Icc 1 T,
    (pmBezoutInteriorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) *
      (addDiff (pmActiveSawtoothComponent ε) n / Real.sqrt (pronicSeq n : ℝ))
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 T)
    (fun n => pmBezoutInteriorPrefix ε n / Real.sqrt (pronicSeq n : ℝ))
    (fun n => addDiff (pmActiveSawtoothComponent ε) n / Real.sqrt (pronicSeq n : ℝ))
  have h1 : (∑ n ∈ Icc 1 T,
      (pmBezoutInteriorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) ^ 2) =
      pmBezoutInteriorPronicEnergy ε T := by
    unfold pmBezoutInteriorPronicEnergy
    refine sum_congr rfl fun n _ => ?_
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h2 : (∑ n ∈ Icc 1 T,
      (addDiff (pmActiveSawtoothComponent ε) n / Real.sqrt (pronicSeq n : ℝ)) ^ 2) =
      pmActivePairPronicEnergy ε T := by
    unfold pmActivePairPronicEnergy
    refine sum_congr rfl fun n _ => ?_
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [h1, h2] at hcs
  have hpair := (pmActivePairPronicEnergy_bounds hε T).2
  have hint0 := pmBezoutInteriorPronicEnergy_nonneg ε T
  have hS2 : S ^ 2 ≤ ((1 / 2 : ℝ) * Real.sqrt (pmBezoutInteriorPronicEnergy ε T)) ^ 2 := by
    calc S ^ 2 ≤ pmBezoutInteriorPronicEnergy ε T * pmActivePairPronicEnergy ε T := hcs
      _ ≤ pmBezoutInteriorPronicEnergy ε T * (1 / 4) :=
          mul_le_mul_of_nonneg_left hpair hint0
      _ = ((1 / 2 : ℝ) * Real.sqrt (pmBezoutInteriorPronicEnergy ε T)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hint0]; ring
  have hsqrt := Real.sqrt_le_sqrt hS2
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at hsqrt

/-- Cauchy–Schwarz bound on the pronic cross-pairing between the centered prefix and the
active-pair impulse. -/
theorem abs_sum_centered_mul_activePair_le
    {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    |∑ n ∈ Icc 1 T,
      (pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) *
        (addDiff (pmActiveSawtoothComponent ε) n / Real.sqrt (pronicSeq n : ℝ))| ≤
      (1 / 2) * Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) := by
  set S := ∑ n ∈ Icc 1 T,
    (pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) *
      (addDiff (pmActiveSawtoothComponent ε) n / Real.sqrt (pronicSeq n : ℝ))
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 T)
    (fun n => pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (pronicSeq n : ℝ))
    (fun n => addDiff (pmActiveSawtoothComponent ε) n / Real.sqrt (pronicSeq n : ℝ))
  have h1 : (∑ n ∈ Icc 1 T,
      (pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) ^ 2) =
      pmPowerDampedDivisorDiscreteEnergy ε T := by
    rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq]
    refine sum_congr rfl fun n _ => ?_
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h2 : (∑ n ∈ Icc 1 T,
      (addDiff (pmActiveSawtoothComponent ε) n / Real.sqrt (pronicSeq n : ℝ)) ^ 2) =
      pmActivePairPronicEnergy ε T := by
    unfold pmActivePairPronicEnergy
    refine sum_congr rfl fun n _ => ?_
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [h1, h2] at hcs
  have hpair := (pmActivePairPronicEnergy_bounds hε T).2
  have hE0 := pmPowerDampedDivisorDiscreteEnergy_nonneg ε T
  have hS2 : S ^ 2 ≤ ((1 / 2 : ℝ) * Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T)) ^ 2 := by
    calc S ^ 2 ≤ pmPowerDampedDivisorDiscreteEnergy ε T * pmActivePairPronicEnergy ε T := hcs
      _ ≤ pmPowerDampedDivisorDiscreteEnergy ε T * (1 / 4) :=
          mul_le_mul_of_nonneg_left hpair hE0
      _ = ((1 / 2 : ℝ) * Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hE0]; ring
  have hsqrt := Real.sqrt_le_sqrt hS2
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at hsqrt

/-- **Coefficient-One Upper Bound on `E_T(ε)` by `E_T^{int}(ε)`**:
`E_T(ε) ≤ E_T^{int}(ε) + \sqrt{E_T^{int}(ε)} + ¼ = (\sqrt{E_T^{int}(ε)} + ½)²`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_le_interiorPronic_add_sqrt_add_quarter
    {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T ≤
      pmBezoutInteriorPronicEnergy ε T +
        Real.sqrt (pmBezoutInteriorPronicEnergy ε T) + 1 / 4 := by
  have hpol := pmPowerDampedDivisorDiscreteEnergy_sub_interiorPronic_eq ε T
  have hcs := (abs_le.mp (abs_sum_interior_mul_activePair_le hε T)).2
  have hpair := (pmActivePairPronicEnergy_bounds hε T).2
  linarith

/-- **Coefficient-One Upper Bound on `E_T^{int}(ε)` by `E_T(ε)`**:
`E_T^{int}(ε) ≤ E_T(ε) + \sqrt{E_T(ε)} + ¼ = (\sqrt{E_T(ε)} + ½)²`. -/
theorem pmBezoutInteriorPronicEnergy_le_discreteEnergy_add_sqrt_add_quarter
    {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    pmBezoutInteriorPronicEnergy ε T ≤
      pmPowerDampedDivisorDiscreteEnergy ε T +
        Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1 / 4 := by
  have hpol : pmBezoutInteriorPronicEnergy ε T - pmPowerDampedDivisorDiscreteEnergy ε T =
      -2 * (∑ n ∈ Icc 1 T,
        (pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) *
          (addDiff (pmActiveSawtoothComponent ε) n / Real.sqrt (pronicSeq n : ℝ))) +
      pmActivePairPronicEnergy ε T := by
    rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq]
    unfold pmBezoutInteriorPronicEnergy pmActivePairPronicEnergy
    rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    have hpr : (0 : ℝ) ≤ (pronicSeq n : ℝ) := Nat.cast_nonneg _
    have hsq : Real.sqrt (pronicSeq n : ℝ) * Real.sqrt (pronicSeq n : ℝ) = (pronicSeq n : ℝ) :=
      Real.mul_self_sqrt hpr
    have hsplit := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
    have hI : pmBezoutInteriorPrefix ε n =
        pmPowerDampedCenteredDivisorPrefix ε n - addDiff (pmActiveSawtoothComponent ε) n := by
      linarith [hsplit]
    rw [div_mul_div_comm, hsq, hI]
    ring
  have hcs := (abs_le.mp (abs_sum_centered_mul_activePair_le hε T)).1
  have hpair := (pmActivePairPronicEnergy_bounds hε T).2
  linarith

/-- **Sharp Square-Root Comparison (`abs_sqrt_pmBezoutInteriorPronicEnergy_sub_sqrt_le_half`):**
At every damping `ε ≥ 0` and horizon `T : ℕ`, the square roots of the pure-interior pronic energy
and the actual discrete energy differ by at most `½`:
`|\sqrt{E_T^{int}(ε)} − \sqrt{E_T(ε)}| ≤ ½`. -/
theorem abs_sqrt_pmBezoutInteriorPronicEnergy_sub_sqrt_le_half
    {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    |Real.sqrt (pmBezoutInteriorPronicEnergy ε T) -
      Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T)| ≤ 1 / 2 := by
  have hE0 := pmPowerDampedDivisorDiscreteEnergy_nonneg ε T
  have hint0 := pmBezoutInteriorPronicEnergy_nonneg ε T
  have h1 : pmBezoutInteriorPronicEnergy ε T ≤
      (Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1 / 2) ^ 2 := by
    calc pmBezoutInteriorPronicEnergy ε T
        ≤ pmPowerDampedDivisorDiscreteEnergy ε T +
            Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1 / 4 :=
          pmBezoutInteriorPronicEnergy_le_discreteEnergy_add_sqrt_add_quarter hε T
      _ = (Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1 / 2) ^ 2 := by
          rw [add_sq, Real.sq_sqrt hE0]; ring
  have h2 : pmPowerDampedDivisorDiscreteEnergy ε T ≤
      (Real.sqrt (pmBezoutInteriorPronicEnergy ε T) + 1 / 2) ^ 2 := by
    calc pmPowerDampedDivisorDiscreteEnergy ε T
        ≤ pmBezoutInteriorPronicEnergy ε T +
            Real.sqrt (pmBezoutInteriorPronicEnergy ε T) + 1 / 4 :=
          pmPowerDampedDivisorDiscreteEnergy_le_interiorPronic_add_sqrt_add_quarter hε T
      _ = (Real.sqrt (pmBezoutInteriorPronicEnergy ε T) + 1 / 2) ^ 2 := by
          rw [add_sq, Real.sq_sqrt hint0]; ring
  have hs1 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (by positivity)] at hs1
  have hs2 := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq (by positivity)] at hs2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Sharp Energy Difference Bound (`abs_pmBezoutInteriorPronicEnergy_sub_discreteEnergy_le`):**
For every `ε ≥ 0` and `T : ℕ`,
`|E_T^{int}(ε) − E_T(ε)| ≤ \sqrt{E_T(ε)} + ¼`. -/
theorem abs_pmBezoutInteriorPronicEnergy_sub_discreteEnergy_le
    {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    |pmBezoutInteriorPronicEnergy ε T - pmPowerDampedDivisorDiscreteEnergy ε T| ≤
      Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1 / 4 := by
  have h1 := pmBezoutInteriorPronicEnergy_le_discreteEnergy_add_sqrt_add_quarter hε T
  have hcs := (abs_le.mp (abs_sum_centered_mul_activePair_le hε T)).2
  have hpair0 := (pmActivePairPronicEnergy_bounds hε T).1
  have hrev : pmPowerDampedDivisorDiscreteEnergy ε T - pmBezoutInteriorPronicEnergy ε T =
      2 * (∑ n ∈ Icc 1 T,
        (pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) *
          (addDiff (pmActiveSawtoothComponent ε) n / Real.sqrt (pronicSeq n : ℝ))) -
      pmActivePairPronicEnergy ε T := by
    rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq]
    unfold pmBezoutInteriorPronicEnergy pmActivePairPronicEnergy
    rw [← sum_sub_distrib, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    have hpr : (0 : ℝ) ≤ (pronicSeq n : ℝ) := Nat.cast_nonneg _
    have hsq : Real.sqrt (pronicSeq n : ℝ) * Real.sqrt (pronicSeq n : ℝ) = (pronicSeq n : ℝ) :=
      Real.mul_self_sqrt hpr
    have hsplit := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
    have hI : pmBezoutInteriorPrefix ε n =
        pmPowerDampedCenteredDivisorPrefix ε n - addDiff (pmActiveSawtoothComponent ε) n := by
      linarith [hsplit]
    rw [div_mul_div_comm, hsq, hI]
    ring
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ## §2. Uniform `O_ε(1)` Conservation-Law Remainder and Interior Martingale Tracking -/

/-- **Unconditional `O_ε(1)` Remainder for the Non-Circular Interior Gradient + Local-Impulse Law:**
For every `ε > 0`, there exists `C ≥ 0` such that for all `T ≥ 1`,
`|(Grad_T(ε) + 2 · Local_T(ε)) − 2 c^{int}(ε) H_T^{comp}| ≤ C`. -/
theorem exists_pmBezoutInteriorGradient_add_localImpulse_compensated_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, 1 ≤ T →
      |(pmBezoutInteriorGradientSum ε T + 2 * pmBezoutLocalImpulseCrossSum ε T) -
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T| ≤ C := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_pmActiveDeletedCovarianceDiagonal_compensated_bound hε
  obtain ⟨C₂, hC₂, h₂⟩ := exists_pmPredecessorPeak_compensated_bound hε
  refine ⟨C₁ + 2 * C₂ + 1 / 4 + |pmInteriorActivePotential ε 1|, by positivity, fun T hT => ?_⟩
  have hcons :=
    pmBezoutInteriorGradient_add_two_mul_localImpulse_eq_activeDeleted_add_predecessorPeak ε hT
  have hdrift := pmInteriorLogCounterterm_eq_half_shiftedCovariance_add_predecessorPeak ε
  have hrew :
      (pmBezoutInteriorGradientSum ε T + 2 * pmBezoutLocalImpulseCrossSum ε T) -
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T =
      (pmActiveDeletedCovarianceDiagonal ε T -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T) +
      2 * (pmPredecessorPeakMartingaleSum ε T -
        pmPredecessorPeakLogDrift ε * pmCompensatedHarmonicSum T) -
      pmActivePairPronicEnergy ε T -
      pmInteriorActivePotential ε 1 * (1 - 1 / ((T : ℝ) + 1)) := by
    rw [hcons, ← hdrift]
    ring
  rw [hrew]
  have hpr := pmActivePairPronicEnergy_bounds hε.le T
  have h1T0 : 0 ≤ 1 - 1 / ((T : ℝ) + 1) := by
    have : (1 : ℝ) / ((T : ℝ) + 1) ≤ 1 :=
      div_le_self zero_le_one (by linarith [Nat.cast_nonneg (α := ℝ) T])
    linarith
  have h1T1 : 1 - 1 / ((T : ℝ) + 1) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
    linarith
  obtain ⟨hA_low, hA_high⟩ := abs_le.mp (h₁ T)
  obtain ⟨hB_low, hB_high⟩ := abs_le.mp (h₂ T)
  have hpot_abs :
      |pmInteriorActivePotential ε 1 * (1 - 1 / ((T : ℝ) + 1))| ≤
        |pmInteriorActivePotential ε 1| := by
    rw [abs_mul, abs_of_nonneg h1T0]
    exact mul_le_of_le_one_right (abs_nonneg _) h1T1
  obtain ⟨hpot_low, hpot_high⟩ := abs_le.mp hpot_abs
  exact abs_le.mpr ⟨by linarith [hpr.1, hpr.2], by linarith [hpr.1, hpr.2]⟩

/-- **Unconditional Square-Root + `O_ε(1)` Tracking Between `E_T^{int}(ε)` and the Compensated
Interior Martingale Bracket:**
For every `ε > 0`, there exists `C ≥ 0` such that for all `T : ℕ`,
`|pmBezoutInteriorPronicEnergy ε T −
  (2 * pmBezoutInteriorMartingaleSum ε T + 2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T)| ≤
  Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + C`. -/
theorem exists_pmBezoutInteriorPronicEnergy_sub_compensated_martingale_le_sqrt_add
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |pmBezoutInteriorPronicEnergy ε T -
        (2 * pmBezoutInteriorMartingaleSum ε T +
          2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T)| ≤
        Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + C := by
  obtain ⟨B, hB0, hB⟩ := exists_pmBezoutInterior_compensated_energy_bound hε
  refine ⟨B + 1 / 4, by positivity, fun T => ?_⟩
  have h1 := abs_pmBezoutInteriorPronicEnergy_sub_discreteEnergy_le hε.le T
  have h2 := hB T
  obtain ⟨h1_low, h1_high⟩ := abs_le.mp h1
  obtain ⟨h2_low, h2_high⟩ := abs_le.mp h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ## §3. Pointwise Equivalence of All Receiver Formulations of §7.1 -/

/-- The set of dampings `ε > 0` at which the pure-interior pronic energy `E_T^{int}(ε)` is
uniformly bounded across all horizons `T : ℕ`. -/
def interiorReceiverDampings : Set ℝ :=
  {ε : ℝ | 0 < ε ∧ ∃ B : ℝ, ∀ T : ℕ, pmBezoutInteriorPronicEnergy ε T ≤ B}

/-- The set of dampings `ε > 0` at which the Bézout interior martingale satisfies strict interior
contraction against `E_T(ε)`. -/
def strictContractionDampings : Set ℝ :=
  {ε : ℝ | 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ T : ℕ,
    2 * pmBezoutInteriorMartingaleSum ε T +
      2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤
      (1 - δ) * pmPowerDampedDivisorDiscreteEnergy ε T + C}

/-- The set of dampings `ε > 0` at which the Bézout interior martingale satisfies strict interior
contraction against the pure-interior pronic energy `E_T^{int}(ε)` itself. -/
def strictInteriorContractionDampings : Set ℝ :=
  {ε : ℝ | 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ T : ℕ,
    2 * pmBezoutInteriorMartingaleSum ε T +
      2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤
      (1 - δ) * pmBezoutInteriorPronicEnergy ε T + C}

/-- The set of dampings `ε > 0` at which the compensated interior bracket
`2 M_T^{int}(ε) + 2 c^{int}(ε) H_T^{comp}` is uniformly bounded above across all horizons `T : ℕ`. -/
def compensatedMartingaleDampings : Set ℝ :=
  {ε : ℝ | 0 < ε ∧ ∃ B : ℝ, ∀ T : ℕ,
    2 * pmBezoutInteriorMartingaleSum ε T +
      2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤ B}

/-- **Equivalence between bounded actual energy and bounded pure-interior pronic energy.** -/
theorem exists_pmBezoutInteriorPronicEnergy_budget_iff
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∃ B : ℝ, ∀ T : ℕ, pmBezoutInteriorPronicEnergy ε T ≤ B) ↔
      (∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨2 * B + 1 / 2, fun T => ?_⟩
    exact (pmPowerDampedDivisorDiscreteEnergy_le_two_mul_interiorPronic_add_half hε T).trans
      (by linarith [hB T])
  · rintro ⟨B, hB⟩
    refine ⟨2 * B + 1 / 2, fun T => ?_⟩
    exact (pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half hε T).trans
      (by linarith [hB T])

/-- **Equivalence between bounded compensated interior bracket and bounded actual energy.** -/
theorem exists_compensated_pmBezoutInteriorMartingale_bound_iff
    {ε : ℝ} (hε : 0 < ε) :
    (∃ B : ℝ, ∀ T : ℕ,
      2 * pmBezoutInteriorMartingaleSum ε T +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤ B) ↔
      (∃ K : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ K) := by
  obtain ⟨C, _, hC⟩ := exists_pmBezoutInterior_compensated_energy_bound hε
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + C, fun T => ?_⟩
    have hlow := (abs_le.mp (hC T)).1
    linarith [hB T]
  · rintro ⟨K, hK⟩
    refine ⟨K + C, fun T => ?_⟩
    have hhigh := (abs_le.mp (hC T)).2
    linarith [hK T]

/-- **Equivalence between strict interior contraction against `E_T^{int}(ε)` and bounded actual
energy.** -/
theorem pmInterior_strict_interior_contraction_iff_bounded_energy
    {ε : ℝ} (hε : 0 < ε) :
    (∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ T : ℕ,
      2 * pmBezoutInteriorMartingaleSum ε T +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤
        (1 - δ) * pmBezoutInteriorPronicEnergy ε T + C) ↔
      (∃ K : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ K) := by
  obtain ⟨B, _, hB⟩ := exists_pmBezoutInterior_compensated_energy_bound hε
  constructor
  · rintro ⟨δ, hδ, C, hC⟩
    by_cases hδ1 : 1 ≤ δ
    · refine ⟨max C 0 + B, fun T => ?_⟩
      have hlow := (abs_le.mp (hB T)).1
      have hnonpos : (1 - δ) * pmBezoutInteriorPronicEnergy ε T ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (pmBezoutInteriorPronicEnergy_nonneg ε T)
      have hT := hC T
      have hCmax : C ≤ max C 0 := le_max_left _ _
      linarith
    · rw [not_le] at hδ1
      have h1δ : 0 < 1 - δ := by linarith
      refine ⟨(C + B + (1 - δ) * (1 / (2 * δ) + 1 / 4)) / (δ / 2), fun T => ?_⟩
      have hlow := (abs_le.mp (hB T)).1
      have hE0 := pmPowerDampedDivisorDiscreteEnergy_nonneg ε T
      have hyoung : Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) ≤
          (δ / 2) * pmPowerDampedDivisorDiscreteEnergy ε T + 1 / (2 * δ) := by
        have hsq : 0 ≤ (Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) - 1 / δ) ^ 2 :=
          sq_nonneg _
        have hexp : (Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) - 1 / δ) ^ 2 =
            pmPowerDampedDivisorDiscreteEnergy ε T -
              (2 / δ) * Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1 / δ ^ 2 := by
          rw [sub_sq, Real.sq_sqrt hE0]; ring
        have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ δ / 2)
        rw [mul_zero, hexp] at hmul
        have hrew : (δ / 2) * (pmPowerDampedDivisorDiscreteEnergy ε T -
            (2 / δ) * Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1 / δ ^ 2) =
            (δ / 2) * pmPowerDampedDivisorDiscreteEnergy ε T -
              Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1 / (2 * δ) := by
          field_simp; ring
        linarith
      have hint_le : pmBezoutInteriorPronicEnergy ε T ≤
          (1 + δ / 2) * pmPowerDampedDivisorDiscreteEnergy ε T + (1 / (2 * δ) + 1 / 4) := by
        have hstep := pmBezoutInteriorPronicEnergy_le_discreteEnergy_add_sqrt_add_quarter hε.le T
        linarith
      have hmul_int : (1 - δ) * pmBezoutInteriorPronicEnergy ε T ≤
          (1 - δ) * ((1 + δ / 2) * pmPowerDampedDivisorDiscreteEnergy ε T +
            (1 / (2 * δ) + 1 / 4)) :=
        mul_le_mul_of_nonneg_left hint_le h1δ.le
      have hprod : (1 - δ) * (1 + δ / 2) ≤ 1 - δ / 2 := by nlinarith [sq_nonneg δ]
      have hprod_E : (1 - δ) * (1 + δ / 2) * pmPowerDampedDivisorDiscreteEnergy ε T ≤
          (1 - δ / 2) * pmPowerDampedDivisorDiscreteEnergy ε T :=
        mul_le_mul_of_nonneg_right hprod hE0
      have hT := hC T
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < δ / 2)).mpr
      linarith
  · rintro ⟨K, hK⟩
    refine ⟨1, by norm_num, K + B, fun T => ?_⟩
    have hhigh := (abs_le.mp (hB T)).2
    linarith [hK T]

/-- **All four interior damping sets coincide with `receiverDampings`.** -/
theorem interiorReceiverDampings_eq_receiverDampings :
    interiorReceiverDampings = receiverDampings := by
  ext ε
  simp only [interiorReceiverDampings, receiverDampings, mem_setOf_eq]
  exact and_congr_right fun hε => exists_pmBezoutInteriorPronicEnergy_budget_iff hε.le

theorem strictContractionDampings_eq_receiverDampings :
    strictContractionDampings = receiverDampings := by
  ext ε
  simp only [strictContractionDampings, receiverDampings, mem_setOf_eq]
  exact and_congr_right fun hε => pmInterior_strict_contraction_iff_bounded_energy hε

theorem strictInteriorContractionDampings_eq_receiverDampings :
    strictInteriorContractionDampings = receiverDampings := by
  ext ε
  simp only [strictInteriorContractionDampings, receiverDampings, mem_setOf_eq]
  exact and_congr_right fun hε => pmInterior_strict_interior_contraction_iff_bounded_energy hε

theorem compensatedMartingaleDampings_eq_receiverDampings :
    compensatedMartingaleDampings = receiverDampings := by
  ext ε
  simp only [compensatedMartingaleDampings, receiverDampings, mem_setOf_eq]
  exact and_congr_right fun hε => exists_compensated_pmBezoutInteriorMartingale_bound_iff hε

/-- **Complete 5-Way Pointwise Equivalence of the Receiver at Fixed `ε > 0`:**
At every `ε > 0`, membership in `receiverDampings`, `interiorReceiverDampings`,
`strictContractionDampings`, `strictInteriorContractionDampings`, and
`compensatedMartingaleDampings` are mutually equivalent. -/
theorem mem_receiverDampings_iff_all_interior_forms {ε : ℝ} :
    (ε ∈ receiverDampings ↔ ε ∈ interiorReceiverDampings) ∧
    (ε ∈ receiverDampings ↔ ε ∈ strictContractionDampings) ∧
    (ε ∈ receiverDampings ↔ ε ∈ strictInteriorContractionDampings) ∧
    (ε ∈ receiverDampings ↔ ε ∈ compensatedMartingaleDampings) := by
  rw [interiorReceiverDampings_eq_receiverDampings,
    strictContractionDampings_eq_receiverDampings,
    strictInteriorContractionDampings_eq_receiverDampings,
    compensatedMartingaleDampings_eq_receiverDampings]
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ## §4. Exact Zero-Width Admission `(Θ − ½, ∞)` and Damping Rate `Θ − ½` -/

/-- **Unconditional Admission of the Pure-Interior Pronic Energy Above the Zero Width `Θ − ½`:**
For every `ε > Θ − ½`, there exists `B ≥ 0` such that `E_T^{int}(ε) ≤ B` for all `T : ℕ`.
This upgrades `exists_pmBezoutInteriorPronicEnergy_budget_of_half_le` (`ε ≥ ½`) and
`LittlewoodAdmitsTheReceiverAboveHalfTheZeroAbscissa` (`ε > Θ/2`) to the exact zero-width
half-line `ε > Θ − ½`. -/
theorem exists_pmBezoutInteriorPronicEnergy_budget_of_zetaZeroAbscissa_lt
    {ε : ℝ} (hΘ : zetaZeroAbscissa < 1 / 2 + ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℕ, pmBezoutInteriorPronicEnergy ε T ≤ B := by
  have hmem := mem_receiverDampings_of_zetaZeroAbscissa_lt hΘ
  obtain ⟨B, hB⟩ := (exists_pmBezoutInteriorPronicEnergy_budget_iff hmem.1.le).mpr hmem.2
  refine ⟨max B 0, le_max_right _ _, fun T => (hB T).trans (le_max_left _ _)⟩

theorem mem_interiorReceiverDampings_of_zetaZeroAbscissa_lt
    {ε : ℝ} (hΘ : zetaZeroAbscissa < 1 / 2 + ε) :
    ε ∈ interiorReceiverDampings := by
  rw [interiorReceiverDampings_eq_receiverDampings]
  exact mem_receiverDampings_of_zetaZeroAbscissa_lt hΘ

/-- **Unconditional Strict Interior Contraction Above the Zero Width `Θ − ½`:**
For every `ε > Θ − ½`, there exist `δ > 0` and `C ≥ 0` such that for all `T : ℕ`,
`2 M_T^{int}(ε) + 2 c^{int}(ε) H_T^{comp} ≤ (1 − δ) E_T(ε) + C`. -/
theorem exists_pmInterior_strict_contraction_of_zetaZeroAbscissa_lt
    {ε : ℝ} (hΘ : zetaZeroAbscissa < 1 / 2 + ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ T : ℕ,
      2 * pmBezoutInteriorMartingaleSum ε T +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤
        (1 - δ) * pmPowerDampedDivisorDiscreteEnergy ε T + C := by
  have hmem : ε ∈ strictContractionDampings := by
    rw [strictContractionDampings_eq_receiverDampings]
    exact mem_receiverDampings_of_zetaZeroAbscissa_lt hΘ
  exact hmem.2

/-- **Unconditional Strict Interior Contraction Against `E_T^{int}(ε)` Above the Zero Width:**
For every `ε > Θ − ½`, there exist `δ > 0` and `C : ℝ` such that for all `T : ℕ`,
`2 M_T^{int}(ε) + 2 c^{int}(ε) H_T^{comp} ≤ (1 − δ) E_T^{int}(ε) + C`. -/
theorem exists_pmInterior_strict_interior_contraction_of_zetaZeroAbscissa_lt
    {ε : ℝ} (hΘ : zetaZeroAbscissa < 1 / 2 + ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ T : ℕ,
      2 * pmBezoutInteriorMartingaleSum ε T +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤
        (1 - δ) * pmBezoutInteriorPronicEnergy ε T + C := by
  have hmem : ε ∈ strictInteriorContractionDampings := by
    rw [strictInteriorContractionDampings_eq_receiverDampings]
    exact mem_receiverDampings_of_zetaZeroAbscissa_lt hΘ
  exact hmem.2

/-- **Unconditional Boundedness of the Compensated Interior Martingale Bracket Above the Zero Width:**
For every `ε > Θ − ½`, there exists `B ≥ 0` such that for all `T : ℕ`,
`2 M_T^{int}(ε) + 2 c^{int}(ε) H_T^{comp} ≤ B`. -/
theorem exists_compensated_pmBezoutInteriorMartingale_bound_of_zetaZeroAbscissa_lt
    {ε : ℝ} (hΘ : zetaZeroAbscissa < 1 / 2 + ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℕ,
      2 * pmBezoutInteriorMartingaleSum ε T +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤ B := by
  have hmem : ε ∈ compensatedMartingaleDampings := by
    rw [compensatedMartingaleDampings_eq_receiverDampings]
    exact mem_receiverDampings_of_zetaZeroAbscissa_lt hΘ
  obtain ⟨B, hB⟩ := hmem.2
  refine ⟨max B 0, le_max_right _ _, fun T => (hB T).trans (le_max_left _ _)⟩

/-- **The Interior Receiver Damping Rate Equals the Zero Width `Θ − ½`.** -/
theorem sInf_derivedSet_interiorReceiverDampings_eq_zetaZeroAbscissa_sub_half :
    sInf (derivedSet interiorReceiverDampings) = zetaZeroAbscissa - 1 / 2 := by
  rw [interiorReceiverDampings_eq_receiverDampings, ← receiverDampingRate,
    receiverDampingRate_eq_zetaZeroAbscissa_sub_half]

/-- **The Strict Interior Contraction Damping Rate Equals the Zero Width `Θ − ½`.** -/
theorem sInf_derivedSet_strictContractionDampings_eq_zetaZeroAbscissa_sub_half :
    sInf (derivedSet strictContractionDampings) = zetaZeroAbscissa - 1 / 2 := by
  rw [strictContractionDampings_eq_receiverDampings, ← receiverDampingRate,
    receiverDampingRate_eq_zetaZeroAbscissa_sub_half]

/-- **The Compensated Martingale Damping Rate Equals the Zero Width `Θ − ½`.** -/
theorem sInf_derivedSet_compensatedMartingaleDampings_eq_zetaZeroAbscissa_sub_half :
    sInf (derivedSet compensatedMartingaleDampings) = zetaZeroAbscissa - 1 / 2 := by
  rw [compensatedMartingaleDampings_eq_receiverDampings, ← receiverDampingRate,
    receiverDampingRate_eq_zetaZeroAbscissa_sub_half]

/-! ## §5. Iterated Zero Translation with Multiplicity Up to the Boundary -/

/-- **Iterated Zero Translation with Multiplicity Up to the Boundary:**
If `ε ∈ receiverDampings` with `ε ≤ ½`, then for every `k : ℕ` and every `ρ : ℂ` with
`½ + kε ≤ Re ρ < 1`,
`analyticOrderAt riemannZeta ρ ≤ analyticOrderAt riemannZeta (ρ − kε)`. -/
theorem analyticOrderAt_le_analyticOrderAt_sub_nat_mul_of_mem_receiverDampings
    {ε : ℝ} (hε : ε ∈ receiverDampings) (hε1 : ε ≤ 1 / 2) :
    ∀ (k : ℕ) {ρ : ℂ}, 1 / 2 + (k : ℝ) * ε ≤ ρ.re → ρ.re < 1 →
      analyticOrderAt riemannZeta ρ ≤
        analyticOrderAt riemannZeta (ρ - (k : ℂ) * (ε : ℂ))
  | 0, ρ, _, _ => by simp
  | k + 1, ρ, hρ, hρ1 => by
      have hε0 : 0 < ε := hε.1
      have hk_re : 1 / 2 + (k : ℝ) * ε ≤ ρ.re := by
        push_cast at hρ; nlinarith
      have ih := analyticOrderAt_le_analyticOrderAt_sub_nat_mul_of_mem_receiverDampings
        hε hε1 k hk_re hρ1
      set ρ' : ℂ := ρ - (k : ℂ) * (ε : ℂ) with hρ'def
      have hρ're : 1 / 2 + ε ≤ ρ'.re := by
        rw [hρ'def]; simp only [sub_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
          mul_zero, sub_zero]
        push_cast at hρ; linarith
      have hρ'1 : ρ'.re < 1 := by
        rw [hρ'def]; simp only [sub_re, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
          mul_zero, sub_zero]
        have hk0 : (0 : ℝ) ≤ (k : ℝ) * ε := by positivity
        linarith
      have hstep := analyticOrderAt_le_analyticOrderAt_sub_of_mem_receiverDampings
        hε hε1 hρ're hρ'1
      have heq : ρ' - (ε : ℂ) = ρ - ((k + 1 : ℕ) : ℂ) * (ε : ℂ) := by
        rw [hρ'def]; push_cast; ring
      rw [heq] at hstep
      exact ih.trans hstep

/-- **Iterated Zero Translation with Multiplicity from Bounded Pure-Interior Pronic Energy:**
If `ε ∈ interiorReceiverDampings` with `ε ≤ ½`, then for every `k : ℕ` and `ρ : ℂ` with
`½ + kε ≤ Re ρ < 1`, `ord_ρ ζ ≤ ord_{ρ − kε} ζ`. -/
theorem analyticOrderAt_le_analyticOrderAt_sub_nat_mul_of_mem_interiorReceiverDampings
    {ε : ℝ} (hε : ε ∈ interiorReceiverDampings) (hε1 : ε ≤ 1 / 2) (k : ℕ) {ρ : ℂ}
    (hρ : 1 / 2 + (k : ℝ) * ε ≤ ρ.re) (hρ1 : ρ.re < 1) :
    analyticOrderAt riemannZeta ρ ≤
      analyticOrderAt riemannZeta (ρ - (k : ℂ) * (ε : ℂ)) := by
  rw [interiorReceiverDampings_eq_receiverDampings] at hε
  exact analyticOrderAt_le_analyticOrderAt_sub_nat_mul_of_mem_receiverDampings hε hε1 k hρ hρ1

/-- **Iterated Zero Translation with Multiplicity from Strict Interior Contraction:**
If `ε ∈ strictContractionDampings` with `ε ≤ ½`, then for every `k : ℕ` and `ρ : ℂ` with
`½ + kε ≤ Re ρ < 1`, `ord_ρ ζ ≤ ord_{ρ − kε} ζ`. -/
theorem analyticOrderAt_le_analyticOrderAt_sub_nat_mul_of_mem_strictContractionDampings
    {ε : ℝ} (hε : ε ∈ strictContractionDampings) (hε1 : ε ≤ 1 / 2) (k : ℕ) {ρ : ℂ}
    (hρ : 1 / 2 + (k : ℝ) * ε ≤ ρ.re) (hρ1 : ρ.re < 1) :
    analyticOrderAt riemannZeta ρ ≤
      analyticOrderAt riemannZeta (ρ - (k : ℂ) * (ε : ℂ)) := by
  rw [strictContractionDampings_eq_receiverDampings] at hε
  exact analyticOrderAt_le_analyticOrderAt_sub_nat_mul_of_mem_receiverDampings hε hε1 k hρ hρ1

/-! ## §6. Necessary and Sufficient Equivalences with `RiemannHypothesis` -/

/-- **All-Damping Pure-Interior Pronic Energy Equivalence with `RiemannHypothesis`.** -/
theorem riemannHypothesis_iff_forall_pos_pmBezoutInteriorPronicEnergy_bounded :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ T : ℕ, pmBezoutInteriorPronicEnergy ε T ≤ B := by
  constructor
  · intro hRH ε hε
    have hΘ : zetaZeroAbscissa = 1 / 2 := zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr hRH
    obtain ⟨B, _, hB⟩ := exists_pmBezoutInteriorPronicEnergy_budget_of_zetaZeroAbscissa_lt
      (by linarith : zetaZeroAbscissa < 1 / 2 + ε)
    exact ⟨B, hB⟩
  · intro h
    apply riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded
    intro δ hδ
    obtain ⟨B, hB⟩ := h (δ / 2) (by linarith)
    exact ⟨δ / 2, by linarith, by linarith, B, fun T _ => hB T⟩

/-- **Cofinal Pure-Interior Pronic Energy Equivalence with `RiemannHypothesis`.** -/
theorem riemannHypothesis_iff_cofinal_pmBezoutInteriorPronicEnergy_bounded :
    RiemannHypothesis ↔
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
        ∃ B : ℝ, ∀ T : ℕ, pmBezoutInteriorPronicEnergy ε T ≤ B := by
  rw [riemannHypothesis_iff_cofinal_budget]
  exact forall₂_congr fun δ _ => exists_congr fun ε => and_congr_right fun hε =>
    and_congr_right fun _ => (exists_pmBezoutInteriorPronicEnergy_budget_iff hε.le).symm

/-- **All-Damping Strict Interior Contraction Equivalence with `RiemannHypothesis`.** -/
theorem riemannHypothesis_iff_forall_pos_pmInterior_strict_contraction :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ T : ℕ,
        2 * pmBezoutInteriorMartingaleSum ε T +
          2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤
          (1 - δ) * pmPowerDampedDivisorDiscreteEnergy ε T + C := by
  constructor
  · intro hRH ε hε
    have hΘ : zetaZeroAbscissa = 1 / 2 := zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr hRH
    exact exists_pmInterior_strict_contraction_of_zetaZeroAbscissa_lt (by linarith)
  · intro h
    rw [riemannHypothesis_iff_cofinal_budget]
    intro δ₀ hδ₀
    obtain ⟨B, hB⟩ := (pmInterior_strict_contraction_iff_bounded_energy
      (by linarith : 0 < δ₀ / 2)).mp (h (δ₀ / 2) (by linarith))
    exact ⟨δ₀ / 2, by linarith, by linarith, B, hB⟩

/-- **Cofinal Strict Interior Contraction Equivalence with `RiemannHypothesis`.** -/
theorem riemannHypothesis_iff_cofinal_pmInterior_strict_contraction_iff :
    RiemannHypothesis ↔
      ∀ δ₀ : ℝ, 0 < δ₀ → ∃ ε : ℝ, 0 < ε ∧ ε < δ₀ ∧
        ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ T : ℕ,
          2 * pmBezoutInteriorMartingaleSum ε T +
            2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤
            (1 - δ) * pmPowerDampedDivisorDiscreteEnergy ε T + C := by
  rw [riemannHypothesis_iff_cofinal_budget]
  exact forall₂_congr fun δ₀ _ => exists_congr fun ε => and_congr_right fun hε =>
    and_congr_right fun _ => (pmInterior_strict_contraction_iff_bounded_energy hε).symm

/-- **All-Damping Compensated Interior Martingale Equivalence with `RiemannHypothesis`.** -/
theorem riemannHypothesis_iff_forall_pos_compensated_pmBezoutInteriorMartingale_bounded :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ T : ℕ,
        2 * pmBezoutInteriorMartingaleSum ε T +
          2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤ B := by
  constructor
  · intro hRH ε hε
    have hΘ : zetaZeroAbscissa = 1 / 2 := zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr hRH
    obtain ⟨B, _, hB⟩ := exists_compensated_pmBezoutInteriorMartingale_bound_of_zetaZeroAbscissa_lt
      (by linarith : zetaZeroAbscissa < 1 / 2 + ε)
    exact ⟨B, hB⟩
  · intro h
    rw [riemannHypothesis_iff_cofinal_budget]
    intro δ₀ hδ₀
    obtain ⟨B, hB⟩ := (exists_compensated_pmBezoutInteriorMartingale_bound_iff
      (by linarith : 0 < δ₀ / 2)).mp (h (δ₀ / 2) (by linarith))
    exact ⟨δ₀ / 2, by linarith, by linarith, B, hB⟩

#print axioms abs_sqrt_pmBezoutInteriorPronicEnergy_sub_sqrt_le_half
#print axioms abs_pmBezoutInteriorPronicEnergy_sub_discreteEnergy_le
#print axioms exists_pmBezoutInteriorPronicEnergy_sub_compensated_martingale_le_sqrt_add
#print axioms mem_receiverDampings_iff_all_interior_forms
#print axioms exists_pmBezoutInteriorPronicEnergy_budget_of_zetaZeroAbscissa_lt
#print axioms exists_pmInterior_strict_contraction_of_zetaZeroAbscissa_lt
#print axioms sInf_derivedSet_interiorReceiverDampings_eq_zetaZeroAbscissa_sub_half
#print axioms analyticOrderAt_le_analyticOrderAt_sub_nat_mul_of_mem_interiorReceiverDampings
#print axioms riemannHypothesis_iff_forall_pos_pmBezoutInteriorPronicEnergy_bounded
#print axioms riemannHypothesis_iff_forall_pos_pmInterior_strict_contraction

end GaloisForLFunctions.BezoutValuationIncidence
