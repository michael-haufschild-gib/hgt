import GaloisForLFunctions.RHTower.XiHeatCassiniWoldPrimeZetaLaplaceSymbol
import GaloisForLFunctions.RHTower.XiHeatCassiniLogMeshPrimeGapQuadrature

/-!
# Resolvent defect of the Route-T prime-log mesh

The ordered mesh current is a right-endpoint quadrature for the elementary Laplace resolvent.
Subtracting the continuous cell telescope before estimating leaves a second-order exponential
remainder.  On the critical wall its arithmetic majorant is exactly the same normalized
mean-square prime-gap weight independently exposed by the physical growing-profile quadrature.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Scaled right-endpoint resolvent defect on one ordered prime-log cell.  The scaled form remains
meaningful at `s = 0`. -/
def xiHeatCassiniLogMeshLaplaceScaledDefect (s : ℂ) (N : ℕ) : ℂ :=
  xiHeatCassiniOrderedPrimeLaplacePhase N s -
    xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s -
    s * xiHeatCassiniLogMeshLaplaceAtom s N

/-- Adjacent Laplace phases differ by the exact exponential of one log-mesh cell. -/
theorem xiHeatCassiniOrderedPrimeLaplacePhase_eq_succ_mul_exp_gap
    (s : ℂ) (N : ℕ) :
    xiHeatCassiniOrderedPrimeLaplacePhase N s =
      xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s *
        Complex.exp (s * (xiHeatCassiniOrderedPrimeLogGap N : ℂ)) := by
  rw [xiHeatCassiniOrderedPrimeLaplacePhase,
    xiHeatCassiniOrderedPrimeLaplacePhase,
    xiHeatCassiniOrderedPrimeComplexNegativePhase,
    xiHeatCassiniOrderedPrimeComplexNegativePhase, ← Complex.exp_add]
  congr 1
  unfold xiHeatCassiniOrderedPrimeLogGap
  push_cast
  linear_combination ((((xiMassNthPrimeLogHeight N : ℝ) : ℂ) -
    ((xiMassNthPrimeLogHeight (N + 1) : ℝ) : ℂ)) * s) * Complex.I_sq

/-- Exact second-order exponential remainder on one mesh cell. -/
theorem xiHeatCassiniLogMeshLaplaceScaledDefect_eq_expRemainder
    (s : ℂ) (N : ℕ) :
    xiHeatCassiniLogMeshLaplaceScaledDefect s N =
      xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s *
        (Complex.exp (s * (xiHeatCassiniOrderedPrimeLogGap N : ℂ)) - 1 -
          s * (xiHeatCassiniOrderedPrimeLogGap N : ℂ)) := by
  rw [xiHeatCassiniLogMeshLaplaceScaledDefect,
    xiHeatCassiniOrderedPrimeLaplacePhase_eq_succ_mul_exp_gap,
    xiHeatCassiniLogMeshLaplaceAtom]
  ring

/-- Finite mesh quadrature is the endpoint resolvent telescope minus the sum of scaled defects. -/
theorem sum_xiHeatCassiniLogMeshLaplaceScaledDefect
    (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, xiHeatCassiniLogMeshLaplaceScaledDefect s n =
      xiHeatCassiniOrderedPrimeLaplacePhase 0 s -
        xiHeatCassiniOrderedPrimeLaplacePhase N s -
        s * ∑ n ∈ Finset.range N, xiHeatCassiniLogMeshLaplaceAtom s n := by
  simp only [xiHeatCassiniLogMeshLaplaceScaledDefect]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_range_sub']

/-- Global Taylor bound for one scaled defect. -/
theorem norm_xiHeatCassiniLogMeshLaplaceScaledDefect_le
    (s : ℂ) (N : ℕ) :
    ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖ ≤
      ‖xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s‖ *
        ‖s * (xiHeatCassiniOrderedPrimeLogGap N : ℂ)‖ ^ 2 *
          Real.exp ‖s * (xiHeatCassiniOrderedPrimeLogGap N : ℂ)‖ := by
  rw [xiHeatCassiniLogMeshLaplaceScaledDefect_eq_expRemainder, norm_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hTaylor := Complex.norm_exp_sub_sum_le_norm_mul_exp
    (s * (xiHeatCassiniOrderedPrimeLogGap N : ℂ)) 2
  rw [sub_sub]
  simpa [Finset.sum_range_succ, Nat.factorial, norm_mul, Complex.norm_real,
    Real.norm_eq_abs] using hTaylor

/-- Bertrand bounds every ordered prime-log cell by one. -/
theorem xiHeatCassiniOrderedPrimeLogGap_le_one (N : ℕ) :
    xiHeatCassiniOrderedPrimeLogGap N ≤ 1 := by
  let p : ℝ := nthPrimeSubtype N
  let q : ℝ := nthPrimeSubtype (N + 1)
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hq2p : q ≤ 2 * p := by
    dsimp only [p, q]
    exact_mod_cast nthPrimeSubtype_succ_le_two_mul N
  have hgap : xiHeatCassiniOrderedPrimeGap N ≤ p := by
    dsimp only [xiHeatCassiniOrderedPrimeGap, p, q]
    linarith
  calc
    xiHeatCassiniOrderedPrimeLogGap N ≤
        xiHeatCassiniOrderedPrimeGap N / p := by
      simpa only [p] using xiHeatCassiniOrderedPrimeLogGap_le_gap_div_prime N
    _ ≤ 1 := (div_le_one hp).mpr hgap

/-- On the critical Laplace wall, the phase has the physical half-density norm. -/
theorem norm_xiHeatCassiniOrderedPrimeLaplacePhase_of_re_eq_neg_half
    {s : ℂ} (hs : s.re = -1 / 2) (N : ℕ) :
    ‖xiHeatCassiniOrderedPrimeLaplacePhase N s‖ =
      Real.exp (xiMassNthPrimeLogHeight N / 2) := by
  rw [norm_xiHeatCassiniOrderedPrimeLaplacePhase, hs]
  congr 1
  ring

/-- **Critical-wall mesh defect bound.**  The resolvent defect has exactly the normalized
mean-square consecutive-prime-gap majorant, with a locally bounded spectral factor. -/
theorem norm_xiHeatCassiniLogMeshLaplaceScaledDefect_le_primeGapSq
    {s : ℂ} (hs : s.re = -1 / 2) (N : ℕ) :
    ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖ ≤
      (2 * ‖s‖ ^ 2 * Real.exp ‖s‖) *
        (xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ)) ^ 2 *
          Real.sqrt (nthPrimeSubtype N : ℝ) := by
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hdelta1 : delta ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
  have hexp : Real.exp (‖s‖ * delta) ≤ Real.exp ‖s‖ := by
    apply Real.exp_le_exp.mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hdelta1 (norm_nonneg s)
  calc
    ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖ ≤
        ‖xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s‖ *
          ‖s * (delta : ℂ)‖ ^ 2 * Real.exp ‖s * (delta : ℂ)‖ := by
      simpa only [delta] using
        norm_xiHeatCassiniLogMeshLaplaceScaledDefect_le s N
    _ = ‖s‖ ^ 2 * Real.exp (‖s‖ * delta) *
          (delta ^ 2 * Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2)) := by
      rw [norm_xiHeatCassiniOrderedPrimeLaplacePhase_of_re_eq_neg_half hs,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdelta]
      ring
    _ ≤ ‖s‖ ^ 2 * Real.exp ‖s‖ *
          (delta ^ 2 * Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2)) := by
      gcongr
    _ ≤ ‖s‖ ^ 2 * Real.exp ‖s‖ *
          (2 * (xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ)) ^ 2 *
            Real.sqrt (nthPrimeSubtype N : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      simpa only [delta] using primeLogGap_sq_mul_criticalHalfDensity_le_primeGapSq N
    _ = _ := by ring

end

end RHTower
