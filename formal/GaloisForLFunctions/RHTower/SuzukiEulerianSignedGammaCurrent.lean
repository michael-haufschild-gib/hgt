import GaloisForLFunctions.RHTower.SuzukiPrimeFlankEulerianKernel
import GaloisForLFunctions.RHTower.CCMFUSuzukiGammaBinetCofinalBridge

/-!
# Exact signed-curvature/Gamma decomposition of the SP-E current

The corrected Chebyshev Eulerian current has an exact, fixed-sign completed decomposition.
Its only archimedean discrepancy from the negative signed checkpoint-curvature first moment is
the positive higher-Binet Gamma prefix.  This prefix is `O(sqrt N)` before normalization, so it
cannot supply or conceal a macroscopic positive source excursion.  Thus signed moderation of the
SP-E current is exactly the remaining moderation problem for its literal curvature carrier.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-- Event-label first moment of the higher-Binet Gamma correction on the SP-E Eulerian clock. -/
def suzukiEulerianHigherBinetGammaPrefix (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ico 3 (N + 2), (p : ℝ) *
    (∫ t in Real.log ((p - 1 : ℕ) : ℝ)..Real.log (p : ℝ),
      ccmGammaHigherBinetModeDensity t)

/-- The SP-E higher-Binet Gamma correction is literally the existing positive checkpoint-tail
prefix, not a newly chosen compensator. -/
theorem suzukiEulerianHigherBinetGammaPrefix_eq_archTailPrefix (N : ℕ) :
    suzukiEulerianHigherBinetGammaPrefix N =
      suzukiCheckpointWeightedArchTailPrefix N := by
  rw [suzukiEulerianHigherBinetGammaPrefix,
    suzukiCheckpointWeightedArchTailPrefix]
  apply Finset.sum_congr rfl
  intro p _hp
  congr 1
  apply intervalIntegral.integral_congr
  intro t _ht
  rw [← suzukiCheckpointArchTail_eq_ccmGammaHigherBinetModeDensity]

private theorem eulerian_cell_eq_neg_curvature_sub_archTail
    {p : ℕ} (hp : 3 ≤ p) :
    (p : ℝ) *
        (RiemannGaussian.suzukiPrimeWeight (p - 2) -
          2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ))) =
      -((p : ℝ) * suzukiCheckpointSignedCurvatureCell (p - 1) +
        (p : ℝ) * (∫ t in Real.log ((p - 1 : ℕ) : ℝ)..Real.log (p : ℝ),
          suzukiCheckpointArchTail t)) := by
  have hp1 : 1 ≤ p := by omega
  have hweight : RiemannGaussian.suzukiPrimeWeight (p - 2) =
      criticalMellinAtomWeight p := by
    rw [criticalMellinAtomWeight_eq_screwPrimeWeight (by omega : 0 < p)]
    exact suzukiPrimeWeight_pred_eq_screwPrimeWeight (by omega : 2 ≤ p)
  have hexp :
      (∫ t in Real.log ((p - 1 : ℕ) : ℝ)..Real.log (p : ℝ),
        Real.exp (t / 2)) =
        2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ)) := by
    simpa only [Nat.sub_add_cancel hp1] using
      (integral_exp_half_log_cell (k := p - 1) (by omega : 1 ≤ p - 1))
  have hscrew :
      (∫ t in Real.log ((p - 1 : ℕ) : ℝ)..Real.log (p : ℝ),
        screwRegularKernel t) =
        (∫ t in Real.log ((p - 1 : ℕ) : ℝ)..Real.log (p : ℝ),
          Real.exp (t / 2)) -
        (∫ t in Real.log ((p - 1 : ℕ) : ℝ)..Real.log (p : ℝ),
          suzukiCheckpointArchTail t) := by
    exact integral_screwRegularKernel_eq_expHalf_sub_archTail hp
  rw [suzukiCheckpointSignedCurvatureCell, Nat.sub_add_cancel hp1, hweight, hscrew, hexp]
  ring

/-- Exact finite SP-E decomposition: the mass-error current is the negative signed-curvature
first moment minus its positive higher-Binet Gamma correction. -/
theorem suzukiChebyshevMassErrorCesaroDefect_eq_neg_weightedSignedCurvature_sub_higherBinetGamma
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiChebyshevMassErrorCesaroDefect N =
      -(suzukiCheckpointWeightedSignedCurvaturePrefix N +
        suzukiEulerianHigherBinetGammaPrefix N) / (N + 1 : ℕ) := by
  rw [suzukiChebyshevMassErrorCesaroDefect_eq_weightedPrimeIncrements hN]
  have hshift :
      (∑ k ∈ Finset.Ico 2 (N + 1), ((k + 1 : ℕ) : ℝ) *
        (RiemannGaussian.suzukiPrimeWeight (k - 1) -
          2 * ((((k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) -
            ((k : ℕ) : ℝ) ^ (1 / 2 : ℝ)))) =
      ∑ p ∈ Finset.Ico 3 (N + 2), (p : ℝ) *
        (RiemannGaussian.suzukiPrimeWeight (p - 2) -
          2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ))) := by
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro a ha b hb hab
      omega
    · intro p hp
      simp only [Finset.mem_Ico] at hp ⊢
      refine ⟨p - 1, ?_, ?_⟩ <;> omega
    · intro k hk
      have hsub : k + 1 - 2 = k - 1 := by omega
      have hpred : k + 1 - 1 = k := by omega
      rw [hsub, hpred]
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hprefix :
      (∑ p ∈ Finset.Ico 3 (N + 2), (p : ℝ) *
        (RiemannGaussian.suzukiPrimeWeight (p - 2) -
          2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ)))) =
      -(suzukiCheckpointWeightedSignedCurvaturePrefix N +
        suzukiCheckpointWeightedArchTailPrefix N) := by
    rw [suzukiCheckpointWeightedSignedCurvaturePrefix,
      suzukiCheckpointWeightedArchTailPrefix]
    calc
      _ = ∑ p ∈ Finset.Ico 3 (N + 2),
          -((p : ℝ) * suzukiCheckpointSignedCurvatureCell (p - 1) +
            (p : ℝ) * (∫ t in Real.log ((p - 1 : ℕ) : ℝ)..Real.log (p : ℝ),
              suzukiCheckpointArchTail t)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact eulerian_cell_eq_neg_curvature_sub_archTail
            (Finset.mem_Ico.mp hp).1
      _ = _ := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  rw [hshift, hprefix, ← suzukiEulerianHigherBinetGammaPrefix_eq_archTailPrefix]

/-- The exact residual after adding back the signed curvature is negative Gamma mass. -/
theorem suzukiChebyshevMassErrorCesaroDefect_add_weightedSignedCurvature_div_eq_neg_higherBinetGamma
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiChebyshevMassErrorCesaroDefect N +
        suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 1 : ℕ) =
      -suzukiEulerianHigherBinetGammaPrefix N / (N + 1 : ℕ) := by
  rw [suzukiChebyshevMassErrorCesaroDefect_eq_neg_weightedSignedCurvature_sub_higherBinetGamma hN]
  ring

/-- The exact Gamma residual is positive before its forced negative sign, and only square-root
size before normalization. -/
theorem suzukiEulerianHigherBinetGammaPrefix_nonneg_le (N : ℕ) :
    0 ≤ suzukiEulerianHigherBinetGammaPrefix N ∧
      suzukiEulerianHigherBinetGammaPrefix N ≤
        (8 / 3 : ℝ) * Real.sqrt (N + 2 : ℕ) := by
  rw [suzukiEulerianHigherBinetGammaPrefix_eq_archTailPrefix]
  exact suzukiCheckpointWeightedArchTailPrefix_nonneg_le N

/-- The Gamma correction has a forced sign: it can only lower the mass-error current relative to
the negative signed-curvature first moment. -/
theorem suzukiChebyshevMassErrorCesaroDefect_le_neg_weightedSignedCurvature_div
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiChebyshevMassErrorCesaroDefect N ≤
      -suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 1 : ℕ) := by
  rw [suzukiChebyshevMassErrorCesaroDefect_eq_neg_weightedSignedCurvature_sub_higherBinetGamma hN]
  have hgamma : 0 ≤ suzukiEulerianHigherBinetGammaPrefix N :=
    (suzukiEulerianHigherBinetGammaPrefix_nonneg_le N).1
  have hden : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
  have hquot : 0 ≤ suzukiEulerianHigherBinetGammaPrefix N / (N + 1 : ℕ) :=
    div_nonneg hgamma hden.le
  calc
    -(suzukiCheckpointWeightedSignedCurvaturePrefix N +
        suzukiEulerianHigherBinetGammaPrefix N) / (N + 1 : ℕ) =
      -suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 1 : ℕ) -
        suzukiEulerianHigherBinetGammaPrefix N / (N + 1 : ℕ) := by ring
    _ ≤ -suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 1 : ℕ) := by linarith

end

end GaloisForLFunctions.RHTower
