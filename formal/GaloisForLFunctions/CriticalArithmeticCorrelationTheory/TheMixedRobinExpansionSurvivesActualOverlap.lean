import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EndpointDecayRemovesTheCrossKernelGapLoss

/-!
# The cancelled mixed Robin expansion survives actual overlap

Polarization retains the overlap mass in the leading logarithmic term.
The common-window remainder is uniform even when two supports coincide;
no singular cross integral is separated from its diagonal cancellation.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis
open _root_.RHTower (levyEnergy)

/-- The polarized finite Robin part, with the common support width retained. -/
def mixedBumpRobin (f g : ℝ → ℝ) (w : ℝ) : ℝ :=
  (bumpRobin (fun u => f u + g u) w - bumpRobin (fun u => -f u + g u) w) / 4

private theorem scalar_robin_remainder {f : ℝ → ℝ} {w : ℝ}
    (hf : ContDiff ℝ 2 f) (hsupp : ∀ u, u ∉ Icc 0 w → f u = 0)
    (hw : 0 < w) (hw1 : w ≤ 1) :
    |levyEnergy f - ((Real.log (1 / w) + archRobinConstant) * (∫ u, f u ^ 2) +
      bumpRobin f w)| ≤ Real.exp (1 / 2) / 2 * w * ∫ u, f u ^ 2 := by
  have hfc : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc hsupp
  obtain ⟨L, _hL, hLip⟩ := ArithmeticCriticalityTheory.exists_lipschitz_bound_of_compactSupport
    (hf.of_le (by norm_num)) hfc
  exact abs_levyEnergy_atom_sub_le hf hfc hsupp hw hw1 (fun u v => hLip v u)

private theorem integral_smul_add_sq {f g : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (t : ℝ) :
    (∫ u, (t * f u + g u) ^ 2) =
      t * t * (∫ u, f u ^ 2) + 2 * t * (∫ u, f u * g u) + ∫ u, g u ^ 2 := by
  have hf2 := integrable_sq_of_continuous hf hfc
  have hg2 := integrable_sq_of_continuous hg hgc
  have hfg : Integrable fun u => f u * g u :=
    (hf.mul hg).integrable_of_hasCompactSupport hfc.mul_right
  have heq : (fun u => (t * f u + g u) ^ 2) =
      fun u => t * t * f u ^ 2 + (2 * t) * (f u * g u) + g u ^ 2 := by
    funext u
    ring
  rw [heq, integral_lin3 hf2 hfg hg2]

/-- The actual mixed Lévy form has a common-window Robin expansion with a
mass-controlled remainder, without any separation assumption. -/
theorem abs_mixed_levy_sub_robin_le {f g : ℝ → ℝ} {w : ℝ}
    (hf : ContDiff ℝ 2 f) (hfsupp : ∀ u, u ∉ Icc 0 w → f u = 0)
    (hg : ContDiff ℝ 2 g) (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0)
    (hw : 0 < w) (hw1 : w ≤ 1) :
    |(∫ y in Ioi 0, levyMixed f g y) -
      ((Real.log (1 / w) + archRobinConstant) * (∫ u, f u * g u) + mixedBumpRobin f g w)| ≤
        Real.exp (1 / 2) / 4 * w * ((∫ u, f u ^ 2) + ∫ u, g u ^ 2) := by
  have hfc : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc hfsupp
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  have hplus := scalar_robin_remainder (hf.add hg)
    (fun u hu => by simp only [hfsupp u hu, hgsupp u hu, add_zero]) hw hw1
  have hminus := scalar_robin_remainder (hf.neg.add hg)
    (fun u hu => by simp only [hfsupp u hu, hgsupp u hu, neg_zero, add_zero]) hw hw1
  have hLp := levyEnergy_smul_add hf hfc hg hgc 1
  have hLm := levyEnergy_smul_add hf hfc hg hgc (-1)
  have hMp := integral_smul_add_sq hf.continuous hfc hg.continuous hgc 1
  have hMm := integral_smul_add_sq hf.continuous hfc hg.continuous hgc (-1)
  simp only [one_mul, neg_one_mul, neg_neg] at hLp hLm hMp hMm
  let R : ℝ := (∫ y in Ioi 0, levyMixed f g y) -
    ((Real.log (1 / w) + archRobinConstant) * (∫ u, f u * g u) + mixedBumpRobin f g w)
  have heq : 4 * R =
      (levyEnergy (fun u => f u + g u) -
        ((Real.log (1 / w) + archRobinConstant) * (∫ u, (f u + g u) ^ 2) +
          bumpRobin (fun u => f u + g u) w)) -
      (levyEnergy (fun u => -f u + g u) -
        ((Real.log (1 / w) + archRobinConstant) * (∫ u, (-f u + g u) ^ 2) +
          bumpRobin (fun u => -f u + g u) w)) := by
    rw [hLp, hLm, hMp, hMm]
    dsimp only [R, mixedBumpRobin]
    ring
  have hsum : (∫ u, (f u + g u) ^ 2) + (∫ u, (-f u + g u) ^ 2) =
      2 * ((∫ u, f u ^ 2) + ∫ u, g u ^ 2) := by
    rw [hMp, hMm]
    ring
  have hb : |4 * R| ≤ Real.exp (1 / 2) / 2 * w *
      ((∫ u, (f u + g u) ^ 2) + ∫ u, (-f u + g u) ^ 2) := by
    rw [heq, mul_add]
    exact (abs_sub _ _).trans (add_le_add hplus hminus)
  rw [hsum, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hb
  change |R| ≤ _
  nlinarith only [hb]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_mixed_levy_sub_robin_le
