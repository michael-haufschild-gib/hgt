import GaloisForLFunctions.ArithmeticIndexDescent.TouchingSupportsHaveBoundedGammaInteraction
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomHasConstantOne
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartOfTheMarkovFormAtTheSpacing

/-!
# Gamma energy across an arithmetic cutoff

Ordered supports have a mixed Gamma cost bounded by ordinary square mass.
For separated logarithmic atoms, the unit logarithmic self-energy loses
only a small multiple of the prime defect and a bounded mass term. These
bounds retain the actual Gamma form and all signed coefficient vectors.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Complex RHTower Zeta23
open scoped ComplexConjugate
namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open ArithmeticElectrostatics RenormalizedArithmeticPotentialTheory ArithmeticCastelnuovoSeveri

/-- Polarization of the actual spectral Gamma form on compact C² profiles. -/
theorem archForm_add_eq {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    archForm (fun u => f u + g u) = archForm f + archForm g +
      2 * ((1 / (2 * Real.pi)) * ∫ r : ℝ,
        (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r) := by
  have ip := integrable_normSq_paperFT_mul_gammaBracket (hf.add hg) (hfc.add hgc)
  have iff := integrable_normSq_paperFT_mul_gammaBracket hf hfc
  have ig := integrable_normSq_paperFT_mul_gammaBracket hg hgc
  have idiff : Integrable (fun r : ℝ =>
      ‖paperFT (fun u => ((f u + g u : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r -
        ‖paperFT (fun u => (f u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) := ip.sub iff
  have hpoint (r : ℝ) :
      ‖paperFT (fun u => ((f u + g u : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r -
          ‖paperFT (fun u => (f u : ℂ)) r‖ ^ 2 * EF.gammaBracket r -
          ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * EF.gammaBracket r =
        2 * ((paperFT (fun u => (f u : ℂ)) r * conj (paperFT (fun u => (g u : ℂ)) r)).re *
          EF.gammaBracket r) := by
    have hp := (paperFT_ofReal_add_and_sub
      (hf.continuous.integrable_of_hasCompactSupport hfc)
      (hg.continuous.integrable_of_hasCompactSupport hgc) r).1
    rw [hp, (norm_add_and_sub_sq_eq
      (paperFT (fun u => (f u : ℂ)) r) (paperFT (fun u => (g u : ℂ)) r)).1]
    ring
  have he : archForm (fun u => f u + g u) - archForm f - archForm g =
      2 * ((1 / (2 * Real.pi)) * ∫ r : ℝ,
        (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r) := by
    unfold archForm
    rw [← mul_sub, ← mul_sub, ← integral_sub ip iff, ← integral_sub idiff ig]
    simp_rw [hpoint]
    rw [integral_const_mul]
    change (1 / (2 * Real.pi)) * (2 * ∫ r : ℝ,
      (paperFT (cx f) r * conj (paperFT (cx g) r)).re * EF.gammaBracket r) = _
    ring
  linarith only [he]

/-- Ordered supports interact at ordinary square-mass cost, with no logarithmic loss. -/
theorem archForm_add_ge_of_ordered {f g : ℝ → ℝ} {b : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) :
    archForm f + archForm g - 2 * Real.pi * ((∫ u, f u ^ 2) + ∫ u, g u ^ 2) ≤
      archForm (fun u => f u + g u) := by
  have h := ArithmeticIndexDescent.abs_archCross_le_of_ordered hf hfc hg hgc hleft hright
  have hlow := (abs_le.mp h).1
  change -(Real.pi * ((∫ u, f u ^ 2) + ∫ u, g u ^ 2)) ≤ _ at hlow
  rw [archForm_add_eq hf hfc hg hgc]
  linarith only [hlow]

/-- Coefficient-mass part of the separated archimedean cross-kernel bound. -/
def separatedCrossMassCost : ℝ :=
  16 * Real.exp 2 + 3 + 16 * Real.exp 2 * (Real.log 4 + 4)

/-- Separated atoms retain unit logarithmic self-energy at prime-defect cost proportional to overlap. -/
theorem archForm_atomicTest_ge_separated_defect {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {M : ℕ} (hM : 1 ≤ M)
    (hw : 0 < w) (hw1 : w ≤ 1) (hsep : w ≤ atomSpacing M / 2) (x : ℕ → ℝ) :
    (∫ u, g u ^ 2) *
      ((2 * gammaHardyPhaseRate 0 + Real.log (1 / w) -
          2 * w * M * separatedCrossMassCost) * (∑ n ∈ Icc 1 M, x n ^ 2) -
        32 * Real.exp 2 * w * M * poleDefect M x) ≤ archForm (atomicTest M x g) := by
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hS : 0 ≤ ∑ n ∈ Icc 1 M, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  have hself := mul_le_mul_of_nonneg_left (levyEnergy_atom_ge hg hgc hsupp hw hw1) hS
  have hdiag := levyEnergy_atomicTest_ge_diag hg hgc hsupp hM hw hsep x
  have hcross := mul_le_mul_of_nonneg_left (cross_penalty_le hM hw x)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hG)
  have hspacing := atomSpacing_pos hM
  have hw' : w < atomSpacing M := by linarith only [hsep, hspacing]
  rw [archForm_eq_levyEnergy (contDiff_atomicTest hg M x)
    (hasCompactSupport_atomicTest hsupp M x), integral_atomicTest_sq hg hgc hsupp hw' x]
  unfold separatedCrossMassCost
  nlinarith only [hself, hdiag, hcross]

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.archForm_add_ge_of_ordered
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.archForm_atomicTest_ge_separated_defect
