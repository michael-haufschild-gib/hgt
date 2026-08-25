import GaloisForLFunctions.RHTower.ConstitutiveDaggerConfluence
import GaloisForLFunctions.RHTower.XiHypertranscendentalModularResidueTransgression

/-!
# Xi source-history residue transgression

Two constructions that previously lived in separate routes carry the same transverse invariant.
The constitutive route measures the metric defect between two executable histories representing
one semantic repair.  The source-normal-cone route measures the real affine residue of the Xi
divisor current.  Their exact proportionality shows that an off-line Xi zero is not merely a
non-neutral divisor point: it is a closed analytic response with nonzero source-history holonomy.

This is not an RH proof.  It fixes the missing producer's mathematical type: any arithmetic
descent law that makes the two semantic histories metrically indistinguishable on Xi-zero fibres
must annihilate the already-constructed affine divisor residue.
-/

open Complex Filter Topology
open GaloisForLFunctions

namespace RHTower

open ConstitutiveCriticalCompletionMechanics

noncomputable section

/-- Exact chart identity: the canonical source-history defect is the shell-transfer entropy
scaled by the logarithmic clock.  Both sides are defined before selecting a Xi divisor. -/
theorem actualRepairHistoryDefect_eq_shellTransferEntropy
    (N clock : ℕ) (s : ℂ) :
    actualRepairOrientationPotential N clock s (left (N + 1)) -
        actualRepairOrientationPotential N clock s (right (N + 1)) =
      -2 * Real.log clock * shellTransferEntropy s := by
  rw [actualRepairOrientationPotential_left,
    actualRepairOrientationPotential_right,
    logarithm_deningerHalfDensityMateGain,
    shellTransferEntropy_eq]
  ring

/-- Multiplicity-exact transgression: accumulated source-history defect equals the real affine
Xi residue, with the clock scale and orientation fixed explicitly. -/
theorem actualRepairHistoryDefect_mul_eq_affineResidue
    (N clock : ℕ) (rho : ℂ) (m : ℤ) :
    (m : ℝ) *
        (actualRepairOrientationPotential N clock rho (left (N + 1)) -
          actualRepairOrientationPotential N clock rho (right (N + 1))) =
      -2 * Real.log clock *
        (-((rho - 1 / 2) * (m : ℂ))).re := by
  rw [actualRepairHistoryDefect_eq_shellTransferEntropy,
    re_centeredXiAffineResidue_eq_shellTransferEntropy]
  ring

/-- At an actual Xi divisor point, the real source-normal-cone current converges to the
clock-normalized defect between the two semantically equivalent repair histories. -/
theorem tendsto_re_xiExceptionalAffineDivisorCurrent_eq_repairHistoryDefect
    {rho : ℂ} {m : ℤ}
    (horder : meromorphicOrderAt xi rho = m)
    (N clock : ℕ) (hclock : 2 ≤ clock) :
    Tendsto
      (fun s =>
        ((s - rho) * xiExceptionalAffineDivisorCurrent s).re)
      (𝓝[≠] rho)
      (nhds
        (-(m : ℝ) *
            (actualRepairOrientationPotential N clock rho (left (N + 1)) -
              actualRepairOrientationPotential N clock rho (right (N + 1))) /
          (2 * Real.log clock))) := by
  have hlog : Real.log (clock : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hclock)))
  have h :=
    tendsto_re_xiExceptionalAffineDivisorCurrent_eq_transferEntropy horder
  convert h using 1
  rw [actualRepairHistoryDefect_eq_shellTransferEntropy]
  field_simp

/-- Exact descent classifier.  For nonzero divisor order, semantic proof erasure for the
source-metric histories is equivalent to annihilation of the local affine Xi residue. -/
theorem actualRepairProofErasureConsistent_iff_affineResidue_eq_zero
    {N clock : ℕ} (hclock : 2 ≤ clock) (rho : ℂ) (m : ℤ) (hm : m ≠ 0) :
    RepairProofErasureConsistent N
        (actualRepairOrientationPotential N clock rho) ↔
      (-((rho - 1 / 2) * (m : ℂ))).re = 0 := by
  rw [actualRepairProofErasureConsistent_iff_re_eq_half hclock,
    re_centeredXiAffineResidue_eq_shellTransferEntropy,
    centeredXiModularCharge_eq_zero_iff hm]

end

end RHTower
