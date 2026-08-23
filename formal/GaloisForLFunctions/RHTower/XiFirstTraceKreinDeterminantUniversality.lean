import GaloisForLFunctions.RHTower.XiWardKreinTransversePickBlock
import GaloisForLFunctions.RHTower.HedenmalmSquarefreeFirstTraceAnomalyCharge
import GaloisForLFunctions.RHTower.XiCompletedAperturePoleResonance

/-!
# First-trace / Krein determinant universality

Three independently constructed rank-two detectors carry the same local invariant.  Weighting the
canonical transverse Pick block by a residue `m` makes its fourth-power-normalized determinant
`-16 m² / 9`.  At an actual strict-right Xi support this is exactly `4/9` of the completed-aperture
collision determinant, while `m` is read entirely from the squarefree first-trace anomaly.

Consequently the finite first-trace anomaly charge is exactly the sum of normalized transverse
Krein determinants.  This is a coefficient-exact source/Krein bridge, but not a new RH endpoint:
the common invariant is the already-isolated reflection self-intersection charge.
-/

open Complex

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Scalar residue weight inserted before taking the canonical transverse determinant. -/
def residueWeightedConjugatePairTransversePickBlock
    (m : ℝ) (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (m : ℂ) • conjugatePairTransversePickBlock t

/-- A residue weight `m` contributes quadratically to the normalized determinant. -/
theorem residueWeightedConjugatePairTransversePickBlock_renormalized_det
    (m : ℝ) (t : ℂ) (ht : t.im ≠ 0) :
    t.im ^ 4 *
        (residueWeightedConjugatePairTransversePickBlock m t).det.re =
      (-16 / 9) * m ^ 2 := by
  rw [residueWeightedConjugatePairTransversePickBlock, Matrix.det_smul]
  simp only [Fintype.card_fin]
  have hbase := conjugatePairTransversePickBlock_renormalized_det t ht
  calc
    t.im ^ 4 *
        (((m : ℂ) ^ 2 * (conjugatePairTransversePickBlock t).det).re) =
        m ^ 2 * (t.im ^ 4 * (conjugatePairTransversePickBlock t).det.re) := by
      have hmre : ((m : ℂ) ^ 2).re = m ^ 2 := by
        norm_num [pow_two, Complex.mul_re]
      have hmim : ((m : ℂ) ^ 2).im = 0 := by
        norm_num [pow_two, Complex.mul_im]
      rw [Complex.mul_re, hmre, hmim]
      ring
    _ = m ^ 2 * (-16 / 9) := by rw [hbase]
    _ = (-16 / 9) * m ^ 2 := by ring

/-- Conjugate-pair pole in the centered spectral coordinate of a proposed divisor point. -/
def xiFirstTraceKreinPole (rho : ℂ) : ℂ :=
  star ((rho - 1 / 2) * (-I))

/-- Pole height is exactly transverse displacement from the critical line. -/
theorem xiFirstTraceKreinPole_im (rho : ℂ) :
    (xiFirstTraceKreinPole rho).im = rho.re - 1 / 2 := by
  simp [xiFirstTraceKreinPole, Complex.mul_im]

/-- The support-defined pole is the actual upper spectral pole on every strict-right copy. -/
theorem xiFirstTraceKreinPole_eq_xiWardKreinUpperSpectralPole
    (q : XiRightUpperZeroCopy) :
    xiFirstTraceKreinPole (q.1.1.1 : ℂ) = xiWardKreinUpperSpectralPole q := by
  rw [xiFirstTraceKreinPole, xiWardKreinUpperSpectralPole,
    xiSpectralPoint_eq_support]
  rfl

/-- Canonical Pick block weighted by multiplicity read from the first-trace anomaly. -/
def xiFirstTraceAnomalyKreinPickBlock
    (rho : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  residueWeightedConjugatePairTransversePickBlock
    (hedenmalmSquarefreeFirstTraceAnomalyMultiplicity rho)
    (xiFirstTraceKreinPole rho)

/-- The source anomaly multiplicity is the complete local normalized determinant charge. -/
theorem xiFirstTraceAnomalyKreinPickBlock_renormalized_det
    (rho : ℂ) (hright : 1 / 2 < rho.re) :
    (rho.re - 1 / 2) ^ 4 *
        (xiFirstTraceAnomalyKreinPickBlock rho).det.re =
      (-16 / 9) *
        (hedenmalmSquarefreeFirstTraceAnomalyMultiplicity rho : ℝ) ^ 2 := by
  have ht : (xiFirstTraceKreinPole rho).im ≠ 0 := by
    rw [xiFirstTraceKreinPole_im]
    linarith
  simpa [xiFirstTraceAnomalyKreinPickBlock, xiFirstTraceKreinPole_im] using
    residueWeightedConjugatePairTransversePickBlock_renormalized_det
      (hedenmalmSquarefreeFirstTraceAnomalyMultiplicity rho : ℝ)
      (xiFirstTraceKreinPole rho) ht

/-- The transverse Pick determinant and completed-aperture collision determinant are the same
residue-square anomaly, with universal ratio `4/9`. -/
theorem xiFirstTraceAnomalyKreinPickBlock_eq_completedAperture
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    ((rho : ℂ).re - 1 / 2) ^ 4 *
        (xiFirstTraceAnomalyKreinPickBlock (rho : ℂ)).det.re =
      (4 / 9) * xiCompletedApertureRegularizedResonantTwoPointDet rho 0 := by
  rw [xiFirstTraceAnomalyKreinPickBlock_renormalized_det (rho : ℂ) hright,
    xiCompletedApertureRegularizedResonantTwoPointDet_zero,
    hedenmalmSquarefreeFirstTraceAnomalyMultiplicity_eq_xi hright
      (xi_divisor_support_re_mem_open_unit rho).2,
    ← xiSupportMultiplicity_eq_analyticOrderAt_toNat]
  ring

/-- On an actual strict-right upper copy, the source-defined block is the actual Xi transverse
Pick block scaled by the source anomaly multiplicity. -/
theorem xiFirstTraceAnomalyKreinPickBlock_eq_actualXiBlock
    (q : XiRightUpperZeroCopy) :
    xiFirstTraceAnomalyKreinPickBlock (q.1.1.1 : ℂ) =
      ((hedenmalmSquarefreeFirstTraceAnomalyMultiplicity q.1.1.1 : ℝ) : ℂ) •
        xiWardKreinTransversePickBlock q := by
  rw [xiFirstTraceAnomalyKreinPickBlock,
    residueWeightedConjugatePairTransversePickBlock,
    xiWardKreinTransversePickBlock,
    xiFirstTraceKreinPole_eq_xiWardKreinUpperSpectralPole]

/-- Sum of source-anomaly-weighted normalized Pick determinants.  Factor `-9/8` converts each
local determinant `-16m²/9` into the two-oriented charge `2m²`. -/
def hedenmalmSquarefreeFirstTraceKreinDeterminantCharge (T : ℝ) : ℝ :=
  ∑ rho ∈ (hedenmalmSquarefreeFirstTraceRightSourceZeros_finite T).toFinset,
    (-9 / 8) * ((rho.re - 1 / 2) ^ 4 *
      (xiFirstTraceAnomalyKreinPickBlock rho).det.re)

/-- Finite source anomaly reflection charge is exactly its normalized transverse determinant
charge. -/
theorem hedenmalmSquarefreeFirstTraceKreinDeterminantCharge_eq_anomalyCharge
    (T : ℝ) :
    hedenmalmSquarefreeFirstTraceKreinDeterminantCharge T =
      (hedenmalmSquarefreeFirstTraceAnomalyReflectionCharge T : ℝ) := by
  rw [hedenmalmSquarefreeFirstTraceKreinDeterminantCharge,
    hedenmalmSquarefreeFirstTraceAnomalyReflectionCharge]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hsource : rho ∈ hedenmalmSquarefreeFirstTraceRightSourceZeros T := by
    simpa only [Set.Finite.mem_toFinset] using hrho
  have hright : 1 / 2 < rho.re := hsource.1
  rw [xiFirstTraceAnomalyKreinPickBlock_renormalized_det rho hright]
  ring

/-- The source/Krein determinant charge is the canonical Xi reflection self-intersection charge. -/
theorem hedenmalmSquarefreeFirstTraceKreinDeterminantCharge_eq_reflectionCharge
    (T : ℝ) :
    hedenmalmSquarefreeFirstTraceKreinDeterminantCharge T =
      (xiReflectionSelfIntersectionCharge T : ℝ) := by
  rw [hedenmalmSquarefreeFirstTraceKreinDeterminantCharge_eq_anomalyCharge,
    hedenmalmSquarefreeFirstTraceAnomalyReflectionCharge_eq]

end

end RHTower
