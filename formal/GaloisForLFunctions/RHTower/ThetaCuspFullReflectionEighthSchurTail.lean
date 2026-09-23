import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthLowerJetBaseline

/-!
# Strict Schur diagonals for complete-theta rank-three curvature

The native rank-three reflected polynomial admits an exact two-by-two Schur form.  Its first
pivot is already strict from the fourth-jet theorem.  This module proves that the transformed
eighth diagonal is also strict on the entire physical theta orbit.  Thus neither diagonal can
cause loss of rank-three positivity: the sole surviving obstruction is saturation of one
explicit sixth-jet coupling.

This removes a full diagonal premise from the finite TCD/S6F gate.  Proving the remaining strict
coupling inequality gives native `D1 > 0`, then the cofinal Hankel/Bezoutian landing and Weil
positivity route to RH.
-/

open Real

namespace RHTower

noncomputable section

/-- First Schur pivot of the rank-three reflected log-jet polynomial. -/
def thetaCuspReflectedEighthSchurHead (A B : ℝ) : ℝ :=
  4 * A ^ (2 : ℕ) - B

/-- Off-diagonal Schur coupling of the rank-three reflected log-jet polynomial. -/
def thetaCuspReflectedEighthSchurCoupling (A C : ℝ) : ℝ :=
  C - 64 * A ^ (3 : ℕ)

/-- Last diagonal Schur reserve of the rank-three reflected log-jet polynomial. -/
def thetaCuspReflectedEighthSchurTail (A B D : ℝ) : ℝ :=
  1216 * A ^ (4 : ℕ) - 32 * A ^ (2 : ℕ) * B + 68 * B ^ (2 : ℕ) - D

/-- Exact Schur normal form of native rank-three reflected curvature. -/
theorem thetaCuspReflectedEighthPolynomial_eq_schur
    (A B C D : ℝ) :
    thetaCuspReflectedEighthPolynomial A B C D =
      thetaCuspReflectedEighthSchurHead A B *
          thetaCuspReflectedEighthSchurTail A B D -
        thetaCuspReflectedEighthSchurCoupling A C ^ (2 : ℕ) := by
  unfold thetaCuspReflectedEighthPolynomial thetaCuspReflectedEighthSchurHead
    thetaCuspReflectedEighthSchurTail thetaCuspReflectedEighthSchurCoupling
  ring

/-- A global first-atom budget used only to prove transformed diagonal strictness.  It is not a
compact-interval threshold: it holds from the physical support edge to infinity. -/
private theorem thetaCuspFirstAtomEighthProfile_lt_schurBudget
    {q : ℝ} (hq : (41 / 25 : ℝ) ≤ q) :
    thetaCuspFirstAtomEighthProfile q <
      200 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (4 : ℕ) := by
  have hqpos : 0 < q := by linarith
  let y := q - 41 / 25
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (8 : ℕ) *
      (200 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (4 : ℕ) -
        thetaCuspFirstAtomEighthProfile q) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 41 / 25 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 8]

/-- The Born eighth jet is globally dominated by the fourth power of the worst admissible
complete curvature. -/
private theorem thetaCuspBornWittenLogEighthDerivative_lt_schurBudget
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenLogEighthDerivative 1 x <
      200 * (thetaCuspBornWittenLogCurvature 1 x - 13 / 10) ^ (4 : ℕ) := by
  let q := thetaCuspBornWittenWeight 1 x
  have hq : (41 / 25 : ℝ) ≤ q := by
    have hpi := Real.pi_gt_d2
    norm_num at hpi
    have he : 1 ≤ Real.exp x := Real.one_le_exp hx
    have he2 : 1 ≤ Real.exp x ^ (2 : ℕ) := by nlinarith [Real.exp_pos x]
    have hscale : Real.pi ≤ thetaCuspMorseScale 1 x := by
      rw [thetaCuspMorseScale]
      norm_num
      simpa using mul_le_mul_of_nonneg_left he2 Real.pi_pos.le
    dsimp only [q]
    rw [thetaCuspBornWittenWeight_eq]
    linarith
  have hprofile := thetaCuspFirstAtomEighthProfile_lt_schurBudget hq
  have hA : thetaCuspBornWittenLogCurvature 1 x =
      thetaCuspFirstAtomCurvatureProfile q := by
    dsimp only [q]
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hx]
    rfl
  have hD : thetaCuspBornWittenLogEighthDerivative 1 x =
      thetaCuspFirstAtomEighthProfile q := by
    dsimp only [q, thetaCuspBornWittenLogEighthDerivative,
      thetaCuspFirstAtomEighthProfile]
  rw [hA, hD]
  exact hprofile

/-- The first Schur pivot is strict on the complete physical theta orbit. -/
theorem thetaCuspFullReflectionEighthSchurHead_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspReflectedEighthSchurHead
      (thetaCuspFullReflectedLogCurvature x)
      (thetaCuspFullReflectedLogFourthJet x) := by
  have hA : 0 < thetaCuspFullReflectedLogCurvature x := by
    have hfirst := nineteen_le_thetaCuspBornWittenLogCurvature
      (n := 1) (by norm_num) hx
    have he2 := thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
    unfold thetaCuspFullReflectedLogCurvature
    linarith
  have hB := thetaCuspFullReflectedLogFourthJet_lt_two_mul_curvature_sq hx
  unfold thetaCuspReflectedEighthSchurHead
  nlinarith [sq_pos_of_pos hA]

/-- The transformed eighth diagonal is strict on the complete physical theta orbit.  Hence a
rank-three failure cannot arise from diagonal degeneration. -/
theorem thetaCuspFullReflectionEighthSchurTail_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspReflectedEighthSchurTail
      (thetaCuspFullReflectedLogCurvature x)
      (thetaCuspFullReflectedLogFourthJet x)
      (thetaCuspFullReflectedLogEighthJet x) := by
  let A0 := thetaCuspBornWittenLogCurvature 1 x
  let D0 := thetaCuspBornWittenLogEighthDerivative 1 x
  let e2 := thetaCuspLikelihoodSourceLogPartitionJetTwo x
  let e8 := thetaCuspLikelihoodSourceLogPartitionJetEight x
  let A := A0 - e2
  let B := thetaCuspFullReflectedLogFourthJet x
  let D := D0 - e8
  let W := A0 - 13 / 10
  have hA0 : (19 : ℝ) ≤ A0 := by
    simpa only [A0] using nineteen_le_thetaCuspBornWittenLogCurvature
      (n := 1) (by norm_num) hx
  have he2 : e2 ≤ (13 / 10 : ℝ) := by
    simpa only [e2] using
      thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
  have he8 : 0 < e8 := by
    simpa only [e8] using thetaCuspLikelihoodSourceLogPartitionJetEight_pos hx
  have hWpos : 0 < W := by dsimp only [W]; linarith
  have hWA : W ≤ A := by dsimp only [W, A]; linarith
  have hApos : 0 < A := hWpos.trans_le hWA
  have hpow : W ^ (4 : ℕ) ≤ A ^ (4 : ℕ) := pow_le_pow_left₀ hWpos.le hWA 4
  have hD0 : D0 < 200 * W ^ (4 : ℕ) := by
    simpa only [D0, W, A0] using
      thetaCuspBornWittenLogEighthDerivative_lt_schurBudget hx
  have hD : D < 200 * A ^ (4 : ℕ) := by
    dsimp only [D]
    nlinarith
  have hsq : 0 ≤ (17 * B - 4 * A ^ (2 : ℕ)) ^ (2 : ℕ) := sq_nonneg _
  have hid : 289 * thetaCuspReflectedEighthSchurTail A B D =
      350336 * A ^ (4 : ℕ) + 68 * (17 * B - 4 * A ^ (2 : ℕ)) ^ (2 : ℕ) - 289 * D := by
    unfold thetaCuspReflectedEighthSchurTail
    ring
  have hA4 : 0 < A ^ (4 : ℕ) := pow_pos hApos 4
  have htail : 0 < thetaCuspReflectedEighthSchurTail A B D := by
    nlinarith
  simpa only [thetaCuspReflectedEighthSchurTail, A, B, D, A0, D0, e2, e8,
    thetaCuspFullReflectedLogCurvature, thetaCuspFullReflectedLogEighthJet] using htail

/-- Exact remaining D1 burden after both Schur diagonals are proved strict: one squared
sixth-jet coupling must stay below their product. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_iff_schurCoupling
    (x : ℝ) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x ↔
      thetaCuspReflectedEighthSchurCoupling
          (thetaCuspFullReflectedLogCurvature x)
          (thetaCuspFullReflectedLogSixthJet x) ^ (2 : ℕ) <
        thetaCuspReflectedEighthSchurHead
            (thetaCuspFullReflectedLogCurvature x)
            (thetaCuspFullReflectedLogFourthJet x) *
          thetaCuspReflectedEighthSchurTail
            (thetaCuspFullReflectedLogCurvature x)
            (thetaCuspFullReflectedLogFourthJet x)
            (thetaCuspFullReflectedLogEighthJet x) := by
  rw [show thetaCuspFullReflectionEighthHankelCurvature x =
      thetaCuspReflectedEighthPolynomial
        (thetaCuspFullReflectedLogCurvature x)
        (thetaCuspFullReflectedLogFourthJet x)
        (thetaCuspFullReflectedLogSixthJet x)
        (thetaCuspFullReflectedLogEighthJet x) by
      rfl,
    thetaCuspReflectedEighthPolynomial_eq_schur]
  constructor <;> intro h <;> linarith

end


end RHTower
