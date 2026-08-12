import GaloisForLFunctions.HTGeometry.ConstitutivePositiveFormationReflection
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperatorBound
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Positive reciprocal formation properness

The global positive packet chart has two independent amplification axes.  Formation amplification
scales the recovered midpoint logarithm, while relative-law amplification scales the recovered
reciprocal logarithm.  Uniform boundedness on both axes holds exactly at the neutral packet.

This is the unconditional bi-axis properness core of ULF-RFTM-3B.  It contains no RH premise.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Natural powers of a positive-definite complex matrix remain positive definite. -/
lemma posDef_natPow {A : Matrix n n ℂ} (hA : A.PosDef) (k : ℕ) :
    (A ^ k).PosDef := by
  apply Matrix.IsStrictlyPositive.posDef
  rw [← CFC.rpow_natCast A k hA.posSemidef.nonneg]
  exact hA.isStrictlyPositive.rpow A k

/-- Two equal natural powers multiply to the doubled power. -/
lemma natPow_mul_self (A : Matrix n n ℂ) (k : ℕ) :
    A ^ k * A ^ k = A ^ (2 * k) := by
  rw [← pow_add]
  congr 1
  omega

/-- Hilbert--Schmidt logarithmic work of the recovered midpoint of the two-axis packet. -/
noncomputable def positiveFormationMidpointWork
    (R Q : Matrix n n ℂ) (formationDepth relativeDepth : ℕ) : ℝ :=
  hsNorm (CFC.log (positiveMatrixGeometricMean
    (positiveFormationPacketDirect (R ^ formationDepth) (Q ^ relativeDepth))
    (positiveFormationPacketReflected (R ^ formationDepth) (Q ^ relativeDepth))))

/-- Hilbert--Schmidt logarithmic work of the recovered relative-law coordinate. -/
noncomputable def positiveFormationRelativeWork
    (R Q : Matrix n n ℂ) (formationDepth relativeDepth : ℕ) : ℝ :=
  hsNorm (CFC.log (positiveFormationRecoveryQ
    (positiveFormationPacketDirect (R ^ formationDepth) (Q ^ relativeDepth))
    (positiveFormationPacketReflected (R ^ formationDepth) (Q ^ relativeDepth))))

/-- Formation amplification changes only the midpoint coordinate. -/
lemma positiveFormationAmplified_midpoint {R Q : Matrix n n ℂ}
    (hR : R.PosDef) (hQ : Q.PosDef) (formationDepth relativeDepth : ℕ) :
    positiveMatrixGeometricMean
      (positiveFormationPacketDirect (R ^ formationDepth) (Q ^ relativeDepth))
      (positiveFormationPacketReflected (R ^ formationDepth) (Q ^ relativeDepth)) =
        R ^ (2 * formationDepth) := by
  rw [positiveFormationPacket_midpoint (posDef_natPow hR formationDepth)
    (posDef_natPow hQ relativeDepth)]
  exact natPow_mul_self R formationDepth

/-- Exact linear escape rate on the midpoint axis. -/
lemma positiveFormationMidpointWork_eq {R Q : Matrix n n ℂ}
    (hR : R.PosDef) (hQ : Q.PosDef) (formationDepth relativeDepth : ℕ) :
    positiveFormationMidpointWork R Q formationDepth relativeDepth =
      (2 * formationDepth : ℕ) * hsNorm (CFC.log R) := by
  unfold positiveFormationMidpointWork
  rw [positiveFormationAmplified_midpoint hR hQ formationDepth relativeDepth]
  rw [CFC.log_pow' (2 * formationDepth) R hR.isStrictlyPositive]
  unfold hsNorm
  change ‖(2 * formationDepth) • matVec (CFC.log R)‖ = _
  rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul]

/-- Exact linear escape rate on the reciprocal relative-law axis. -/
lemma positiveFormationRelativeWork_eq {R Q : Matrix n n ℂ}
    (hR : R.PosDef) (hQ : Q.PosDef) (formationDepth relativeDepth : ℕ) :
    positiveFormationRelativeWork R Q formationDepth relativeDepth =
      (relativeDepth : ℕ) * hsNorm (CFC.log Q) := by
  unfold positiveFormationRelativeWork
  rw [positiveFormationRecoveryQ_formation (posDef_natPow hR formationDepth)
    (posDef_natPow hQ relativeDepth)]
  rw [CFC.log_pow' relativeDepth Q hQ.isStrictlyPositive]
  unfold hsNorm
  change ‖relativeDepth • matVec (CFC.log Q)‖ = _
  rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul]

/-- The positive functional-calculus logarithm vanishes exactly at the identity. -/
lemma cfcLog_eq_zero_iff_posDef {A : Matrix n n ℂ} (hA : A.PosDef) :
    CFC.log A = 0 ↔ A = 1 := by
  constructor
  · intro h
    have hexp := CFC.exp_log A hA.isStrictlyPositive
    rw [h] at hexp
    simpa using hexp.symm
  · rintro rfl
    exact CFC.log_one

/-- Bounded work on the complete formation-amplification axis selects neutral formation. -/
theorem positiveFormationMidpointWork_bounded_iff {R Q : Matrix n n ℂ}
    (hR : R.PosDef) (hQ : Q.PosDef) :
    (∃ C : ℝ, ∀ formationDepth relativeDepth : ℕ,
      positiveFormationMidpointWork R Q formationDepth relativeDepth ≤ C) ↔ R = 1 := by
  constructor
  · rintro ⟨C, hC⟩
    have hd : hsNorm (CFC.log R) = 0 := by
      by_contra hd0
      have hdpos : 0 < hsNorm (CFC.log R) :=
        lt_of_le_of_ne (hsNorm_nonneg _) (Ne.symm hd0)
      obtain ⟨k, hk⟩ := exists_nat_gt (C / (2 * hsNorm (CFC.log R)))
      have hden : 0 < 2 * hsNorm (CFC.log R) := mul_pos (by norm_num) hdpos
      have hstrict : C < (k : ℝ) * (2 * hsNorm (CFC.log R)) :=
        (div_lt_iff₀ hden).mp hk
      have hwork : positiveFormationMidpointWork R Q k 1 =
          (k : ℝ) * (2 * hsNorm (CFC.log R)) := by
        rw [positiveFormationMidpointWork_eq hR hQ k 1]
        norm_num
        ring
      have hle := hC k 1
      rw [hwork] at hle
      exact (not_lt_of_ge hle) hstrict
    have hlog : CFC.log R = 0 := by
      have hvec : matVec (CFC.log R) = 0 := norm_eq_zero.mp hd
      ext i j
      have hij := congrArg
        (fun v : EuclideanSpace ℂ (n × n) =>
          (EuclideanSpace.equiv (n × n) ℂ v) (i, j)) hvec
      simpa [matVec] using hij
    exact (cfcLog_eq_zero_iff_posDef hR).mp hlog
  · rintro rfl
    refine ⟨0, ?_⟩
    intro formationDepth relativeDepth
    rw [positiveFormationMidpointWork_eq Matrix.PosDef.one hQ formationDepth relativeDepth,
      CFC.log_one]
    have hz : matVec (0 : Matrix n n ℂ) = 0 := rfl
    simp [hsNorm, hz]

/-- Bounded work on the complete relative-law amplification axis selects the reflection center. -/
theorem positiveFormationRelativeWork_bounded_iff {R Q : Matrix n n ℂ}
    (hR : R.PosDef) (hQ : Q.PosDef) :
    (∃ C : ℝ, ∀ formationDepth relativeDepth : ℕ,
      positiveFormationRelativeWork R Q formationDepth relativeDepth ≤ C) ↔ Q = 1 := by
  constructor
  · rintro ⟨C, hC⟩
    have hd : hsNorm (CFC.log Q) = 0 := by
      by_contra hd0
      have hdpos : 0 < hsNorm (CFC.log Q) :=
        lt_of_le_of_ne (hsNorm_nonneg _) (Ne.symm hd0)
      obtain ⟨k, hk⟩ := exists_nat_gt (C / hsNorm (CFC.log Q))
      have hstrict : C < (k : ℝ) * hsNorm (CFC.log Q) :=
        (div_lt_iff₀ hdpos).mp hk
      have hwork : positiveFormationRelativeWork R Q 0 k =
          (k : ℝ) * hsNorm (CFC.log Q) := by
        rw [positiveFormationRelativeWork_eq hR hQ 0 k]
      exact (not_lt_of_ge (hC 0 k)) (hwork ▸ hstrict)
    have hlog : CFC.log Q = 0 := by
      have hvec : matVec (CFC.log Q) = 0 := norm_eq_zero.mp hd
      ext i j
      have hij := congrArg
        (fun v : EuclideanSpace ℂ (n × n) =>
          (EuclideanSpace.equiv (n × n) ℂ v) (i, j)) hvec
      simpa [matVec] using hij
    exact (cfcLog_eq_zero_iff_posDef hQ).mp hlog
  · rintro rfl
    refine ⟨0, ?_⟩
    intro formationDepth relativeDepth
    rw [positiveFormationRelativeWork_eq hR Matrix.PosDef.one formationDepth relativeDepth,
      CFC.log_one]
    have hz : matVec (0 : Matrix n n ℂ) = 0 := rfl
    simp [hsNorm, hz]

/-- **Bi-axis properness capstone.**  Uniform boundedness of both complete amplification axes is
equivalent to simultaneous neutrality of formation and reciprocal relative law. -/
theorem positiveFormationBiAxisWork_bounded_iff {R Q : Matrix n n ℂ}
    (hR : R.PosDef) (hQ : Q.PosDef) :
    ((∃ C : ℝ, ∀ formationDepth relativeDepth : ℕ,
        positiveFormationMidpointWork R Q formationDepth relativeDepth ≤ C) ∧
      (∃ C : ℝ, ∀ formationDepth relativeDepth : ℕ,
        positiveFormationRelativeWork R Q formationDepth relativeDepth ≤ C)) ↔
      R = 1 ∧ Q = 1 := by
  rw [positiveFormationMidpointWork_bounded_iff hR hQ,
    positiveFormationRelativeWork_bounded_iff hR hQ]

end GaloisForLFunctions.HTGeometry
