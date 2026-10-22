import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianCountertransportXiCapacity
import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalGreenParityObstruction

/-!
# Reflected Gaussian jet Wronskian and the Green fracture

The fixed reflected Meyer Gaussian carries more source information than its
zeroth Xi evaluation.  Pair its zeroth and first Mellin jets at an actual Xi
copy `q` and its critical-line reflection `q# = 1 - conj(q)`.  Their
alternating determinant is

`J₁(q) J₀(q#) - J₀(q) J₁(q#)`.

This module proves unconditionally that this source-native, off-diagonal
Wronskian is exactly the horizontal Green fracture times a nowhere-zero
Gaussian pair factor.  Thus it vanishes exactly on the critical line and is
division-free equivalent to the actual reflected adaptive Green coefficient.
The result supplies the previously absent coupling between resolved source
jet provenance and the Green displacement.  It does not assume or prove the
arithmetic annihilation of that determinant.

No RH premise, divisor-selected source, or computation is used.
-/

open Complex Function Set Topology MeasureTheory
open scoped Real
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

namespace DeningerMeyerGaussianGreen

/-- Critical-line conjugation is an involution on multiplicity-exact Xi
copies.  The copy index is transported twice through the same divisor
equalities, so it too returns exactly, not merely up to support equality. -/
@[simp]
theorem xiZeroCopyLineConjEquiv_apply_apply (q : XiZeroCopy) :
    xiZeroCopyLineConjEquiv (xiZeroCopyLineConjEquiv q) = q := by
  have hfst :
      (xiZeroCopyLineConjEquiv (xiZeroCopyLineConjEquiv q)).1 = q.1 := by
    apply Subtype.ext
    simp [xiZeroCopyLineConjEquiv, xiZeroCopyConjEquiv,
      xiZeroCopyReflectEquiv, xiZeroConjEquiv, xiZeroReflectEquiv,
      Equiv.sigmaCongr, Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg (fun rho : XiDivisorSupport =>
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ))) hfst)).2
  simp [xiZeroCopyLineConjEquiv, xiZeroCopyConjEquiv,
    xiZeroCopyReflectEquiv, xiZeroConjEquiv, xiZeroReflectEquiv,
    Equiv.sigmaCongr, Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  exact Fin.val_eq_val_of_heq (cast_heq _ q.2)

/-- Zeroth Mellin jet of the fixed reflected Gaussian at an actual Xi copy. -/
def deningerMeyerReflectedGaussianMellinZeroJet (q : XiZeroCopy) : ℂ :=
  deningerMeyerStrongLogMellinJetLM 0 (q.1 : ℂ)
    deningerMeyerReflectedLogGaussianSource

/-- First Mellin jet of the same fixed source.  This is taken before the
Meyer boundary quotient, so it exists without any multiplicity assumption. -/
def deningerMeyerReflectedGaussianMellinFirstJet (q : XiZeroCopy) : ℂ :=
  deningerMeyerStrongLogMellinJetLM 1 (q.1 : ℂ)
    deningerMeyerReflectedLogGaussianSource

/-- Exact zeroth-jet Gaussian formula. -/
theorem deningerMeyerReflectedGaussianMellinZeroJet_eq (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianMellinZeroJet q =
      Complex.exp (((q.1 : ℂ) - 1 / 2) ^ 2 / (4 * π)) := by
  rw [deningerMeyerReflectedGaussianMellinZeroJet,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
    iteratedDeriv_zero, deningerMeyerReflectedLogGaussianSource_mellin]

/-- The zeroth jet is the already admitted global Gaussian horizon grade. -/
theorem deningerMeyerReflectedGaussianMellinZeroJet_eq_horizonGrade
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianMellinZeroJet q =
      reflectedGaussianHorizonGrade q := by
  rw [deningerMeyerReflectedGaussianMellinZeroJet,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
    iteratedDeriv_zero, reflectedGaussianHorizonGrade]

/-- Exact first-jet Gaussian formula. -/
theorem deningerMeyerReflectedGaussianMellinFirstJet_eq (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianMellinFirstJet q =
      (((q.1 : ℂ) - 1 / 2) / (2 * π)) *
        Complex.exp (((q.1 : ℂ) - 1 / 2) ^ 2 / (4 * π)) := by
  rw [deningerMeyerReflectedGaussianMellinFirstJet,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
    iteratedDeriv_one]
  rw [show
    deningerMeyerStrongLogMellin
        deningerMeyerReflectedLogGaussianSource =
      fun z : ℂ => Complex.exp ((z - 1 / 2) ^ 2 / (4 * π)) by
        funext z
        exact deningerMeyerReflectedLogGaussianSource_mellin z]
  have hinner : HasDerivAt
      (fun z : ℂ => (z - 1 / 2) ^ 2 / (4 * π))
      ((((q.1 : ℂ) - 1 / 2) / (2 * π))) (q.1 : ℂ) := by
    convert (((hasDerivAt_id (q.1 : ℂ)).sub_const (1 / 2)).pow 2).div_const
      (4 * π) using 1
    all_goals try rfl
    all_goals simp only [id_eq]
    all_goals ring_nf
  simpa only [mul_comm] using hinner.cexp.deriv

/-- The first jet is the centered spectral coordinate times the zeroth jet. -/
theorem deningerMeyerReflectedGaussianMellinFirstJet_eq_centered_mul_zeroJet
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianMellinFirstJet q =
      (((q.1 : ℂ) - 1 / 2) / (2 * π)) *
        deningerMeyerReflectedGaussianMellinZeroJet q := by
  rw [deningerMeyerReflectedGaussianMellinFirstJet_eq,
    deningerMeyerReflectedGaussianMellinZeroJet_eq]

/-! ## Realizing the first jet as an honest second Meyer source -/

/-- Differentiation preserves the all-weight Meyer target. -/
def deningerMeyerStrongLogDerivative
    (g : DeningerMeyerStrongLogTarget) : DeningerMeyerStrongLogTarget :=
  ⟨deriv (g : ℝ → ℂ), g.property.deriv⟩

@[simp]
theorem deningerMeyerStrongLogDerivative_apply
    (g : DeningerMeyerStrongLogTarget) (t : ℝ) :
    ((deningerMeyerStrongLogDerivative g :
      DeningerMeyerStrongLogTarget) : ℝ → ℂ) t =
      deriv (g : ℝ → ℂ) t :=
  rfl

/-- Logarithmic moment of the reflected Gaussian, constructed internally
from differentiation and linear closure of the exact Meyer target. -/
def deningerMeyerReflectedLogGaussianMomentSource :
    DeningerMeyerStrongLogTarget :=
  (-1 / (2 * (π : ℂ))) •
    (deningerMeyerStrongLogDerivative
        deningerMeyerReflectedLogGaussianSource +
      (1 / 2 : ℂ) • deningerMeyerReflectedLogGaussianSource)

/-- Exact derivative of the reflection-adapted Gaussian profile. -/
theorem deriv_deningerMeyerReflectedLogGaussianSource (t : ℝ) :
    deriv (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) t =
      (((-1 / 2 - 2 * Real.pi * t : ℝ) : ℂ) *
        (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) t) := by
  have hinner : HasDerivAt
      (fun x : ℝ => -x / 2 - Real.pi * x ^ 2)
      (-1 / 2 - 2 * Real.pi * t) t := by
    convert ((hasDerivAt_id t).neg.div_const 2).sub
      (((hasDerivAt_const t Real.pi).mul ((hasDerivAt_id t).pow 2)))
      using 1
    all_goals try rfl
    all_goals simp only [id_eq]
    all_goals ring_nf
  have hreal := (Real.hasDerivAt_exp
    (-t / 2 - Real.pi * t ^ 2)).comp t hinner
  have hcomplex := hreal.ofReal_comp
  have hfun :
      (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) =
        fun x : ℝ => ((Real.exp (-x / 2 - Real.pi * x ^ 2) : ℝ) : ℂ) := by
    funext x
    rw [deningerMeyerReflectedLogGaussianSource_apply, gaussReal,
      Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    ring_nf
  calc
    deriv (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) t =
        ((Real.exp (-t / 2 - Real.pi * t ^ 2) : ℝ) : ℂ) *
          (((-1 / 2 - 2 * Real.pi * t : ℝ) : ℂ)) := by
      rw [hfun]
      simpa only [Function.comp_apply, Complex.ofReal_mul] using hcomplex.deriv
    _ = (((-1 / 2 - 2 * Real.pi * t : ℝ) : ℂ) *
        (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) t) := by
      rw [hfun]
      ring_nf

/-- The constructed source is literally `t ↦ t h_ref(t)`. -/
theorem deningerMeyerReflectedLogGaussianMomentSource_apply (t : ℝ) :
    (deningerMeyerReflectedLogGaussianMomentSource : ℝ → ℂ) t =
      (t : ℂ) *
        (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) t := by
  simp only [deningerMeyerReflectedLogGaussianMomentSource,
    deningerMeyerStrongLogDerivative, Submodule.coe_smul,
    Submodule.coe_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  change (-1 / (2 * π)) *
      (deriv (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) t +
        (1 / 2) *
          (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) t) = _
  rw [deriv_deningerMeyerReflectedLogGaussianSource]
  have hpi : (π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf

/-- Zeroth Mellin evaluation of the moment source is the first jet of the
original Gaussian. -/
theorem deningerMeyerReflectedLogGaussianMomentSource_mellin (s : ℂ) :
    deningerMeyerStrongLogMellin
        deningerMeyerReflectedLogGaussianMomentSource s =
      deningerMeyerStrongLogMellinJetLM 1 s
        deningerMeyerReflectedLogGaussianSource := by
  rw [deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
    iteratedDeriv_deningerMeyerStrongLogMellin_eq_integral_jet
      deningerMeyerReflectedLogGaussianSource.property]
  apply integral_congr_ae
  filter_upwards with t
  rw [deningerMeyerStrongLogMellinJet, deningerMeyerStrongLogMellinJet,
    deningerMeyerReflectedLogGaussianMomentSource_apply]
  ring_nf

/-- The logarithmic moment occupies the anti-reflected source sector. -/
theorem deningerMeyerReflectedLogGaussianMomentSource_J_antiFixed :
    deningerMeyerStrongLogJ
        deningerMeyerReflectedLogGaussianMomentSource =
      -deningerMeyerReflectedLogGaussianMomentSource := by
  apply Subtype.ext
  funext t
  rw [deningerMeyerStrongLogJ_apply,
    deningerMeyerReflectedLogGaussianMomentSource_apply]
  simp only [Submodule.coe_neg, Pi.neg_apply]
  rw [deningerMeyerReflectedLogGaussianMomentSource_apply]
  have hfixed := congrArg
    (fun g : DeningerMeyerStrongLogTarget => (g : ℝ → ℂ) t)
    deningerMeyerReflectedLogGaussianSource_J_fixed
  change (Real.exp (-t) : ℂ) *
      (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) (-t) =
    (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) t at hfixed
  calc
    (Real.exp (-t) : ℂ) *
          (((-t : ℝ) : ℂ) *
            (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) (-t)) =
        ((-t : ℝ) : ℂ) *
          ((Real.exp (-t) : ℂ) *
            (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) (-t)) := by
      ring_nf
    _ = -((t : ℂ) *
        (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) t) := by
      rw [hfixed]
      push_cast
      ring_nf

/-- Honest Meyer middle class of the logarithmic moment source. -/
def deningerMeyerReflectedLogGaussianMomentCohomologyClass :
    DeningerMeyerStrongLogCohomology :=
  Submodule.Quotient.mk deningerMeyerReflectedLogGaussianMomentSource

/-- Anti-reflection survives passage to Meyer cohomology. -/
theorem deningerMeyerReflectedLogGaussianMomentCohomologyClass_J_antiFixed :
    deningerMeyerStrongLogCohomologyJ
        deningerMeyerReflectedLogGaussianMomentCohomologyClass =
      -deningerMeyerReflectedLogGaussianMomentCohomologyClass := by
  rw [deningerMeyerReflectedLogGaussianMomentCohomologyClass,
    deningerMeyerStrongLogCohomologyJ_mk,
    deningerMeyerReflectedLogGaussianMomentSource_J_antiFixed]
  rfl

/-- Every first source jet is therefore a zeroth evaluation of one fixed,
target-free Meyer cohomology class. -/
theorem deningerMeyerReflectedLogGaussianMomentCohomologyClass_evaluation
    (q : XiZeroCopy) :
    deningerMeyerXiSupportJetEvaluationLM q.1
        (⟨0, xiSupportMultiplicity_pos q.1⟩ :
          DeningerArithmeticJetIndex q.1)
        deningerMeyerReflectedLogGaussianMomentCohomologyClass =
      deningerMeyerReflectedGaussianMellinFirstJet q := by
  rw [deningerMeyerReflectedLogGaussianMomentCohomologyClass,
    deningerMeyerXiSupportJetEvaluationLM_mk]
  simpa [deningerMeyerReflectedGaussianMellinFirstJet,
    deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv] using
      deningerMeyerReflectedLogGaussianMomentSource_mellin (q.1 : ℂ)

/-- Zeroth evaluation of the reflected Gaussian class is its zeroth jet. -/
theorem deningerMeyerReflectedLogGaussianCohomologyClass_evaluation
    (q : XiZeroCopy) :
    deningerMeyerXiSupportJetEvaluationLM q.1
        (⟨0, xiSupportMultiplicity_pos q.1⟩ :
          DeningerArithmeticJetIndex q.1)
        deningerMeyerReflectedLogGaussianCohomologyClass =
      deningerMeyerReflectedGaussianMellinZeroJet q := by
  rw [deningerMeyerReflectedGaussianMellinZeroJet_eq_horizonGrade]
  exact (reflectedGaussianHorizonGrade_eq_sourceEvaluation q).symm

/-- Critical-line reflection conjugates the zeroth Gaussian jet. -/
theorem deningerMeyerReflectedGaussianMellinZeroJet_lineConj
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianMellinZeroJet
        (xiZeroCopyLineConjEquiv q) =
      starRingEnd ℂ (deningerMeyerReflectedGaussianMellinZeroJet q) := by
  rw [deningerMeyerReflectedGaussianMellinZeroJet_eq_horizonGrade,
    deningerMeyerReflectedGaussianMellinZeroJet_eq_horizonGrade,
    reflectedGaussianHorizonGrade_lineConj]

/-- Critical-line reflection anti-conjugates the logarithmic-moment source
evaluation.  This is the source-level even/odd Hodge split. -/
theorem deningerMeyerReflectedGaussianMellinFirstJet_lineConj
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianMellinFirstJet
        (xiZeroCopyLineConjEquiv q) =
      -starRingEnd ℂ (deningerMeyerReflectedGaussianMellinFirstJet q) := by
  rw [deningerMeyerReflectedGaussianMellinFirstJet_eq_centered_mul_zeroJet,
    deningerMeyerReflectedGaussianMellinFirstJet_eq_centered_mul_zeroJet,
    deningerMeyerReflectedGaussianMellinZeroJet_lineConj]
  have hline : ((xiZeroCopyLineConjEquiv q).1 : ℂ) =
      1 - starRingEnd ℂ (q.1 : ℂ) := rfl
  rw [hline]
  simp only [map_mul, map_div₀, map_sub, map_one, map_ofNat,
    Complex.conj_ofReal]
  ring_nf

/-- The zeroth Gaussian jet never erases a divisor copy. -/
theorem deningerMeyerReflectedGaussianMellinZeroJet_ne_zero
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianMellinZeroJet q ≠ 0 := by
  rw [deningerMeyerReflectedGaussianMellinZeroJet_eq]
  exact Complex.exp_ne_zero _

/-- Alternating two-point, two-jet determinant of one target-free source. -/
def deningerMeyerReflectedGaussianLineWronskian (q : XiZeroCopy) : ℂ :=
  deningerMeyerReflectedGaussianMellinFirstJet q *
      deningerMeyerReflectedGaussianMellinZeroJet
        (xiZeroCopyLineConjEquiv q) -
    deningerMeyerReflectedGaussianMellinZeroJet q *
      deningerMeyerReflectedGaussianMellinFirstJet
        (xiZeroCopyLineConjEquiv q)

/-- Same determinant written entirely with zeroth evaluations of two honest
Meyer cohomology classes.  Hence no first-jet multiplicity assumption occurs. -/
def deningerMeyerReflectedGaussianCohomologyLineWronskian
    (q : XiZeroCopy) : ℂ :=
  deningerMeyerXiSupportJetEvaluationLM q.1
      (⟨0, xiSupportMultiplicity_pos q.1⟩ :
        DeningerArithmeticJetIndex q.1)
      deningerMeyerReflectedLogGaussianMomentCohomologyClass *
    deningerMeyerXiSupportJetEvaluationLM
      (xiZeroCopyLineConjEquiv q).1
      (⟨0, xiSupportMultiplicity_pos (xiZeroCopyLineConjEquiv q).1⟩ :
        DeningerArithmeticJetIndex (xiZeroCopyLineConjEquiv q).1)
      deningerMeyerReflectedLogGaussianCohomologyClass -
  deningerMeyerXiSupportJetEvaluationLM q.1
      (⟨0, xiSupportMultiplicity_pos q.1⟩ :
        DeningerArithmeticJetIndex q.1)
      deningerMeyerReflectedLogGaussianCohomologyClass *
    deningerMeyerXiSupportJetEvaluationLM
      (xiZeroCopyLineConjEquiv q).1
      (⟨0, xiSupportMultiplicity_pos (xiZeroCopyLineConjEquiv q).1⟩ :
        DeningerArithmeticJetIndex (xiZeroCopyLineConjEquiv q).1)
      deningerMeyerReflectedLogGaussianMomentCohomologyClass

/-- The cohomological two-source determinant is literally the first-jet
Wronskian. -/
theorem deningerMeyerReflectedGaussianCohomologyLineWronskian_eq
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianCohomologyLineWronskian q =
      deningerMeyerReflectedGaussianLineWronskian q := by
  rw [deningerMeyerReflectedGaussianCohomologyLineWronskian,
    deningerMeyerReflectedGaussianLineWronskian,
    deningerMeyerReflectedLogGaussianMomentCohomologyClass_evaluation,
    deningerMeyerReflectedLogGaussianMomentCohomologyClass_evaluation,
    deningerMeyerReflectedLogGaussianCohomologyClass_evaluation,
    deningerMeyerReflectedLogGaussianCohomologyClass_evaluation]

/-- The determinant is the unsquared Hermitian cross-polarization between
the anti-reflected moment class and the reflected Gaussian class. -/
theorem deningerMeyerReflectedGaussianLineWronskian_eq_hermitian_cross
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskian q =
      deningerMeyerReflectedGaussianMellinFirstJet q *
          starRingEnd ℂ
            (deningerMeyerReflectedGaussianMellinZeroJet q) +
        deningerMeyerReflectedGaussianMellinZeroJet q *
          starRingEnd ℂ
            (deningerMeyerReflectedGaussianMellinFirstJet q) := by
  rw [deningerMeyerReflectedGaussianLineWronskian,
    deningerMeyerReflectedGaussianMellinZeroJet_lineConj,
    deningerMeyerReflectedGaussianMellinFirstJet_lineConj]
  ring_nf

/-- Real form of the unsquared cross-polarization.  This identifies the
source Wronskian with the exact Hermitian orientation trace requested by the
Hellinger--Hodge descent frontier. -/
theorem deningerMeyerReflectedGaussianLineWronskian_eq_two_re_cross
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskian q =
      ((2 * (deningerMeyerReflectedGaussianMellinFirstJet q *
        starRingEnd ℂ
          (deningerMeyerReflectedGaussianMellinZeroJet q)).re : ℝ) : ℂ) := by
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_hermitian_cross]
  simpa only [map_mul, starRingEnd_self_apply, mul_comm] using
    Complex.add_conj
      (deningerMeyerReflectedGaussianMellinFirstJet q *
        starRingEnd ℂ (deningerMeyerReflectedGaussianMellinZeroJet q))

/-- Nowhere-zero Gaussian pair scale in the Wronskian comparison. -/
def deningerMeyerReflectedGaussianLinePairScale (q : XiZeroCopy) : ℂ :=
  (1 / (2 * π)) * deningerMeyerReflectedGaussianMellinZeroJet q *
    deningerMeyerReflectedGaussianMellinZeroJet
      (xiZeroCopyLineConjEquiv q)

/-- The pair scale is nonzero at every actual divisor copy. -/
theorem deningerMeyerReflectedGaussianLinePairScale_ne_zero
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLinePairScale q ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact one_div_ne_zero
        (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    · exact deningerMeyerReflectedGaussianMellinZeroJet_ne_zero q
  · exact deningerMeyerReflectedGaussianMellinZeroJet_ne_zero
      (xiZeroCopyLineConjEquiv q)

/-- The comparison scale is not merely nonzero: it is the positive Hermitian
square of the fixed source value, divided by `2π`. -/
theorem deningerMeyerReflectedGaussianLinePairScale_eq_normSq
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLinePairScale q =
      ((Complex.normSq
          (deningerMeyerReflectedGaussianMellinZeroJet q) /
        (2 * Real.pi) : ℝ) : ℂ) := by
  rw [deningerMeyerReflectedGaussianLinePairScale,
    deningerMeyerReflectedGaussianMellinZeroJet_lineConj]
  calc
    (1 / (2 * π)) * deningerMeyerReflectedGaussianMellinZeroJet q *
          starRingEnd ℂ
            (deningerMeyerReflectedGaussianMellinZeroJet q) =
        (1 / (2 * π)) *
          (deningerMeyerReflectedGaussianMellinZeroJet q *
            starRingEnd ℂ
              (deningerMeyerReflectedGaussianMellinZeroJet q)) := by ring_nf
    _ = ((Complex.normSq
          (deningerMeyerReflectedGaussianMellinZeroJet q) /
        (2 * Real.pi) : ℝ) : ℂ) := by
      rw [Complex.mul_conj]
      push_cast
      ring_nf

/-- Strict positivity of the Hermitian normalization. -/
theorem deningerMeyerReflectedGaussianLinePairScale_re_pos
    (q : XiZeroCopy) :
    0 < (deningerMeyerReflectedGaussianLinePairScale q).re := by
  rw [deningerMeyerReflectedGaussianLinePairScale_eq_normSq]
  change 0 < Complex.normSq
      (deningerMeyerReflectedGaussianMellinZeroJet q) / (2 * Real.pi)
  exact div_pos
    (Complex.normSq_pos.mpr
      (deningerMeyerReflectedGaussianMellinZeroJet_ne_zero q))
    (mul_pos (by norm_num) Real.pi_pos)

/-- **Source/Green coupling law.**  The line-reflected first-jet determinant
is exactly the horizontal Green fracture times a nonzero Gaussian scale. -/
theorem deningerMeyerReflectedGaussianLineWronskian_eq_greenFracture_mul
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskian q =
      xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) *
        deningerMeyerReflectedGaussianLinePairScale q := by
  rw [deningerMeyerReflectedGaussianLineWronskian,
    deningerMeyerReflectedGaussianLinePairScale,
    deningerMeyerReflectedGaussianMellinFirstJet_eq,
    deningerMeyerReflectedGaussianMellinFirstJet_eq,
    deningerMeyerReflectedGaussianMellinZeroJet_eq,
    deningerMeyerReflectedGaussianMellinZeroJet_eq,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  have hline : ((xiZeroCopyLineConjEquiv q).1 : ℂ) =
      1 - starRingEnd ℂ (q.1 : ℂ) := rfl
  rw [hline]
  have hpi : (π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  apply Complex.ext
  · simp
    ring_nf
  · simp
    ring_nf

/-- Explicit real orientation formula.  The determinant is horizontal
displacement times a strictly positive Hermitian Gaussian density. -/
theorem deningerMeyerReflectedGaussianLineWronskian_eq_real_orientation
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskian q =
      (((q.1 : ℂ).re - 1 / 2) *
        (Complex.normSq
          (deningerMeyerReflectedGaussianMellinZeroJet q) / Real.pi) : ℝ) := by
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_greenFracture_mul,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re,
    deningerMeyerReflectedGaussianLinePairScale_eq_normSq]
  push_cast
  ring_nf

/-- The cohomological determinant retains the sign of the resolved
horizontal Green orientation, not merely its zero set. -/
theorem deningerMeyerReflectedGaussianLineWronskian_re_pos_iff
    (q : XiZeroCopy) :
    0 < (deningerMeyerReflectedGaussianLineWronskian q).re ↔
      1 / 2 < (q.1 : ℂ).re := by
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_real_orientation]
  simp only [ofReal_re]
  have hweight : 0 <
      Complex.normSq
        (deningerMeyerReflectedGaussianMellinZeroJet q) / Real.pi :=
    div_pos
      (Complex.normSq_pos.mpr
        (deningerMeyerReflectedGaussianMellinZeroJet_ne_zero q))
      Real.pi_pos
  constructor <;> intro h <;> nlinarith

/-- The source determinant recovers the Green fracture exactly; no target
support selection is hidden in the comparison. -/
theorem xiNearbyPoleDualityAdjunctionFracture_eq_lineWronskian_div_scale
    (q : XiZeroCopy) :
    xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) =
      deningerMeyerReflectedGaussianLineWronskian q /
        deningerMeyerReflectedGaussianLinePairScale q := by
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_greenFracture_mul]
  exact (mul_div_cancel_right₀ _
    (deningerMeyerReflectedGaussianLinePairScale_ne_zero q)).symm

/-- The determinant reverses under critical-line reflection. -/
theorem deningerMeyerReflectedGaussianLineWronskian_lineConj
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskian
        (xiZeroCopyLineConjEquiv q) =
      -deningerMeyerReflectedGaussianLineWronskian q := by
  rw [deningerMeyerReflectedGaussianLineWronskian,
    xiZeroCopyLineConjEquiv_apply_apply,
    deningerMeyerReflectedGaussianLineWronskian]
  ring_nf

/-- Exact local zero set of the source Wronskian. -/
theorem deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskian q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_greenFracture_mul]
  constructor
  · intro hzero
    exact (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (q.1 : ℂ)).mp
      ((mul_eq_zero.mp hzero).resolve_right
        (deningerMeyerReflectedGaussianLinePairScale_ne_zero q))
  · intro hline
    rw [(xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
      (q.1 : ℂ)).2 hline, zero_mul]

/-- Pointwise bound by one fixed multiple of the admitted Gaussian horizon.
It is independent of the divisor coordinate. -/
theorem norm_deningerMeyerReflectedGaussianLineWronskian_le
    (q : XiZeroCopy) :
    ‖deningerMeyerReflectedGaussianLineWronskian q‖ ≤
      (‖(1 / (2 * π) : ℂ)‖ * ‖reflectedGaussianHorizonGradeL2‖) *
        ‖reflectedGaussianHorizonGrade q‖ := by
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_greenFracture_mul,
    deningerMeyerReflectedGaussianLinePairScale,
    norm_mul, norm_mul, norm_mul,
    deningerMeyerReflectedGaussianMellinZeroJet_eq_horizonGrade,
    deningerMeyerReflectedGaussianMellinZeroJet_eq_horizonGrade,
    reflectedGaussianHorizonGrade_lineConj, Complex.norm_conj]
  have hfracture :=
    norm_xiNearbyPoleDualityAdjunctionFracture_le_one q
  have hcoordinate :=
    lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
      reflectedGaussianHorizonGradeL2 q
  rw [reflectedGaussianHorizonGradeL2_apply] at hcoordinate
  calc
    ‖xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ)‖ *
          (‖(1 / (2 * π) : ℂ)‖ *
            ‖reflectedGaussianHorizonGrade q‖ *
              ‖reflectedGaussianHorizonGrade q‖) ≤
        1 * (‖(1 / (2 * π) : ℂ)‖ *
          ‖reflectedGaussianHorizonGrade q‖ *
            ‖reflectedGaussianHorizonGrade q‖) :=
      mul_le_mul_of_nonneg_right hfracture (by positivity)
    _ ≤ (‖(1 / (2 * π) : ℂ)‖ *
          ‖reflectedGaussianHorizonGradeL2‖) *
        ‖reflectedGaussianHorizonGrade q‖ := by
      rw [one_mul]
      gcongr

/-- Global multiplicity-exact landing of the off-diagonal cohomological
Wronskian. -/
def deningerMeyerReflectedGaussianLineWronskianField : XiDivisorL2 :=
  ⟨deningerMeyerReflectedGaussianLineWronskian,
    Memℓp.mono
      ((lp.memℓp reflectedGaussianHorizonGradeL2).norm.const_smul
        (‖(1 / (2 * π) : ℂ)‖ * ‖reflectedGaussianHorizonGradeL2‖))
      (fun q => by
        simpa only [Pi.smul_apply, smul_eq_mul,
          reflectedGaussianHorizonGradeL2_apply, norm_mul,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using
            norm_deningerMeyerReflectedGaussianLineWronskian_le q)⟩

@[simp]
theorem deningerMeyerReflectedGaussianLineWronskianField_apply
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskianField q =
      deningerMeyerReflectedGaussianLineWronskian q :=
  rfl

/-- Every global coordinate remains the exterior determinant of two zeroth
Meyer cohomology evaluations. -/
theorem deningerMeyerReflectedGaussianLineWronskianField_cohomology_apply
    (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskianField q =
      deningerMeyerReflectedGaussianCohomologyLineWronskian q := by
  rw [deningerMeyerReflectedGaussianLineWronskianField_apply,
    deningerMeyerReflectedGaussianCohomologyLineWronskian_eq]

/-- Green's nonzero Hodge factor after completed Riesz conjugation. -/
def adaptivePrimeNormalReflectedHorizonGreenHodgeFactor
    (p : Nat.Primes) (q : XiZeroCopy) : ℂ :=
  deningerArithmeticOrientedHodgeLp
    (deningerArithmeticCompletedRieszConjugation
      (adaptivePrimeNormalReflectedHorizonColumn p)) q

theorem adaptivePrimeNormalReflectedHorizonGreenHodgeFactor_ne_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedHorizonGreenHodgeFactor p q ≠ 0 := by
  rw [adaptivePrimeNormalReflectedHorizonGreenHodgeFactor,
    deningerArithmeticOrientedHodgeLp_apply,
    deningerArithmeticCompletedRieszConjugation_apply]
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (deningerArithmeticFEOrientation_ne_zero q)
  · rw [starRingEnd_self_apply]
    exact adaptivePrimeNormalReflectedHorizonColumn_apply_ne_zero p
      (xiZeroCopyReflectEquiv q)

/-- The actual reflected adaptive Green coefficient has the same fracture,
with its independent nowhere-zero Hodge factor. -/
theorem adaptivePrimeNormalReflectedHorizonGreenCoefficient_eq_fracture_mul
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedHorizonGreenCoefficient p q =
      xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) *
        adaptivePrimeNormalReflectedHorizonGreenHodgeFactor p q := by
  rw [adaptivePrimeNormalReflectedHorizonGreenCoefficient,
    adaptivePrimeNormalReflectedHorizonGreenProvenance,
    deningerArithmeticCompletedGreenProvenance_apply,
    adaptivePrimeNormalReflectedHorizonGreenHodgeFactor]

/-- **Division-free source/Green comparison.**  Cross multiplication removes
both nowhere-zero normalizations and identifies the actual Green record with
the off-diagonal source determinant. -/
theorem deningerMeyerReflectedGaussianLineWronskian_green_cross_comparison
    (p : Nat.Primes) (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskian q *
        adaptivePrimeNormalReflectedHorizonGreenHodgeFactor p q =
      adaptivePrimeNormalReflectedHorizonGreenCoefficient p q *
        deningerMeyerReflectedGaussianLinePairScale q := by
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_greenFracture_mul,
    adaptivePrimeNormalReflectedHorizonGreenCoefficient_eq_fracture_mul]
  ring_nf

/-- The source determinant and actual reflected Green coefficient have
identical pointwise support. -/
theorem deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff_green
    (p : Nat.Primes) (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianLineWronskian q = 0 ↔
      adaptivePrimeNormalReflectedHorizonGreenCoefficient p q = 0 := by
  rw [deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff,
    adaptivePrimeNormalReflectedHorizonGreenCoefficient_eq_zero_iff]

/-- Global vanishing of one target-free source Wronskian is exactly RH. -/
theorem deningerMeyerReflectedGaussianLineWronskian_vanishes_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      deningerMeyerReflectedGaussianLineWronskian q = 0) ↔
      RiemannHypothesis := by
  rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  constructor
  · intro hzero rho
    let q : XiZeroCopy :=
      ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
    exact (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)).2
      ((deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff q).mp
        (hzero q))
  · intro hneutral q
    exact (deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff q).2
      ((xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (q.1 : ℂ)).mp
        (hneutral q.1))

/-- The assembled cohomological exterior packet vanishes exactly under RH. -/
theorem deningerMeyerReflectedGaussianLineWronskianField_eq_zero_iff_riemannHypothesis :
    deningerMeyerReflectedGaussianLineWronskianField = 0 ↔
      RiemannHypothesis := by
  rw [←
    deningerMeyerReflectedGaussianLineWronskian_vanishes_iff_riemannHypothesis]
  constructor
  · intro hzero q
    have hq := congrArg (fun a : XiDivisorL2 => a q) hzero
    simpa using hq
  · intro hzero
    apply lp.ext
    funext q
    exact hzero q

/-- Global Wronskian packet and actual reflected adaptive Green record have
the same vanishing locus as vectors. -/
theorem deningerMeyerReflectedGaussianLineWronskianField_eq_zero_iff_green
    (p : Nat.Primes) :
    deningerMeyerReflectedGaussianLineWronskianField = 0 ↔
      adaptivePrimeNormalReflectedHorizonGreenProvenance p = 0 := by
  rw [deningerMeyerReflectedGaussianLineWronskianField_eq_zero_iff_riemannHypothesis,
    adaptivePrimeNormalReflectedHorizonGreenProvenance_eq_zero_iff_riemannHypothesis]

/-- Any source-derived factorization of the determinant through a
line-reflection-invariant arithmetic observation would close RH.  This is the
remaining incidence statement, not a premise used above. -/
theorem riemannHypothesis_of_gaussianLineWronskian_factorization
    {Q : Type*} (obs : XiZeroCopy → Q) (d : Q → ℂ)
    (hπ : ∀ q : XiZeroCopy,
      obs (xiZeroCopyLineConjEquiv q) = obs q)
    (hfactor : ∀ q : XiZeroCopy,
      deningerMeyerReflectedGaussianLineWronskian q = d (obs q)) :
    RiemannHypothesis := by
  rw [← deningerMeyerReflectedGaussianLineWronskian_vanishes_iff_riemannHypothesis]
  intro q
  have heven :
      deningerMeyerReflectedGaussianLineWronskian
          (xiZeroCopyLineConjEquiv q) =
        deningerMeyerReflectedGaussianLineWronskian q := by
    rw [hfactor, hfactor, hπ]
  rw [deningerMeyerReflectedGaussianLineWronskian_lineConj] at heven
  linear_combination (-1 / 2 : ℂ) * heven

end DeningerMeyerGaussianGreen

end

end RHTower
