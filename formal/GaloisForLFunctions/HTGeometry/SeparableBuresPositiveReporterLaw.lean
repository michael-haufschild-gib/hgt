import GaloisForLFunctions.HTGeometry.SeparableBuresCompactTargetBody
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
import Mathlib.Topology.Sion

/-!
# Positive reporters for separable trace-class Bures geometry

This file builds the genuine bounded-operator trace pairing between a Schatten-one covariance and
a bounded reporter.  For positive covariances it identifies that pairing with the exact
Hilbert--Schmidt energy after applying the positive square root of the reporter.  The resulting
factorization proves the infinite-dimensional Alberti lower inequality for every bounded strictly
positive invertible reporter.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap Set
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Real trace pairing `Re Tr(MA)` of a Schatten-one operator with a bounded reporter. -/
def separableBuresTracePairing (M : SchattenOneOperator H) (A : H →L[ℂ] H) : ℝ :=
  Complex.re (opTrace ((M : H →L[ℂ] H) ∘L A))

/-- Complex trace pairing as a continuous linear functional in the Schatten-one variable. -/
noncomputable def schattenOneTracePairingCLM (A : H →L[ℂ] H) :
    SchattenOneOperator H →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun M => opTrace ((M : H →L[ℂ] H) ∘L A)
      map_add' := fun M N => by
        rw [SchattenOneOperator.coe_add, add_comp]
        exact opTrace_add_of_memSchattenClass_one
          (memSchattenClass_one_comp_right M.property A)
          (memSchattenClass_one_comp_right N.property A)
      map_smul' := fun c M => by
        rw [SchattenOneOperator.coe_smul, smul_comp, opTrace_smul]
        rfl }
    ‖A‖ fun M => by
      calc
        ‖opTrace ((M : H →L[ℂ] H) ∘L A)‖ ≤
            traceNorm H ((M : H →L[ℂ] H) ∘L A) :=
          norm_opTrace_le_traceNorm (memSchattenClass_one_comp_right M.property A)
        _ ≤ traceNorm H (M : H →L[ℂ] H) * ‖A‖ :=
          traceNorm_comp_right_le M.summable A
        _ = ‖A‖ * ‖M‖ := by
          rw [SchattenOneOperator.norm_def]
          ring

@[simp] theorem schattenOneTracePairingCLM_apply
    (A : H →L[ℂ] H) (M : SchattenOneOperator H) :
    schattenOneTracePairingCLM A M =
      opTrace ((M : H →L[ℂ] H) ∘L A) := rfl

theorem continuous_separableBuresTracePairing_left (A : H →L[ℂ] H) :
    Continuous (fun M : SchattenOneOperator H => separableBuresTracePairing M A) :=
  Complex.continuous_re.comp (schattenOneTracePairingCLM A).continuous

/-- Complex trace pairing as a continuous linear functional in the bounded reporter variable. -/
noncomputable def boundedTracePairingCLM (M : SchattenOneOperator H) :
    (H →L[ℂ] H) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun A => opTrace ((M : H →L[ℂ] H) ∘L A)
      map_add' := fun A B => by
        rw [comp_add]
        exact opTrace_add_of_memSchattenClass_one
          (memSchattenClass_one_comp_right M.property A)
          (memSchattenClass_one_comp_right M.property B)
      map_smul' := fun c A => by
        rw [comp_smul, opTrace_smul]
        rfl }
    ‖M‖ fun A => by
      calc
        ‖opTrace ((M : H →L[ℂ] H) ∘L A)‖ ≤
            traceNorm H ((M : H →L[ℂ] H) ∘L A) :=
          norm_opTrace_le_traceNorm (memSchattenClass_one_comp_right M.property A)
        _ ≤ traceNorm H (M : H →L[ℂ] H) * ‖A‖ :=
          traceNorm_comp_right_le M.summable A
        _ = ‖M‖ * ‖A‖ := by rw [SchattenOneOperator.norm_def]

theorem continuous_separableBuresTracePairing_right (M : SchattenOneOperator H) :
    Continuous (separableBuresTracePairing M) :=
  Complex.continuous_re.comp (boundedTracePairingCLM M).continuous

theorem separableBuresTracePairing_add_left
    (M N : SchattenOneOperator H) (A : H →L[ℂ] H) :
    separableBuresTracePairing (M + N) A =
      separableBuresTracePairing M A + separableBuresTracePairing N A := by
  change Complex.re (schattenOneTracePairingCLM A (M + N)) = _
  rw [map_add, Complex.add_re]
  rfl

theorem separableBuresTracePairing_real_smul_left
    (c : ℝ) (M : SchattenOneOperator H) (A : H →L[ℂ] H) :
    separableBuresTracePairing (c • M) A =
      c * separableBuresTracePairing M A := by
  change Complex.re (schattenOneTracePairingCLM A ((c : ℂ) • M)) = _
  rw [map_smul]
  change (((c : ℂ) * schattenOneTracePairingCLM A M).re) = _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

theorem separableBuresTracePairing_add_right
    (M : SchattenOneOperator H) (A B : H →L[ℂ] H) :
    separableBuresTracePairing M (A + B) =
      separableBuresTracePairing M A + separableBuresTracePairing M B := by
  change Complex.re (boundedTracePairingCLM M (A + B)) = _
  rw [map_add, Complex.add_re]
  rfl

theorem separableBuresTracePairing_real_smul_right
    (c : ℝ) (M : SchattenOneOperator H) (A : H →L[ℂ] H) :
    separableBuresTracePairing M (c • A) =
      c * separableBuresTracePairing M A := by
  change Complex.re (boundedTracePairingCLM M ((c : ℂ) • A)) = _
  rw [map_smul]
  change (((c : ℂ) * boundedTracePairingCLM M A).re) = _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- Positive square root of every positive Schatten-one operator is Hilbert--Schmidt. -/
theorem positiveSchattenOne_sqrt_isHilbertSchmidt
    (M : SchattenOneOperator H) (hM : (M : H →L[ℂ] H).IsPositive) :
    (CFC.sqrt (M : H →L[ℂ] H)).IsHilbertSchmidt := by
  have hM0 : (0 : H →L[ℂ] H) ≤ (M : H →L[ℂ] H) :=
    (nonneg_iff_isPositive _).2 hM
  have hMstar : star (M : H →L[ℂ] H) = (M : H →L[ℂ] H) :=
    (IsSelfAdjoint.of_nonneg hM0).star_eq
  have habs : absOp (M : H →L[ℂ] H) = (M : H →L[ℂ] H) := by
    unfold absOp
    rw [hMstar]
    exact CFC.sqrt_mul_self (M : H →L[ℂ] H) hM0
  have hroot := traceClassRoot_isHilbertSchmidt M.property
  simpa [traceClassRoot, habs] using hroot

/-- Positive trace pairing is exactly reporter-weighted Hilbert--Schmidt energy. -/
theorem separableBuresTracePairing_eq_hsNormSq
    (M : SchattenOneOperator H) (hM : (M : H →L[ℂ] H).IsPositive)
    (A : H →L[ℂ] H) (hA : 0 ≤ A) :
    separableBuresTracePairing M A =
      hsNormSq (CFC.sqrt A ∘L CFC.sqrt (M : H →L[ℂ] H)) := by
  let R : H →L[ℂ] H := CFC.sqrt (M : H →L[ℂ] H)
  let P : H →L[ℂ] H := CFC.sqrt A
  let T : H →L[ℂ] H := P ∘L R
  have hR : R.IsHilbertSchmidt := positiveSchattenOne_sqrt_isHilbertSchmidt M hM
  have hPstar : adjoint P = P := by
    exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
  have hRstar : adjoint R = R := by
    exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (M : H →L[ℂ] H))
  have hP2 : P ∘L P = A := CFC.sqrt_mul_sqrt_self A hA
  have hR2 : R ∘L R = (M : H →L[ℂ] H) :=
    CFC.sqrt_mul_sqrt_self _ ((nonneg_iff_isPositive _).2 hM)
  have hT : T.IsHilbertSchmidt := hR.comp_left P
  have hcyc : opTrace (R ∘L (A ∘L R)) = opTrace ((A ∘L R) ∘L R) :=
    opTrace_comp_comm hR (hR.comp_left A)
  have htrace : opTrace ((M : H →L[ℂ] H) ∘L A) =
      opTrace (adjoint T ∘L T) := by
    have hAM : A ∘L (M : H →L[ℂ] H) = (A ∘L R) ∘L R := by
      rw [← hR2, comp_assoc]
    have henergy : adjoint T ∘L T = R ∘L (A ∘L R) := by
      calc
        adjoint T ∘L T = (R ∘L P) ∘L (P ∘L R) := by
          simp only [T, adjoint_comp, hRstar, hPstar]
        _ = R ∘L ((P ∘L P) ∘L R) := by
          simp only [comp_assoc]
        _ = R ∘L (A ∘L R) := by rw [hP2]
    calc
      opTrace ((M : H →L[ℂ] H) ∘L A) =
          opTrace (A ∘L (M : H →L[ℂ] H)) :=
        M.property.one_opTrace_comp_comm A |>.symm
      _ = opTrace ((A ∘L R) ∘L R) := by rw [hAM]
      _ = opTrace (R ∘L (A ∘L R)) := hcyc.symm
      _ = opTrace (adjoint T ∘L T) := by rw [henergy]
  unfold separableBuresTracePairing
  rw [htrace]
  change RCLike.re (opTrace (adjoint T ∘L T)) = _
  simpa only [T, P, R] using re_opTrace_adjoint_comp_self hT

theorem separableBuresTracePairing_nonneg
    (M : SchattenOneOperator H) (hM : (M : H →L[ℂ] H).IsPositive)
    (A : H →L[ℂ] H) (hA : 0 ≤ A) :
    0 ≤ separableBuresTracePairing M A := by
  rw [separableBuresTracePairing_eq_hsNormSq M hM A hA]
  exact hsNormSq_nonneg _

/-- Strictly positive bounded reporters form a convex cone slice. -/
theorem convex_strictlyPositiveReporters :
    Convex ℝ {A : H →L[ℂ] H | IsStrictlyPositive A} := by
  intro A hA B hB a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hB
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hA
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  exact (hA.smul haPos).add_nonneg (smul_nonneg hb hB.nonneg)

/-- Infinite-dimensional positive-reporter half-sum. -/
def separableBuresReporterHalfSum
    (C M : SchattenOneOperator H) (A : H →L[ℂ] H) : ℝ :=
  (separableBuresTracePairing C A +
    separableBuresTracePairing M (Ring.inverse A)) / 2

/-- **Infinite Alberti lower law.**  Every bounded strictly-positive invertible reporter dominates
the Bures root fidelity of an arbitrary positive Schatten-one pair. -/
theorem operatorBuresRootFidelity_le_separableReporterHalfSum
    (C M : SchattenOneOperator H)
    (hC : (C : H →L[ℂ] H).IsPositive)
    (hM : (M : H →L[ℂ] H).IsPositive)
    (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) :
    operatorBuresRootFidelity (C : H →L[ℂ] H) (M : H →L[ℂ] H) ≤
      separableBuresReporterHalfSum C M A := by
  let RC : H →L[ℂ] H := CFC.sqrt (C : H →L[ℂ] H)
  let RM : H →L[ℂ] H := CFC.sqrt (M : H →L[ℂ] H)
  let P : H →L[ℂ] H := CFC.sqrt A
  let Q : H →L[ℂ] H := CFC.sqrt (Ring.inverse A)
  let X : H →L[ℂ] H := RC ∘L P
  let Y : H →L[ℂ] H := Q ∘L RM
  have hRC : RC.IsHilbertSchmidt := positiveSchattenOne_sqrt_isHilbertSchmidt C hC
  have hRM : RM.IsHilbertSchmidt := positiveSchattenOne_sqrt_isHilbertSchmidt M hM
  have hPstar : adjoint P = P :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
  have hRCstar : adjoint RC = RC :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (C : H →L[ℂ] H))
  have hQeq : Q = Ring.inverse P := by
    exact CFC.sqrt_ringInverse
  have hPunit : IsUnit P := hA.isUnit_cfcSqrt A
  have hPQ : P ∘L Q = 1 := by
    rw [hQeq]
    simpa only [ContinuousLinearMap.mul_def] using Ring.mul_inverse_cancel P hPunit
  have hX : X.IsHilbertSchmidt := hRC.comp_right P
  have hY : Y.IsHilbertSchmidt := hRM.comp_left Q
  have hfactor : X ∘L Y = RC ∘L RM := by
    calc
      X ∘L Y = RC ∘L ((P ∘L Q) ∘L RM) := by
        simp only [X, Y, comp_assoc]
      _ = RC ∘L RM := by
        rw [hPQ]
        simpa only [ContinuousLinearMap.mul_def] using
          congrArg (fun Z : H →L[ℂ] H => RC * Z) (one_mul RM)
  have hnuclear : traceNorm H (RC ∘L RM) ≤ hsNorm X * hsNorm Y := by
    rw [← hfactor]
    exact tsum_approxNumber_comp_le hX hY
  have hsource : hsNorm X ^ 2 = separableBuresTracePairing C A := by
    rw [separableBuresTracePairing_eq_hsNormSq C hC A hA.nonneg]
    have hPRC : (P ∘L RC).IsHilbertSchmidt := hRC.comp_left P
    have hXeq : X = adjoint (P ∘L RC) := by
      simp only [X, adjoint_comp, hRCstar, hPstar]
    rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg X), hXeq,
      hPRC.hsNormSq_adjoint]
  have htarget : hsNorm Y ^ 2 =
      separableBuresTracePairing M (Ring.inverse A) := by
    rw [separableBuresTracePairing_eq_hsNormSq M hM (Ring.inverse A)
      hA.ringInverse.nonneg]
    rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg Y)]
  unfold operatorBuresRootFidelity separableBuresReporterHalfSum
  change traceNorm H (RC ∘L RM) ≤ _
  calc
    traceNorm H (RC ∘L RM) ≤ hsNorm X * hsNorm Y := hnuclear
    _ ≤ (hsNorm X ^ 2 + hsNorm Y ^ 2) / 2 := by
      nlinarith [sq_nonneg (hsNorm X - hsNorm Y)]
    _ = (separableBuresTracePairing C A +
        separableBuresTracePairing M (Ring.inverse A)) / 2 := by
      rw [hsource, htarget]

end RHTower
