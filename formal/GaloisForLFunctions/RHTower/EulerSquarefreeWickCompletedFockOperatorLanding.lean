import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedFactorialFockLanding
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.HTGeometry.PolarizedExactnessHorizonRelativeConnesPhaseLaw
import GaloisForLFunctions.RHTower.XiCriticalLineIntegrality
import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedJetHorizontalFaithfulness

/-!
# Completed EWQ Fock-operator landing

The completed EWQ jet is now an honest nonzero `ℓ²` vector, so its positive ray gives a
rank-one Schatten-class operator.  This module uses that ray as the off-diagonal block of one
bounded triangular operator whose scalar diagonal is Riemann Xi.

The result is coefficient-faithful at operator level: the block operator is nowhere zero and is
square-zero exactly on the Xi divisor.  Its EWQ block is positive and trace class, and the full
family obeys an exact unitary reflection intertwiner.  This replaces the earlier product of finite
jet matrices by a single bounded operator that can enter Fredholm, trace, recurrence, and quantum
observer constructions without selecting a derivative coordinate.
-/

open Complex Matrix
open scoped ENNReal InnerProductSpace Matrix

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

abbrev EulerWickCompletedFockSpace := lp (fun _ : ℕ => ℂ) 2

/-- Positive rank-one operator carrying the full completed EWQ Fock color. -/
def eulerWickCompletedFockColorProjector (s : ℂ) :
    EulerWickCompletedFockSpace →L[ℂ] EulerWickCompletedFockSpace :=
  InnerProductSpace.rankOne ℂ
    (eulerWickPrimitiveCompletedInteractionFockVector s)
    (eulerWickPrimitiveCompletedInteractionFockVector s)

@[simp] theorem eulerWickCompletedFockColorProjector_apply
    (s : ℂ) (x : EulerWickCompletedFockSpace) :
    eulerWickCompletedFockColorProjector s x =
      inner ℂ (eulerWickPrimitiveCompletedInteractionFockVector s) x •
        eulerWickPrimitiveCompletedInteractionFockVector s := rfl

theorem eulerWickCompletedFockColorProjector_ne_zero (s : ℂ) :
    eulerWickCompletedFockColorProjector s ≠ 0 := by
  intro hzero
  let v := eulerWickPrimitiveCompletedInteractionFockVector s
  have hv : v ≠ 0 := eulerWickPrimitiveCompletedInteractionFockVector_ne_zero s
  have happly := congrArg (fun T : EulerWickCompletedFockSpace →L[ℂ]
      EulerWickCompletedFockSpace => T v) hzero
  have hinner : inner ℂ v v ≠ 0 := inner_self_ne_zero.mpr hv
  exact (smul_ne_zero hinner hv) (by simpa [v] using happly)

theorem eulerWickCompletedFockColorProjector_isPositive (s : ℂ) :
    (eulerWickCompletedFockColorProjector s).IsPositive := by
  exact InnerProductSpace.isPositive_rankOne_self
    (eulerWickPrimitiveCompletedInteractionFockVector s)

/-- Same color bundled in the corpus Schatten-one Banach carrier. -/
def eulerWickCompletedFockColorTraceClass (s : ℂ) :
    _root_.RHTower.SchattenOneOperator EulerWickCompletedFockSpace :=
  _root_.RHTower.positiveRankOneSchattenOne
    (eulerWickPrimitiveCompletedInteractionFockVector s)

@[simp] theorem eulerWickCompletedFockColorTraceClass_coe (s : ℂ) :
    (eulerWickCompletedFockColorTraceClass s :
      EulerWickCompletedFockSpace →L[ℂ] EulerWickCompletedFockSpace) =
      eulerWickCompletedFockColorProjector s := rfl

@[simp] theorem norm_eulerWickCompletedFockColorTraceClass (s : ℂ) :
    ‖eulerWickCompletedFockColorTraceClass s‖ =
      ‖eulerWickPrimitiveCompletedInteractionFockVector s‖ ^ 2 :=
  _root_.RHTower.norm_positiveRankOneSchattenOne _

/-- Block-Hilbert completed Xi landing: scalar Xi diagonal plus positive rank-one EWQ color. -/
def eulerWickCompletedFockOperatorLanding (s : ℂ) :
    Matrix (Fin 2) (Fin 2)
      (EulerWickCompletedFockSpace →L[ℂ] EulerWickCompletedFockSpace) :=
  !![(_root_.RHTower.xi s) • 1, eulerWickCompletedFockColorProjector s;
     0, (_root_.RHTower.xi s) • 1]

theorem eulerWickCompletedFockOperatorLanding_ne_zero (s : ℂ) :
    eulerWickCompletedFockOperatorLanding s ≠ 0 := by
  intro hzero
  have h01 := congrFun (congrFun hzero (0 : Fin 2)) (1 : Fin 2)
  simp only [eulerWickCompletedFockOperatorLanding] at h01
  exact eulerWickCompletedFockColorProjector_ne_zero s h01

theorem eulerWickCompletedFockOperatorLanding_squareZero_iff (s : ℂ) :
    eulerWickCompletedFockOperatorLanding s *
        eulerWickCompletedFockOperatorLanding s = 0 ↔
      _root_.RHTower.xi s = 0 := by
  constructor
  · intro hsquare
    have h11 := congrFun (congrFun hsquare (1 : Fin 2)) (1 : Fin 2)
    have hv := congrArg (fun T : EulerWickCompletedFockSpace →L[ℂ]
        EulerWickCompletedFockSpace =>
          T (eulerWickPrimitiveCompletedInteractionFockVector s)) h11
    simp [eulerWickCompletedFockOperatorLanding, Matrix.mul_apply,
      Fin.sum_univ_two] at hv
    have hvne := eulerWickPrimitiveCompletedInteractionFockVector_ne_zero s
    exact hv.resolve_right hvne
  · intro hxi
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eulerWickCompletedFockOperatorLanding, Matrix.mul_apply,
        Fin.sum_univ_two, hxi]

/-- The finite block matrix realized as one bounded operator on two Fock copies. -/
def eulerWickCompletedFockBlockOperator (s : ℂ) :
    (EulerWickCompletedFockSpace × EulerWickCompletedFockSpace) →L[ℂ]
      (EulerWickCompletedFockSpace × EulerWickCompletedFockSpace) :=
  (((_root_.RHTower.xi s) •
      ContinuousLinearMap.fst ℂ EulerWickCompletedFockSpace EulerWickCompletedFockSpace) +
    (eulerWickCompletedFockColorProjector s).comp
      (ContinuousLinearMap.snd ℂ EulerWickCompletedFockSpace EulerWickCompletedFockSpace)).prod
    ((_root_.RHTower.xi s) •
      ContinuousLinearMap.snd ℂ EulerWickCompletedFockSpace EulerWickCompletedFockSpace)

@[simp] theorem eulerWickCompletedFockBlockOperator_apply
    (s : ℂ) (x : EulerWickCompletedFockSpace × EulerWickCompletedFockSpace) :
    eulerWickCompletedFockBlockOperator s x =
      (_root_.RHTower.xi s • x.1 + eulerWickCompletedFockColorProjector s x.2,
        _root_.RHTower.xi s • x.2) := rfl

theorem eulerWickCompletedFockBlockOperator_ne_zero (s : ℂ) :
    eulerWickCompletedFockBlockOperator s ≠ 0 := by
  intro hzero
  apply eulerWickCompletedFockColorProjector_ne_zero s
  apply ContinuousLinearMap.ext
  intro y
  have hy := congrArg
    (fun T : (EulerWickCompletedFockSpace × EulerWickCompletedFockSpace) →L[ℂ]
      (EulerWickCompletedFockSpace × EulerWickCompletedFockSpace) => (T (0, y)).1) hzero
  simpa using hy

theorem eulerWickCompletedFockBlockOperator_squareZero_iff (s : ℂ) :
    eulerWickCompletedFockBlockOperator s *
        eulerWickCompletedFockBlockOperator s = 0 ↔
      _root_.RHTower.xi s = 0 := by
  constructor
  · intro hsquare
    let v := eulerWickPrimitiveCompletedInteractionFockVector s
    have hv := congrArg
      (fun T : (EulerWickCompletedFockSpace × EulerWickCompletedFockSpace) →L[ℂ]
        (EulerWickCompletedFockSpace × EulerWickCompletedFockSpace) => (T (0, v)).2) hsquare
    simp [eulerWickCompletedFockBlockOperator_apply] at hv
    exact hv.resolve_right (eulerWickPrimitiveCompletedInteractionFockVector_ne_zero s)
  · intro hxi
    apply ContinuousLinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext
    · simp [eulerWickCompletedFockBlockOperator_apply, hxi]
    · simp [eulerWickCompletedFockBlockOperator_apply, hxi]

theorem eulerWickCompletedFockColorProjector_reflection_intertwining
    (s : ℂ) (x : EulerWickCompletedFockSpace) :
    eulerWickCompletedFockColorProjector (1 - s)
        (eulerWickPrimitiveCompletedInteractionFockReflectionUnitary x) =
      eulerWickPrimitiveCompletedInteractionFockReflectionUnitary
        (eulerWickCompletedFockColorProjector s x) := by
  simp only [eulerWickCompletedFockColorProjector_apply]
  rw [eulerWickPrimitiveCompletedInteractionFockVector_one_sub]
  rw [LinearIsometryEquiv.inner_map_map]
  exact (eulerWickPrimitiveCompletedInteractionFockReflectionUnitary.map_smul
    (inner ℂ (eulerWickPrimitiveCompletedInteractionFockVector s) x)
    (eulerWickPrimitiveCompletedInteractionFockVector s)).symm

theorem eulerWickCompletedFockBlockOperator_reflection_intertwining
    (s : ℂ) (x y : EulerWickCompletedFockSpace) :
    eulerWickCompletedFockBlockOperator (1 - s)
        (eulerWickPrimitiveCompletedInteractionFockReflectionUnitary x,
          eulerWickPrimitiveCompletedInteractionFockReflectionUnitary y) =
      (eulerWickPrimitiveCompletedInteractionFockReflectionUnitary
          (eulerWickCompletedFockBlockOperator s (x, y)).1,
        eulerWickPrimitiveCompletedInteractionFockReflectionUnitary
          (eulerWickCompletedFockBlockOperator s (x, y)).2) := by
  ext <;>
    simp only [eulerWickCompletedFockBlockOperator_apply, _root_.RHTower.xi_one_sub,
      eulerWickCompletedFockColorProjector_reflection_intertwining, map_add, map_smul]

/-- Schatten-one EWQ color on the original Xi divisor. -/
def eulerWickXiDivisorCompletedFockColor
    (rho : _root_.RHTower.XiDivisorSupport) :
    _root_.RHTower.SchattenOneOperator EulerWickCompletedFockSpace :=
  eulerWickCompletedFockColorTraceClass (rho : ℂ)

theorem eulerWickXiDivisorCompletedFockColor_ne_zero
    (rho : _root_.RHTower.XiDivisorSupport) :
    eulerWickXiDivisorCompletedFockColor rho ≠ 0 := by
  intro hzero
  have hcoe := congrArg
    (fun A : _root_.RHTower.SchattenOneOperator EulerWickCompletedFockSpace =>
      (A : EulerWickCompletedFockSpace →L[ℂ] EulerWickCompletedFockSpace)) hzero
  simp only [eulerWickXiDivisorCompletedFockColor,
    eulerWickCompletedFockColorTraceClass_coe] at hcoe
  exact eulerWickCompletedFockColorProjector_ne_zero (rho : ℂ) hcoe

/-- Positive trace-class color loses only a scalar phase, still enough to separate every free
critical-line reflection orbit. -/
theorem eulerWickXiDivisorCompletedFockColor_lineConj_eq_iff
    (rho : _root_.RHTower.XiDivisorSupport) :
    eulerWickXiDivisorCompletedFockColor
        (_root_.RHTower.xiZeroLineConjEquiv rho) =
      eulerWickXiDivisorCompletedFockColor rho ↔
        ((rho : ℂ).re = 1 / 2) := by
  constructor
  · intro hcolor
    have hcoe := congrArg
      (fun A : _root_.RHTower.SchattenOneOperator EulerWickCompletedFockSpace =>
        (A : EulerWickCompletedFockSpace →L[ℂ] EulerWickCompletedFockSpace)) hcolor
    simp only [eulerWickXiDivisorCompletedFockColor,
      eulerWickCompletedFockColorTraceClass_coe] at hcoe
    have hphase := (GaloisForLFunctions.HTGeometry.positiveRankOne_eq_iff_phase
      (eulerWickPrimitiveCompletedInteractionFockVector_ne_zero
        (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ))
      (eulerWickPrimitiveCompletedInteractionFockVector_ne_zero (rho : ℂ))).1 (by
        simpa [GaloisForLFunctions.HTGeometry.positiveRankOne,
          eulerWickCompletedFockColorProjector] using hcoe)
    obtain ⟨theta, hvector⟩ := hphase
    have hprojective : EulerWickPrimitiveCompletedJetsProjectivelyAgree
        (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ) (rho : ℂ) := by
      refine ⟨Complex.exp ((theta : ℂ) * Complex.I), Complex.exp_ne_zero _, ?_⟩
      intro n
      have hn := congrArg (fun v : EulerWickCompletedFockSpace => v n) hvector
      change iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction
          (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ) /
            (Real.sqrt (n.factorial : ℝ) : ℂ) =
        Complex.exp ((theta : ℂ) * Complex.I) *
          (iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction (rho : ℂ) /
            (Real.sqrt (n.factorial : ℝ) : ℂ)) at hn
      have hfac : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
      field_simp at hn
      exact hn
    have hre := re_eq_of_eulerWickPrimitiveCompletedJetsProjectivelyAgree hprojective
    rw [_root_.RHTower.xiZeroLineConjEquiv_apply] at hre
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro hre
    have hpoint : _root_.RHTower.xiZeroLineConjEquiv rho = rho := by
      apply Subtype.ext
      apply Complex.ext
      · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
        simp
    rw [hpoint]

theorem norm_eulerWickXiDivisorCompletedFockColor_lineConj
    (rho : _root_.RHTower.XiDivisorSupport) :
    ‖eulerWickXiDivisorCompletedFockColor
        (_root_.RHTower.xiZeroLineConjEquiv rho)‖ =
      ‖eulerWickXiDivisorCompletedFockColor rho‖ := by
  simp only [eulerWickXiDivisorCompletedFockColor,
    norm_eulerWickCompletedFockColorTraceClass]
  rw [_root_.RHTower.xiZeroLineConjEquiv_apply,
    norm_eulerWickPrimitiveCompletedInteractionFockVector_one_sub,
    norm_eulerWickPrimitiveCompletedInteractionFockVector_conj]

/-- Operational trace-class distance between the two line-conjugate divisor colors. -/
def eulerWickXiDivisorCompletedFockTraceDefect
    (rho : _root_.RHTower.XiDivisorSupport) : ℝ :=
  ‖eulerWickXiDivisorCompletedFockColor
      (_root_.RHTower.xiZeroLineConjEquiv rho) -
    eulerWickXiDivisorCompletedFockColor rho‖

theorem eulerWickXiDivisorCompletedFockTraceDefect_eq_zero_iff
    (rho : _root_.RHTower.XiDivisorSupport) :
    eulerWickXiDivisorCompletedFockTraceDefect rho = 0 ↔
      ((rho : ℂ).re = 1 / 2) := by
  rw [eulerWickXiDivisorCompletedFockTraceDefect, norm_eq_zero, sub_eq_zero]
  exact eulerWickXiDivisorCompletedFockColor_lineConj_eq_iff rho

theorem eulerWickXiDivisorCompletedFockTraceDefect_pos_iff
    (rho : _root_.RHTower.XiDivisorSupport) :
    0 < eulerWickXiDivisorCompletedFockTraceDefect rho ↔
      ((rho : ℂ).re ≠ 1 / 2) := by
  rw [eulerWickXiDivisorCompletedFockTraceDefect, norm_pos_iff, sub_ne_zero]
  exact not_congr (eulerWickXiDivisorCompletedFockColor_lineConj_eq_iff rho)


end

end GaloisForLFunctions.RHTower
