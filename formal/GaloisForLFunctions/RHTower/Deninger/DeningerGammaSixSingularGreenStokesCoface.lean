import GaloisForLFunctions.HTGeometry.LpInjectionCompression
import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixFullSourcePrincipalClass

namespace RHTower

noncomputable section

theorem deningerGammaSixWoldCoordinate_injective :
    Function.Injective deningerGammaSixWoldCoordinate := by
  intro i j hij
  unfold deningerGammaSixWoldCoordinate at hij
  omega

/-- Literal unilateral Wold isometry on the sorted ordinary-integer shell
coordinates.  It sends coordinate `n` to `6*n+1080`. -/
def deningerGammaSixWoldShift : EllTwo →ₗᵢ[ℂ] EllTwo :=
  lpScalarInjection deningerGammaSixWoldCoordinate
    deningerGammaSixWoldCoordinate_injective

@[simp] theorem deningerGammaSixWoldShift_single (n : ℕ) (c : ℂ) :
    deningerGammaSixWoldShift (lp.single 2 n c) =
      lp.single 2 (deningerGammaSixWoldCoordinate n) c :=
  lpScalarInjection_single deningerGammaSixWoldCoordinate
    deningerGammaSixWoldCoordinate_injective n c

@[simp] theorem deningerGammaSixWoldShift_coordinate
    (x : EllTwo) (n : ℕ) :
    deningerGammaSixWoldShift x (deningerGammaSixWoldCoordinate n) = x n :=
  lpScalarInjection_coordinate deningerGammaSixWoldCoordinate
    deningerGammaSixWoldCoordinate_injective x n

/-- Vector-valued adjoint Wold pullback.  This is the `1 tensor S₆*` leg of
rectangular shell compression. -/
def deningerGammaSixTensorWoldPullback :
    lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 →L[ℂ]
      lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  lpCoordinatePullback deningerGammaSixWoldCoordinate
    deningerGammaSixWoldCoordinate_injective

@[simp] theorem deningerGammaSixTensorWoldPullback_apply
    (y : lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2) (n : ℕ) :
    deningerGammaSixTensorWoldPullback y n =
      y (deningerGammaSixWoldCoordinate n) := rfl

/-- Actual Wold compression `(1 tensor S₆*) T S₆` on rectangular source
operators. -/
def deningerGammaSixWoldCompression
    (T : EllTwo →L[ℂ]
      lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2) :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  deningerGammaSixTensorWoldPullback ∘L
    T ∘L deningerGammaSixWoldShift.toContinuousLinearMap

@[simp] theorem deningerGammaSixWoldCompression_apply
    (T : EllTwo →L[ℂ]
      lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2)
    (x : EllTwo) (n : ℕ) :
    deningerGammaSixWoldCompression T x n =
      T (deningerGammaSixWoldShift x)
        (deningerGammaSixWoldCoordinate n) := rfl

theorem deningerGammaSixShellHonestDepth_wold (n : ℕ) :
    deningerGammaSixShellHonestDepth (deningerGammaSixWoldCoordinate n) =
      ⟨deningerGammaSixShellDepth n + 1,
        (three_le_deningerGammaSixShellDepth n).trans (Nat.le_succ _)⟩ := by
  unfold deningerGammaSixShellHonestDepth
  rw [Subtype.mk.injEq]
  exact deningerGammaSixShellDepth_wold n

/-- Exact compression of the complete source operator advances its literal
countertransported tensor source by one shell depth. -/
theorem deningerGammaSixWoldCompression_full_apply
    (x : EllTwo) (n : ℕ) :
    deningerGammaSixWoldCompression
        deningerGammaSixFullSourceTensorOperator x n =
      x n • deningerGammaSixSourceTensorSquare
        ⟨deningerGammaSixShellDepth n + 1,
          (three_le_deningerGammaSixShellDepth n).trans (Nat.le_succ _)⟩ := by
  rw [deningerGammaSixWoldCompression_apply,
    deningerGammaSixFullSourceTensorOperator_apply,
    deningerGammaSixWoldShift_coordinate,
    deningerGammaSixShellHonestDepth_wold]

/-- Principal source symbol has exact Wold eigenvalue `1/6`, before taking
any weak-trace quotient. -/
theorem deningerGammaSixWoldCompression_principal :
    deningerGammaSixWoldCompression
        deningerGammaSixSourceTensorPrincipalOperator =
      ((1 / 6 : ℂ) • deningerGammaSixSourceTensorPrincipalOperator) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  rw [deningerGammaSixWoldCompression_apply,
    deningerGammaSixSourceTensorPrincipalOperator_apply,
    deningerGammaSixWoldShift_coordinate,
    deningerGammaSixShellHonestDepth_wold]
  change _ = (1 / 6 : ℂ) •
    (deningerGammaSixSourceTensorPrincipalOperator x n)
  rw [
    deningerGammaSixSourceTensorPrincipalOperator_apply,
    deningerGammaSixSourceTensorPrincipal_eq,
    deningerGammaSixSourceTensorPrincipal_eq, pow_succ]
  change x n • (((1 / 6 : ℝ) ^ deningerGammaSixShellDepth n * (1 / 6 : ℝ) : ℝ) : ℂ) •
      deningerGammaSixLeadingTensorVector =
    (1 / 6 : ℂ) •
      (x n • (((1 / 6 : ℝ) ^ deningerGammaSixShellDepth n : ℝ) : ℂ) •
        deningerGammaSixLeadingTensorVector)
  module

theorem deningerGammaSixWoldCompression_remainder_traceClass :
    MemRectSchattenClass 1
      (deningerGammaSixWoldCompression
        deningerGammaSixSourceTensorRemainderOperator) := by
  exact (deningerGammaSixSourceTensorRemainderOperator_traceClass.one_comp_right
      deningerGammaSixWoldShift.toContinuousLinearMap).one_comp_left
    deningerGammaSixTensorWoldPullback

theorem deningerGammaSixWoldCompression_add
    (S T : EllTwo →L[ℂ]
      lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2) :
    deningerGammaSixWoldCompression (S + T) =
      deningerGammaSixWoldCompression S +
        deningerGammaSixWoldCompression T := by
  unfold deningerGammaSixWoldCompression
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

theorem deningerGammaSix_smul_remainder_traceClass :
    MemRectSchattenClass 1
      ((1 / 6 : ℂ) • deningerGammaSixSourceTensorRemainderOperator) := by
  let A : lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 →L[ℂ]
      lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
    (1 / 6 : ℂ) • ContinuousLinearMap.id ℂ _
  have hA := deningerGammaSixSourceTensorRemainderOperator_traceClass.one_comp_left A
  convert hA using 1
  apply ContinuousLinearMap.ext
  intro x
  simp [A]

theorem deningerGammaSixWoldCompression_full_coface_eq_remainder :
    deningerGammaSixWoldCompression
          deningerGammaSixFullSourceTensorOperator -
        (1 / 6 : ℂ) • deningerGammaSixFullSourceTensorOperator =
      deningerGammaSixWoldCompression
          deningerGammaSixSourceTensorRemainderOperator -
        (1 / 6 : ℂ) • deningerGammaSixSourceTensorRemainderOperator := by
  have hdecomp : deningerGammaSixFullSourceTensorOperator =
      deningerGammaSixSourceTensorPrincipalOperator +
        deningerGammaSixSourceTensorRemainderOperator := by
    rw [← deningerGammaSixFullSourceTensorOperator_sub_principal]
    module
  rw [hdecomp, deningerGammaSixWoldCompression_add,
    deningerGammaSixWoldCompression_principal, smul_add]
  module

/-- **Singular Gamma-six Green--Stokes coface.**  Literal Wold compression
of the complete corrected source has eigenvalue `1/6` modulo the ordinary
rectangular trace class. -/
theorem deningerGammaSixFullSource_singularGreenStokesCoface :
    MemRectSchattenClass 1
      (deningerGammaSixWoldCompression
          deningerGammaSixFullSourceTensorOperator -
        (1 / 6 : ℂ) • deningerGammaSixFullSourceTensorOperator) := by
  rw [deningerGammaSixWoldCompression_full_coface_eq_remainder]
  exact deningerGammaSixWoldCompression_remainder_traceClass.one_sub
    deningerGammaSix_smul_remainder_traceClass

end

end RHTower
