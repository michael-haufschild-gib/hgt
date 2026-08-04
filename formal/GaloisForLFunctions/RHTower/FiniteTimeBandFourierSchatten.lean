/-
Classical Schatten-1 upgrade for finite time-band Fourier operators.

`FiniteTimeBandFourierCompact` constructs these operators and proves compactness.  Here the
Fourier exponential is expanded into its factorially decaying separable Taylor series.  Each
term has rank at most one, and the weighted operator-norm tails are summable; the project's
approximation-number definition therefore places the exact operator in Schatten class one.

This is analytic infrastructure, not a novelty claim.
-/
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.RHTower.SoninL2Model
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Currying continuous maps on compact spaces is a contraction. -/
def continuousMapCurryCLM (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] :
    C(X × Y, ℂ) →L[ℂ] C(X, C(Y, ℂ)) :=
  LinearMap.mkContinuous
    { toFun := ContinuousMap.curry
      map_add' := by intro f g; ext x y; rfl
      map_smul' := by intro c f; ext x y; rfl }
    1 (fun f => by
      change ‖f.curry‖ ≤ 1 * ‖f‖
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro x
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro y
      exact f.norm_coe_le_norm (x, y))

/-- Extend a continuous interval function constantly along nearest-point projection. -/
def projectClosedIntervalBCFCLM (a b : ℝ) (hab : a ≤ b)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    C(ClosedInterval a b, E) →L[ℂ] (ℝ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.ofNormedAddCommGroup
        (fun x => f (Set.projIcc a b hab x))
        (f.continuous.comp continuous_projIcc) ‖f‖
        (fun x => f.norm_coe_le_norm _)
      map_add' := by intro f g; ext x; rfl
      map_smul' := by intro c f; ext x; rfl }
    1 (fun f => by
      rw [one_mul]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
      intro x
      exact f.norm_coe_le_norm _)

/-- Continuous rectangle kernels mapped to full `L²(ℝ)` integral operators, with input and
output restricted to the source and target intervals. -/
def fullRectangleKernelOperatorMap (a b c d : ℝ) (hab : a ≤ b) :
    C(ClosedInterval a b × ClosedInterval c d, ℂ) →L[ℂ]
      (RealL2 →L[ℂ] RealL2) := by
  let toLpY : C(ClosedInterval c d, ℂ) →L[ℂ] IntervalL2 c d :=
    ContinuousMap.toLp (α := ClosedInterval c d) (E := ℂ) 2
      (volume : Measure (ClosedInterval c d)) ℂ
  let pairing : IntervalL2 c d →L[ℂ] (IntervalL2 c d →L[ℂ] ℂ) :=
    complexMulBilinear.lpPairing (volume : Measure (ClosedInterval c d)) 2 2
  let precompRestrict : (IntervalL2 c d →L[ℂ] ℂ) →L[ℂ] (RealL2 →L[ℂ] ℂ) :=
    ContinuousLinearMap.flip
      (ContinuousLinearMap.compL ℂ RealL2 (IntervalL2 c d) ℂ)
      (restrictToClosedInterval c d)
  let bcfToLp : (ℝ →ᵇ (RealL2 →L[ℂ] ℂ)) →L[ℂ]
      Lp (RealL2 →L[ℂ] ℂ) 2
        ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
    BoundedContinuousFunction.toLp 2
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ℂ
  let extendOut : Lp ℂ 2 ((volume : Measure ℝ).restrict (Set.Icc a b)) →L[ℂ]
      RealL2 :=
    lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
      (Set.Icc a b) measurableSet_Icc
  let postExtend : (RealL2 →L[ℂ]
      Lp ℂ 2 ((volume : Measure ℝ).restrict (Set.Icc a b))) →L[ℂ]
      (RealL2 →L[ℂ] RealL2) :=
    ContinuousLinearMap.compL ℂ RealL2
      (Lp ℂ 2 ((volume : Measure ℝ).restrict (Set.Icc a b))) RealL2 extendOut
  exact
    postExtend ∘L
    kernelOperatorMap (E := RealL2)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ∘L
    bcfToLp ∘L
    projectClosedIntervalBCFCLM a b hab (RealL2 →L[ℂ] ℂ) ∘L
    precompRestrict.compLeftContinuous ℂ (ClosedInterval a b) ∘L
    pairing.compLeftContinuous ℂ (ClosedInterval a b) ∘L
    toLpY.compLeftContinuous ℂ (ClosedInterval a b) ∘L
    continuousMapCurryCLM (ClosedInterval a b) (ClosedInterval c d)

theorem fullRectangleKernelOperatorMap_phase
    (a b c d : ℝ) (hab : a ≤ b) :
    fullRectangleKernelOperatorMap a b c d hab
      (fourierPhaseContinuous a b c d) =
      fullTimeBandFourier a b c d hab := by
  unfold fullRectangleKernelOperatorMap fullTimeBandFourier
    fullToRestrictedTimeBandFourier fullFourierFunctionalField
    fullFourierFunctionalBCF fullFourierFunctionalContinuous
    fourierFunctionalContinuous fourierSectionContinuous fourierPhaseCurried
  rfl

def continuousRectangleTensor (a b c d : ℝ)
    (u : C(ClosedInterval a b, ℂ)) (v : C(ClosedInterval c d, ℂ)) :
    C(ClosedInterval a b × ClosedInterval c d, ℂ) where
  toFun z := u z.1 * v z.2
  continuous_toFun := u.continuous.comp continuous_fst |>.mul
    (v.continuous.comp continuous_snd)

theorem fullRectangleKernelOperatorMap_tensor_apply
    (a b c d : ℝ) (hab : a ≤ b)
    (u : C(ClosedInterval a b, ℂ)) (v : C(ClosedInterval c d, ℂ))
    (f : RealL2) :
    let vLp : IntervalL2 c d :=
      ContinuousMap.toLp 2 (volume : Measure (ClosedInterval c d)) ℂ v
    let ell : RealL2 →L[ℂ] ℂ :=
      (complexMulBilinear.lpPairing
        (volume : Measure (ClosedInterval c d)) 2 2 vLp) ∘L
          restrictToClosedInterval c d
    let uBCF : ℝ →ᵇ ℂ := projectClosedIntervalBCFCLM a b hab ℂ u
    let uOut : Lp ℂ 2 ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
      BoundedContinuousFunction.toLp 2
        ((volume : Measure ℝ).restrict (Set.Icc a b)) ℂ uBCF
    let uFull : RealL2 :=
      lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
        (Set.Icc a b) measurableSet_Icc uOut
    fullRectangleKernelOperatorMap a b c d hab
        (continuousRectangleTensor a b c d u v) f = ell f • uFull := by
  dsimp only
  let toLpY : C(ClosedInterval c d, ℂ) →L[ℂ] IntervalL2 c d :=
    ContinuousMap.toLp (α := ClosedInterval c d) (E := ℂ) 2
      (volume : Measure (ClosedInterval c d)) ℂ
  let pairing : IntervalL2 c d →L[ℂ] (IntervalL2 c d →L[ℂ] ℂ) :=
    complexMulBilinear.lpPairing (volume : Measure (ClosedInterval c d)) 2 2
  let precompRestrict : (IntervalL2 c d →L[ℂ] ℂ) →L[ℂ] (RealL2 →L[ℂ] ℂ) :=
    ContinuousLinearMap.flip
      (ContinuousLinearMap.compL ℂ RealL2 (IntervalL2 c d) ℂ)
      (restrictToClosedInterval c d)
  let vLp : IntervalL2 c d := toLpY v
  let ell : RealL2 →L[ℂ] ℂ := precompRestrict (pairing vLp)
  let uBCF : ℝ →ᵇ ℂ := projectClosedIntervalBCFCLM a b hab ℂ u
  let ellBCF : ℝ →ᵇ (RealL2 →L[ℂ] ℂ) :=
    uBCF • BoundedContinuousFunction.const ℝ ell
  let field : Lp (RealL2 →L[ℂ] ℂ) 2
      ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
    BoundedContinuousFunction.toLp 2
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ℂ ellBCF
  let uOut : Lp ℂ 2 ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
    BoundedContinuousFunction.toLp 2
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ℂ uBCF
  let extendOut : Lp ℂ 2 ((volume : Measure ℝ).restrict (Set.Icc a b)) →L[ℂ]
      RealL2 := lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
        (Set.Icc a b) measurableSet_Icc
  have hBCF :
      projectClosedIntervalBCFCLM a b hab (RealL2 →L[ℂ] ℂ)
        (precompRestrict.compLeftContinuous ℂ (ClosedInterval a b)
          (pairing.compLeftContinuous ℂ (ClosedInterval a b)
            (toLpY.compLeftContinuous ℂ (ClosedInterval a b)
              (continuousRectangleTensor a b c d u v).curry))) = ellBCF := by
    ext x f
    change precompRestrict
      (pairing (toLpY ((continuousRectangleTensor a b c d u v).curry
        (Set.projIcc a b hab x)))) f = (uBCF x • ell) f
    have hsection : (continuousRectangleTensor a b c d u v).curry
        (Set.projIcc a b hab x) = uBCF x • v := by
      ext y
      rfl
    rw [hsection, map_smul, map_smul, map_smul]
  have hkernel : kernelOperator
        ((volume : Measure ℝ).restrict (Set.Icc a b)) field f = ell f • uOut := by
    apply Lp.ext
    filter_upwards [
      (evalBilinear (𝕜 := ℂ) (E := RealL2)).coeFn_holder (r := (2 : ENNReal))
        field (Lp.const ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)) f),
      BoundedContinuousFunction.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
        (μ := ((volume : Measure ℝ).restrict (Set.Icc a b))) ellBCF,
      Lp.coeFn_const (p := ∞) ((volume : Measure ℝ).restrict (Set.Icc a b)) f,
      BoundedContinuousFunction.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
        (μ := ((volume : Measure ℝ).restrict (Set.Icc a b))) uBCF,
      Lp.coeFn_smul (ell f) uOut
    ] with x hholder hfield hconst hu hout
    rw [kernelOperator, kernelOperatorMap_apply, hholder, hfield, hconst, hout]
    change (uBCF x • ell) f = ell f * uOut x
    rw [show uOut x = uBCF x from hu]
    simp [mul_comm]
  unfold fullRectangleKernelOperatorMap
  change extendOut (kernelOperator
    ((volume : Measure ℝ).restrict (Set.Icc a b))
      (BoundedContinuousFunction.toLp 2
        ((volume : Measure ℝ).restrict (Set.Icc a b)) ℂ
          (projectClosedIntervalBCFCLM a b hab (RealL2 →L[ℂ] ℂ)
            (precompRestrict.compLeftContinuous ℂ (ClosedInterval a b)
              (pairing.compLeftContinuous ℂ (ClosedInterval a b)
                (toLpY.compLeftContinuous ℂ (ClosedInterval a b)
                  (continuousRectangleTensor a b c d u v).curry))))) f) =
      ell f • extendOut uOut
  rw [hBCF]
  change extendOut (kernelOperator
    ((volume : Measure ℝ).restrict (Set.Icc a b)) field f) = _
  rw [hkernel, map_smul]

def fourierPhaseExponentContinuous (a b c d : ℝ) :
    C(ClosedInterval a b × ClosedInterval c d, ℂ) where
  toFun z := ((-(2 * Real.pi * (z.1 : ℝ) * (z.2 : ℝ)) : ℝ) * Complex.I)
  continuous_toFun := by fun_prop

theorem exp_fourierPhaseExponentContinuous (a b c d : ℝ) :
    NormedSpace.exp (fourierPhaseExponentContinuous a b c d) =
      fourierPhaseContinuous a b c d := by
  rw [NormedSpace.exp_continuousMap_eq]
  ext z
  change NormedSpace.exp
    (((-(2 * Real.pi * (z.1 : ℝ) * (z.2 : ℝ)) : ℝ) * Complex.I)) =
      Complex.exp (((-(2 * Real.pi * (z.1 : ℝ) * (z.2 : ℝ)) : ℝ) * Complex.I))
  rw [← Complex.exp_eq_exp_ℂ]

def fourierTaylorOutputContinuous (a b : ℝ) (n : ℕ) :
    C(ClosedInterval a b, ℂ) where
  toFun x := ((n.factorial : ℂ)⁻¹ *
      (((-(2 * Real.pi) : ℝ) : ℂ) * Complex.I) ^ n) * ((x : ℝ) : ℂ) ^ n
  continuous_toFun := by fun_prop

def intervalMonomialContinuous (c d : ℝ) (n : ℕ) :
    C(ClosedInterval c d, ℂ) where
  toFun y := ((y : ℝ) : ℂ) ^ n
  continuous_toFun := by fun_prop

theorem fourierPhaseTaylorTerm_eq_tensor
    (a b c d : ℝ) (n : ℕ) :
    (NormedSpace.expSeries ℂ
      C(ClosedInterval a b × ClosedInterval c d, ℂ) n
        (fun _ => fourierPhaseExponentContinuous a b c d)) =
      continuousRectangleTensor a b c d
        (fourierTaylorOutputContinuous a b n)
        (intervalMonomialContinuous c d n) := by
  rw [NormedSpace.expSeries_apply_eq]
  ext z
  change (n.factorial : ℂ)⁻¹ *
      ((((-(2 * Real.pi * (z.1 : ℝ) * (z.2 : ℝ)) : ℝ) : ℂ) * Complex.I) ^ n) =
    (((n.factorial : ℂ)⁻¹ *
      (((-(2 * Real.pi) : ℝ) : ℂ) * Complex.I) ^ n) *
        (((z.1 : ℝ) : ℂ) ^ n)) * (((z.2 : ℝ) : ℂ) ^ n)
  push_cast
  ring

def fullTimeBandFourierTaylorTerm
    (a b c d : ℝ) (hab : a ≤ b) (n : ℕ) : RealL2 →L[ℂ] RealL2 :=
  fullRectangleKernelOperatorMap a b c d hab
    (NormedSpace.expSeries ℂ
      C(ClosedInterval a b × ClosedInterval c d, ℂ) n
        (fun _ => fourierPhaseExponentContinuous a b c d))

theorem hasSum_fullTimeBandFourierTaylorTerm
    (a b c d : ℝ) (hab : a ≤ b) :
    HasSum (fullTimeBandFourierTaylorTerm a b c d hab)
      (fullTimeBandFourier a b c d hab) := by
  have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ)
    (fourierPhaseExponentContinuous a b c d)
  have hm := (fullRectangleKernelOperatorMap a b c d hab).hasSum h
  rw [exp_fourierPhaseExponentContinuous,
    fullRectangleKernelOperatorMap_phase] at hm
  exact hm

theorem hasRankLE_fullTimeBandFourierTaylorTerm
    (a b c d : ℝ) (hab : a ≤ b) (n : ℕ) :
    HasRankLE (fullTimeBandFourierTaylorTerm a b c d hab n) 1 := by
  let u := fourierTaylorOutputContinuous a b n
  let v := intervalMonomialContinuous c d n
  let uBCF : ℝ →ᵇ ℂ := projectClosedIntervalBCFCLM a b hab ℂ u
  let uOut : Lp ℂ 2 ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
    BoundedContinuousFunction.toLp 2
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ℂ uBCF
  let uFull : RealL2 :=
    lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
      (Set.Icc a b) measurableSet_Icc uOut
  refine ⟨Submodule.span ℂ ({uFull} : Set RealL2),
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton uFull),
    (finrank_span_le_card ({uFull} : Set RealL2)).trans (by simp), ?_⟩
  intro f
  have happ := fullRectangleKernelOperatorMap_tensor_apply
    a b c d hab u v f
  rw [fullTimeBandFourierTaylorTerm, fourierPhaseTaylorTerm_eq_tensor]
  rw [happ]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_singleton uFull))

theorem nat_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by ring

theorem summable_succ_mul_norm_expSeries_continuousMap
    (a b c d : ℝ) :
    Summable (fun n => ((n + 1 : ℕ) : ℝ) *
      ‖NormedSpace.expSeries ℂ
        C(ClosedInterval a b × ClosedInterval c d, ℂ) n
          (fun _ => fourierPhaseExponentContinuous a b c d)‖) := by
  let X := fourierPhaseExponentContinuous a b c d
  let E := C(ClosedInterval a b × ClosedInterval c d, ℂ)
  have hbase := NormedSpace.norm_expSeries_summable (𝕂 := ℂ)
    (show E from (2 : ℂ) • X)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (fun n => ?_) hbase
  have hterm : NormedSpace.expSeries ℂ E n (fun _ => (2 : ℂ) • X) =
      (2 : ℂ) ^ n • NormedSpace.expSeries ℂ E n (fun _ => X) := by
    simp only [NormedSpace.expSeries_apply_eq, smul_pow, smul_smul]
    rw [mul_comm ((n.factorial : ℂ)⁻¹) ((2 : ℂ) ^ n)]
  have hnorm := congrArg norm hterm
  simp only [norm_smul, norm_pow, Complex.norm_ofNat] at hnorm
  change ((n + 1 : ℕ) : ℝ) *
      ‖NormedSpace.expSeries ℂ E n (fun _ => X)‖ ≤
    ‖NormedSpace.expSeries ℂ E n (fun _ => (2 : ℂ) • X)‖
  calc
    ((n + 1 : ℕ) : ℝ) * ‖NormedSpace.expSeries ℂ E n (fun _ => X)‖ ≤
        2 ^ n * ‖NormedSpace.expSeries ℂ E n (fun _ => X)‖ :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast nat_succ_le_two_pow n) (norm_nonneg _)
    _ = ‖NormedSpace.expSeries ℂ E n (fun _ => (2 : ℂ) • X)‖ := hnorm.symm

theorem summable_succ_mul_norm_fullTimeBandFourierTaylorTerm
    (a b c d : ℝ) (hab : a ≤ b) :
    Summable (fun n => ((n + 1 : ℕ) : ℝ) *
      ‖fullTimeBandFourierTaylorTerm a b c d hab n‖) := by
  let L := fullRectangleKernelOperatorMap a b c d hab
  let A : ℕ → C(ClosedInterval a b × ClosedInterval c d, ℂ) := fun n =>
    NormedSpace.expSeries ℂ
      C(ClosedInterval a b × ClosedInterval c d, ℂ) n
        (fun _ => fourierPhaseExponentContinuous a b c d)
  have hw : Summable (fun n => ((n + 1 : ℕ) : ℝ) * ‖A n‖) := by
    simpa [A] using summable_succ_mul_norm_expSeries_continuousMap a b c d
  have hmajor : Summable (fun n => ‖L‖ *
      (((n + 1 : ℕ) : ℝ) * ‖A n‖)) := hw.mul_left ‖L‖
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (fun n => ?_) hmajor
  change ((n + 1 : ℕ) : ℝ) * ‖L (A n)‖ ≤
    ‖L‖ * (((n + 1 : ℕ) : ℝ) * ‖A n‖)
  calc
    ((n + 1 : ℕ) : ℝ) * ‖L (A n)‖ ≤
        ((n + 1 : ℕ) : ℝ) * (‖L‖ * ‖A n‖) :=
      mul_le_mul_of_nonneg_left (L.le_opNorm (A n)) (Nat.cast_nonneg _)
    _ = ‖L‖ * (((n + 1 : ℕ) : ℝ) * ‖A n‖) := by ring

theorem summable_norm_fullTimeBandFourierTaylorTerm
    (a b c d : ℝ) (hab : a ≤ b) :
    Summable (fun n => ‖fullTimeBandFourierTaylorTerm a b c d hab n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) (summable_succ_mul_norm_fullTimeBandFourierTaylorTerm a b c d hab)
  calc
    ‖fullTimeBandFourierTaylorTerm a b c d hab n‖ =
        1 * ‖fullTimeBandFourierTaylorTerm a b c d hab n‖ := by rw [one_mul]
    _ ≤ ((n + 1 : ℕ) : ℝ) * ‖fullTimeBandFourierTaylorTerm a b c d hab n‖ :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (norm_nonneg _)

/-- Every finite time-band Fourier operator on `L²(ℝ)` is Schatten-1. -/
theorem memSchattenClass_one_fullTimeBandFourier
    (a b c d : ℝ) (hab : a ≤ b) :
    MemSchattenClass 1 (fullTimeBandFourier a b c d hab) := by
  let A := fullTimeBandFourierTaylorTerm a b c d hab
  have hw : Summable (fun n => ((n + 1 : ℕ) : ℝ) * ‖A n‖) := by
    simpa [A] using
      summable_succ_mul_norm_fullTimeBandFourierTaylorTerm a b c d hab
  have hn : Summable (fun n => ‖A n‖) := by
    simpa [A] using summable_norm_fullTimeBandFourierTaylorTerm a b c d hab
  have ht : Summable (fun n => ∑' k, ‖A (k + n)‖) :=
    summable_tsum_nat_add_of_summable_succ_mul
      (fun n => ‖A n‖) (fun n => norm_nonneg _) hw
  have hS : MemSchattenClass 1 (∑' n, A n) :=
    memSchattenClass_one_tsum_rankOneTerms A
      (hasRankLE_fullTimeBandFourierTaylorTerm a b c d hab) hn ht
  rw [(hasSum_fullTimeBandFourierTaylorTerm a b c d hab).tsum_eq] at hS
  exact hS

/-- Concrete physical--Fourier interval block is Schatten-1. -/
theorem memSchattenClass_one_cutoffFourierCutoff
    (a b c d : ℝ) (hab : a ≤ b) :
    MemSchattenClass 1 (cutoffFourierCutoff a b c d) := by
  rw [← fullTimeBandFourier_eq_cutoffFourierCutoff a b c d hab]
  exact memSchattenClass_one_fullTimeBandFourier a b c d hab

end RHTower
