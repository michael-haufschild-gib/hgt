import GaloisForLFunctions.RHTower.FiniteTimeBandFourierCompact
import GaloisForLFunctions.RHTower.BandTransformSymmetric

/-!
# The band operator on real interval `L²`

The prolate (Slepian) band operator is the integral operator with the smoothed sinc kernel on
`[-1, 1]`.  This module realises it as a *bounded operator on a real Hilbert space*, which is what
perturbation theory acts on, and proves the two structural facts that theory needs: the operator is
compact and it is symmetric.

Both come from a general statement proved here for an arbitrary continuous kernel on a closed
interval: the kernel row `y ↦ K (x, y)` is a continuous family of `L²` vectors, hence a continuous
family of continuous functionals, hence a square-integrable field of functionals, and the field form
of the Hilbert–Schmidt kernel theorem turns any such field into a compact operator.  Symmetry is
Fubini for the bounded kernel against two `L¹` functions.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Real `L²` of a closed interval, with its subtype Lebesgue measure. -/
abbrev RealIntervalL2 (a b : ℝ) := Lp ℝ 2 (volume : Measure (ClosedInterval a b))

variable {a b : ℝ}

/-- The kernel rows, as a continuous family of `L²` vectors. -/
def kernelSectionContinuous (K : C(ClosedInterval a b × ClosedInterval a b, ℝ)) :
    C(ClosedInterval a b, RealIntervalL2 a b) where
  toFun x := ContinuousMap.toLp 2 volume ℝ (K.curry x)
  continuous_toFun :=
    (ContinuousMap.toLp 2 volume ℝ).continuous.comp K.curry.continuous

/-- Multiplication of reals as a continuous bilinear map. -/
def realMulBilinear : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ

/-- The kernel rows, as a continuous family of continuous functionals on `L²`. -/
def kernelFunctionalContinuous (K : C(ClosedInterval a b × ClosedInterval a b, ℝ)) :
    C(ClosedInterval a b, RealIntervalL2 a b →L[ℝ] ℝ) where
  toFun x := (realMulBilinear.lpPairing volume 2 2) (kernelSectionContinuous K x)
  continuous_toFun :=
    (realMulBilinear.lpPairing volume 2 2).continuous.comp
      (kernelSectionContinuous K).continuous

/-- The square-integrable field of functionals of a continuous kernel. -/
def kernelFunctionalField (K : C(ClosedInterval a b × ClosedInterval a b, ℝ)) :
    Lp (RealIntervalL2 a b →L[ℝ] ℝ) 2 (volume : Measure (ClosedInterval a b)) :=
  ContinuousMap.toLp 2 volume ℝ (kernelFunctionalContinuous K)

/-- **The integral operator of a continuous kernel on a closed interval.** -/
def continuousKernelOperator (K : C(ClosedInterval a b × ClosedInterval a b, ℝ)) :
    RealIntervalL2 a b →L[ℝ] RealIntervalL2 a b :=
  kernelOperator (volume : Measure (ClosedInterval a b)) (kernelFunctionalField K)

/-- The operator's values are the kernel pairings against the rows. -/
theorem continuousKernelOperator_coeFn_pairing
    (K : C(ClosedInterval a b × ClosedInterval a b, ℝ)) (f : RealIntervalL2 a b) :
    (continuousKernelOperator K f : ClosedInterval a b → ℝ) =ᵐ[volume]
      fun x => (realMulBilinear.lpPairing volume 2 2) (kernelSectionContinuous K x) f := by
  filter_upwards [
    (evalBilinear (𝕜 := ℝ) (E := RealIntervalL2 a b)).coeFn_holder
      (r := (2 : ENNReal)) (kernelFunctionalField K)
      (Lp.const ∞ (volume : Measure (ClosedInterval a b)) f),
    ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (μ := (volume : Measure (ClosedInterval a b))) (kernelFunctionalContinuous K),
    Lp.coeFn_const (p := ∞) (volume : Measure (ClosedInterval a b)) f
  ] with x hholder hfield hconst
  rw [continuousKernelOperator, kernelOperator, kernelOperatorMap_apply,
    hholder, kernelFunctionalField, hfield, hconst]
  rfl

/-- The kernel pairing of real `L²` is the inner product. -/
theorem lpPairing_eq_inner (v f : RealIntervalL2 a b) :
    (realMulBilinear.lpPairing volume 2 2) v f = (inner ℝ v f : ℝ) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [realMulBilinear, RCLike.inner_apply, mul_comm]

/-- The operator is the integral operator with kernel `K`. -/
theorem continuousKernelOperator_coeFn (K : C(ClosedInterval a b × ClosedInterval a b, ℝ))
    (f : RealIntervalL2 a b) :
    (continuousKernelOperator K f : ClosedInterval a b → ℝ) =ᵐ[volume]
      fun x => ∫ y : ClosedInterval a b, K (x, y) * f y ∂volume := by
  filter_upwards [continuousKernelOperator_coeFn_pairing K f] with x hx
  rw [hx, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
    (μ := (volume : Measure (ClosedInterval a b))) (K.curry x)] with y hy
  change realMulBilinear ((ContinuousMap.toLp 2 volume ℝ (K.curry x)) y) (f y) = _
  rw [hy]
  simp [realMulBilinear]

/-- **The integral operator of a continuous kernel is compact.** -/
theorem isCompactOperator_continuousKernelOperator
    (K : C(ClosedInterval a b × ClosedInterval a b, ℝ)) :
    IsCompactOperator (continuousKernelOperator K) :=
  isCompactOperator_kernelOperator (volume : Measure (ClosedInterval a b))
    (kernelFunctionalField K)

/-- `L²` functions on a finite measure space are integrable. -/
theorem integrable_of_realIntervalL2 (f : RealIntervalL2 a b) :
    Integrable (f : ClosedInterval a b → ℝ) (volume : Measure (ClosedInterval a b)) :=
  (Lp.memLp f).integrable (by norm_num)

/-- **The quadratic form of a kernel operator is the double integral of its kernel.** -/
theorem inner_continuousKernelOperator_eq (K : C(ClosedInterval a b × ClosedInterval a b, ℝ))
    (f g : RealIntervalL2 a b) :
    (inner ℝ (continuousKernelOperator K f) g : ℝ)
      = ∫ x : ClosedInterval a b, ∫ y : ClosedInterval a b,
          K (x, y) * ((g x : ℝ) * (f y : ℝ)) ∂volume ∂volume := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [continuousKernelOperator_coeFn K f] with x hx
  rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

/-- The squared `L²` norm on the band is the integral of the square. -/
theorem norm_sq_eq_integral (f : RealIntervalL2 a b) :
    ‖f‖ ^ 2 = ∫ x : ClosedInterval a b, ((f x : ℝ)) ^ 2 ∂volume := by
  have h := L2.inner_def (𝕜 := ℝ) f f
  have hnorm : (inner ℝ f f : ℝ) = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f
  rw [hnorm] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

/-- **The integral operator of a symmetric continuous kernel is symmetric.**  Fubini for the bounded
kernel against two integrable functions. -/
theorem continuousKernelOperator_symmetric
    (K : C(ClosedInterval a b × ClosedInterval a b, ℝ))
    (hK : ∀ z : ClosedInterval a b × ClosedInterval a b, K z = K (z.2, z.1))
    (f g : RealIntervalL2 a b) :
    (inner ℝ (continuousKernelOperator K f) g : ℝ)
      = inner ℝ f (continuousKernelOperator K g) := by
  have hf := integrable_of_realIntervalL2 f
  have hg := integrable_of_realIntervalL2 g
  -- the product integrand is integrable
  have hprod : Integrable
      (fun z : ClosedInterval a b × ClosedInterval a b => (g z.1 : ℝ) * (f z.2 : ℝ))
      ((volume : Measure (ClosedInterval a b)).prod volume) := hg.mul_prod hf
  have hbdd : Integrable
      (fun z : ClosedInterval a b × ClosedInterval a b =>
        K (z.1, z.2) * ((g z.1 : ℝ) * (f z.2 : ℝ)))
      ((volume : Measure (ClosedInterval a b)).prod volume) :=
    hprod.bdd_mul (c := ‖K‖) K.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => K.norm_coe_le_norm _)
  -- both sides are the same double integral
  have hleft := inner_continuousKernelOperator_eq K f g
  have hright : (inner ℝ f (continuousKernelOperator K g) : ℝ)
      = ∫ y : ClosedInterval a b, ∫ x : ClosedInterval a b,
          K (x, y) * ((g x : ℝ) * (f y : ℝ)) ∂volume ∂volume := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [continuousKernelOperator_coeFn K g] with y hy
    rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, hy, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hK (y, x)]
    ring
  rw [hleft, hright]
  exact integral_integral_swap hbdd

/-! ## The operator norm of a kernel operator -/

/-- The rows of the kernel, unfolded. -/
theorem kernelSectionContinuous_apply (K : C(ClosedInterval a b × ClosedInterval a b, ℝ))
    (x : ClosedInterval a b) :
    kernelSectionContinuous K x = ContinuousMap.toLp 2 volume ℝ (K.curry x) := rfl

/-- The mass of the interval. -/
theorem measureUnivNNReal_interval (hab : a ≤ b) :
    ((measureUnivNNReal (volume : Measure (ClosedInterval a b)) : ℝ)) = b - a := by
  have h : ((measureUnivNNReal (volume : Measure (ClosedInterval a b)) : NNReal) : ENNReal)
      = ENNReal.ofReal (b - a) := by
    rw [coe_measureUnivNNReal, Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet,
      Real.volume_Icc]
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.coe_toReal, ENNReal.toReal_ofReal (by linarith)] at h2
  exact h2

/-- A kernel row is an `L²` vector of norm at most `√(b-a)` times the sup norm of the kernel. -/
theorem norm_toLp_curry_le (hab : a ≤ b) (K : C(ClosedInterval a b × ClosedInterval a b, ℝ))
    (x : ClosedInterval a b) :
    ‖ContinuousMap.toLp (2 : ENNReal) (volume : Measure (ClosedInterval a b)) ℝ (K.curry x)‖
      ≤ Real.sqrt (b - a) * ‖K‖ := by
  have hbd : ∀ᵐ y ∂(volume : Measure (ClosedInterval a b)),
      ‖(ContinuousMap.toLp (2 : ENNReal) (volume : Measure (ClosedInterval a b)) ℝ (K.curry x) :
        ClosedInterval a b → ℝ) y‖ ≤ ‖K‖ := by
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (μ := (volume : Measure (ClosedInterval a b))) (K.curry x)] with y hy
    rw [hy]
    exact K.norm_coe_le_norm (x, y)
  have h := Lp.norm_le_of_ae_bound
    (f := ContinuousMap.toLp (2 : ENNReal) (volume : Measure (ClosedInterval a b)) ℝ (K.curry x))
    (norm_nonneg K) hbd
  have hexp : ((2 : ENNReal).toReal)⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [hexp, measureUnivNNReal_interval hab, ← Real.sqrt_eq_rpow] at h
  exact h

/-- **Operator-norm bound from a kernel representation.**  Any bounded operator whose values are the
inner products against the rows of a continuous kernel has operator norm at most `(b-a)` times the
sup norm of the kernel.  Cauchy–Schwarz bounds the values pointwise by the row norms, and the row
norms by the sup norm; the `L²` norm of the output then costs one more factor `√(b-a)`. -/
theorem norm_le_of_kernel_repr (hab : a ≤ b)
    (G : C(ClosedInterval a b × ClosedInterval a b, ℝ))
    (B : RealIntervalL2 a b →L[ℝ] RealIntervalL2 a b)
    (hB : ∀ f : RealIntervalL2 a b, (B f : ClosedInterval a b → ℝ) =ᵐ[volume]
      fun x => (inner ℝ
        (ContinuousMap.toLp (2 : ENNReal) (volume : Measure (ClosedInterval a b)) ℝ (G.curry x))
        f : ℝ)) :
    ‖B‖ ≤ (b - a) * ‖G‖ := by
  have hba : (0 : ℝ) ≤ b - a := by linarith
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hba (norm_nonneg G)) fun f => ?_
  have hC : 0 ≤ Real.sqrt (b - a) * ‖G‖ * ‖f‖ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg G)) (norm_nonneg f)
  have hptw : ∀ᵐ x ∂(volume : Measure (ClosedInterval a b)),
      ‖(B f : ClosedInterval a b → ℝ) x‖ ≤ Real.sqrt (b - a) * ‖G‖ * ‖f‖ := by
    filter_upwards [hB f] with x hx
    rw [hx]
    calc ‖(inner ℝ
          (ContinuousMap.toLp (2 : ENNReal) (volume : Measure (ClosedInterval a b)) ℝ (G.curry x))
          f : ℝ)‖
        ≤ ‖ContinuousMap.toLp (2 : ENNReal) (volume : Measure (ClosedInterval a b)) ℝ
            (G.curry x)‖ * ‖f‖ := abs_real_inner_le_norm _ _
      _ ≤ (Real.sqrt (b - a) * ‖G‖) * ‖f‖ :=
          mul_le_mul_of_nonneg_right (norm_toLp_curry_le hab G x) (norm_nonneg f)
  have h := Lp.norm_le_of_ae_bound (f := B f) hC hptw
  have hexp : ((2 : ENNReal).toReal)⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [hexp, measureUnivNNReal_interval hab, ← Real.sqrt_eq_rpow] at h
  refine h.trans ?_
  rw [← mul_assoc, ← mul_assoc, Real.mul_self_sqrt hba]

/-- The kernel operator itself has the kernel representation. -/
theorem continuousKernelOperator_coeFn_inner
    (K : C(ClosedInterval a b × ClosedInterval a b, ℝ)) (f : RealIntervalL2 a b) :
    (continuousKernelOperator K f : ClosedInterval a b → ℝ) =ᵐ[volume]
      fun x => (inner ℝ
        (ContinuousMap.toLp (2 : ENNReal) (volume : Measure (ClosedInterval a b)) ℝ (K.curry x))
        f : ℝ) := by
  filter_upwards [continuousKernelOperator_coeFn_pairing K f] with x hx
  rw [hx, lpPairing_eq_inner, kernelSectionContinuous_apply]

/-- **The operator norm bound for a continuous kernel.** -/
theorem norm_continuousKernelOperator_le (hab : a ≤ b)
    (K : C(ClosedInterval a b × ClosedInterval a b, ℝ)) :
    ‖continuousKernelOperator K‖ ≤ (b - a) * ‖K‖ :=
  norm_le_of_kernel_repr hab K _ (continuousKernelOperator_coeFn_inner K)

/-- The rows of a linear combination of kernels are the combination of the rows. -/
theorem toLp_curry_comb (K L M : C(ClosedInterval a b × ClosedInterval a b, ℝ)) (r : ℝ)
    (x : ClosedInterval a b) :
    ContinuousMap.toLp (2 : ENNReal) (volume : Measure (ClosedInterval a b)) ℝ
        ((K - L - r • M).curry x)
      = ContinuousMap.toLp 2 volume ℝ (K.curry x)
        - ContinuousMap.toLp 2 volume ℝ (L.curry x)
        - r • ContinuousMap.toLp 2 volume ℝ (M.curry x) := by
  have hcurry : (K - L - r • M).curry x
      = K.curry x - L.curry x - r • M.curry x := ContinuousMap.ext fun y => rfl
  rw [hcurry, map_sub, map_sub, map_smul]

/-- **A linear combination of kernel operators is the kernel operator of the combination**, in the
form of a kernel representation.  This is what turns a bound on kernels into a bound on
operators. -/
theorem coeFn_comb_inner (K L M : C(ClosedInterval a b × ClosedInterval a b, ℝ)) (r : ℝ)
    (f : RealIntervalL2 a b) :
    ((continuousKernelOperator K - continuousKernelOperator L
        - r • continuousKernelOperator M) f : ClosedInterval a b → ℝ) =ᵐ[volume]
      fun x => (inner ℝ
        (ContinuousMap.toLp (2 : ENNReal) (volume : Measure (ClosedInterval a b)) ℝ
          ((K - L - r • M).curry x)) f : ℝ) := by
  filter_upwards [
    Lp.coeFn_sub (continuousKernelOperator K f - continuousKernelOperator L f)
      (r • continuousKernelOperator M f),
    Lp.coeFn_sub (continuousKernelOperator K f) (continuousKernelOperator L f),
    Lp.coeFn_smul r (continuousKernelOperator M f),
    continuousKernelOperator_coeFn_inner K f,
    continuousKernelOperator_coeFn_inner L f,
    continuousKernelOperator_coeFn_inner M f] with x hsub1 hsub2 hsmul hK hL hM
  have hval : ((continuousKernelOperator K - continuousKernelOperator L
      - r • continuousKernelOperator M) f : ClosedInterval a b → ℝ) x
      = (continuousKernelOperator K f : ClosedInterval a b → ℝ) x
        - (continuousKernelOperator L f : ClosedInterval a b → ℝ) x
        - r * (continuousKernelOperator M f : ClosedInterval a b → ℝ) x := by
    have h1 : ((continuousKernelOperator K - continuousKernelOperator L
        - r • continuousKernelOperator M) f)
        = (continuousKernelOperator K f - continuousKernelOperator L f)
          - r • continuousKernelOperator M f := by
      simp
    rw [h1, hsub1, Pi.sub_apply, hsub2, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul]
  rw [hval, hK, hL, hM, toLp_curry_comb, inner_sub_left, inner_sub_left, real_inner_smul_left]

/-- **Operator-norm bound for a difference of kernel operators.** -/
theorem norm_continuousKernelOperator_sub_le (hab : a ≤ b)
    (K L : C(ClosedInterval a b × ClosedInterval a b, ℝ)) :
    ‖continuousKernelOperator K - continuousKernelOperator L‖ ≤ (b - a) * ‖K - L‖ := by
  have hrepr : ∀ f : RealIntervalL2 a b,
      ((continuousKernelOperator K - continuousKernelOperator L) f
          : ClosedInterval a b → ℝ) =ᵐ[volume]
        fun x => (inner ℝ
          (ContinuousMap.toLp (2 : ENNReal) (volume : Measure (ClosedInterval a b)) ℝ
            ((K - L).curry x)) f : ℝ) := by
    intro f
    have h := coeFn_comb_inner K L K (0 : ℝ) f
    have hop : continuousKernelOperator K - continuousKernelOperator L
        - (0 : ℝ) • continuousKernelOperator K
        = continuousKernelOperator K - continuousKernelOperator L := by
      simp
    have hker : K - L - (0 : ℝ) • K = K - L := by
      simp
    rw [hop, hker] at h
    exact h
  exact norm_le_of_kernel_repr hab (K - L) _ hrepr

/-! ## The band operator -/

/-- The smoothed sinc kernel on the square `[-1, 1]²`, as a continuous map. -/
def sincKernelContinuous (c : ℝ) :
    C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℝ) where
  toFun z := sincKernelSmooth c (z.1 : ℝ) (z.2 : ℝ)
  continuous_toFun := by
    have h : Continuous fun z : ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1 =>
        ((z.1 : ℝ) - (z.2 : ℝ)) := by fun_prop
    simpa [sincKernelSmooth, Function.comp_def] using (contDiff_sincSmooth c).continuous.comp h

/-- **The band operator of aperture `c`** on real `L²[-1, 1]`. -/
def bandOperatorL2 (c : ℝ) : RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1 :=
  continuousKernelOperator (sincKernelContinuous c)

/-- The band operator is the integral operator with the smoothed sinc kernel. -/
theorem bandOperatorL2_coeFn (c : ℝ) (f : RealIntervalL2 (-1 : ℝ) 1) :
    (bandOperatorL2 c f : ClosedInterval (-1 : ℝ) 1 → ℝ) =ᵐ[volume]
      fun x => ∫ y : ClosedInterval (-1 : ℝ) 1,
        sincKernelSmooth c (x : ℝ) (y : ℝ) * f y ∂volume :=
  continuousKernelOperator_coeFn (sincKernelContinuous c) f

/-- **The band operator is compact.** -/
theorem isCompactOperator_bandOperatorL2 (c : ℝ) :
    IsCompactOperator (bandOperatorL2 c) :=
  isCompactOperator_continuousKernelOperator (sincKernelContinuous c)

/-- **The band operator is symmetric**, because the sinc kernel is. -/
theorem bandOperatorL2_symmetric (c : ℝ) (f g : RealIntervalL2 (-1 : ℝ) 1) :
    (inner ℝ (bandOperatorL2 c f) g : ℝ) = inner ℝ f (bandOperatorL2 c g) :=
  continuousKernelOperator_symmetric (sincKernelContinuous c)
    (fun z => sincKernelSmooth_symm c (z.1 : ℝ) (z.2 : ℝ)) f g

end GaloisForLFunctions.RHTower

end
