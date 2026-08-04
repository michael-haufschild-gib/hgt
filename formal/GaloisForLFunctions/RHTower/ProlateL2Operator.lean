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

/-- The operator is the integral operator with kernel `K`. -/
theorem continuousKernelOperator_coeFn (K : C(ClosedInterval a b × ClosedInterval a b, ℝ))
    (f : RealIntervalL2 a b) :
    (continuousKernelOperator K f : ClosedInterval a b → ℝ) =ᵐ[volume]
      fun x => ∫ y : ClosedInterval a b, K (x, y) * f y ∂volume := by
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
  change (realMulBilinear.lpPairing volume 2 2 (kernelSectionContinuous K x)) f = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
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
    Integrable (f : ClosedInterval a b → ℝ) (volume : Measure (ClosedInterval a b)) := by
  have h : MemLp (f : ClosedInterval a b → ℝ) 1 (volume : Measure (ClosedInterval a b)) :=
    (Lp.memLp f).mono_exponent_of_measure_support_ne_top (fun _ _ => id) (by simp) (by norm_num)
  exact (memLp_one_iff_integrable).1 h

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
      ((volume : Measure (ClosedInterval a b)).prod volume) := hg.prod_mul hf
  have hbdd : Integrable
      (fun z : ClosedInterval a b × ClosedInterval a b => K z * ((g z.1 : ℝ) * (f z.2 : ℝ)))
      ((volume : Measure (ClosedInterval a b)).prod volume) := by
    refine hprod.bdd_mul' (c := ‖K‖) ?_ ?_
    · exact K.continuous.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => K.norm_coe_le_norm z
  -- both sides are the same double integral
  have hleft : (inner ℝ (continuousKernelOperator K f) g : ℝ)
      = ∫ x : ClosedInterval a b, ∫ y : ClosedInterval a b,
          K (x, y) * ((g x : ℝ) * (f y : ℝ)) ∂volume ∂volume := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [continuousKernelOperator_coeFn K f] with x hx
    rw [starRingEnd_apply, star_trivial, hx, ← integral_mul_right]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have hright : (inner ℝ f (continuousKernelOperator K g) : ℝ)
      = ∫ y : ClosedInterval a b, ∫ x : ClosedInterval a b,
          K (x, y) * ((g x : ℝ) * (f y : ℝ)) ∂volume ∂volume := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [continuousKernelOperator_coeFn K g] with y hy
    rw [starRingEnd_apply, star_trivial, hy, ← integral_mul_left]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hK (x, y)]
    ring
  rw [hleft, hright]
  exact integral_integral_swap hbdd

/-! ## The band operator -/

/-- The smoothed sinc kernel on the square `[-1, 1]²`, as a continuous map. -/
def sincKernelContinuous (c : ℝ) :
    C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℝ) where
  toFun z := sincKernelSmooth c (z.1 : ℝ) (z.2 : ℝ)
  continuous_toFun := by
    have h : Continuous fun z : ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1 =>
        ((z.1 : ℝ) - (z.2 : ℝ)) := by fun_prop
    simpa [sincKernelSmooth] using (contDiff_sincSmooth c).continuous.comp h

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
