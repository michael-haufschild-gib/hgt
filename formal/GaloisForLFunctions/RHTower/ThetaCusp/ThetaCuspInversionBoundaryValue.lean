import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFourierLaplace

/-!
# The one-sided theta boundary reflection value

The completed theta source is even in logarithmic coordinates.  Splitting its Fourier--Laplace
transform at an arbitrary boundary `x` therefore gives a source-only reflection relation: the two
opposite one-sided primitives add to `exp (i w x) * XiC w`.  Consequently a completed Xi zero is
exactly the anti-invariance of this boundary primitive under `(w, x) ↦ (-w, -x)`.

This is static bridge infrastructure for the Hedenmalm theta boundary problem.  It does not prove
that any zero parameter is real: the reflection defect is exactly the Xi value, so the resulting
constraint is a value reformulation rather than an independent RH mechanism.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The left boundary primitive of the completed theta source in logarithmic coordinates. -/
def thetaCuspBoundaryPrimitive (w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (I * w * (x : ℂ)) *
    ∫ y : ℝ in Iic x, thetaCuspFourierLaplaceIntegrand w y

/-- The unnormalized failure of the one-sided theta primitive to be anti-invariant under
simultaneous spectral and boundary reflection. -/
def thetaCuspBoundaryReflectionDefect (x : ℝ) (w : ℂ) : ℂ :=
  thetaCuspBoundaryPrimitive w x +
    thetaCuspBoundaryPrimitive (-w) (-x)

/-- Inversion reflection turns the opposite boundary primitive into the complementary
half-line integral. -/
theorem integral_thetaCuspFourierLaplaceIntegrand_reflection
    (w : ℂ) (x : ℝ) :
    (∫ y : ℝ in Iic (-x), thetaCuspFourierLaplaceIntegrand (-w) y) =
      ∫ y : ℝ in Ioi x, thetaCuspFourierLaplaceIntegrand w y := by
  calc
    _ = ∫ y : ℝ in Ioi x,
        thetaCuspFourierLaplaceIntegrand (-w) (-y) :=
      (integral_comp_neg_Ioi x
        (thetaCuspFourierLaplaceIntegrand (-w))).symm
    _ = ∫ y : ℝ in Ioi x, thetaCuspFourierLaplaceIntegrand w y := by
      apply integral_congr_ae
      filter_upwards with y
      rw [thetaCuspFourierLaplaceIntegrand, thetaCuspFourierLaplaceIntegrand,
        thetaCuspFullSource_neg]
      congr 2
      push_cast
      ring

/-- The completed Xi value is exactly the defect of anti-invariance of the one-sided theta
boundary primitive under `(w,x) ↦ (-w,-x)`. -/
theorem thetaCuspBoundaryPrimitive_reflection_defect
    {w : ℂ} (hw : |w.im| < 1) (x : ℝ) :
    thetaCuspBoundaryPrimitive w x +
        thetaCuspBoundaryPrimitive (-w) (-x) =
      Complex.exp (I * w * (x : ℂ)) * XiC w := by
  have hwInt : Integrable (thetaCuspFourierLaplaceIntegrand w) :=
    integrable_thetaCuspFourierLaplaceIntegrand hw
  have hsplit :
      (∫ y : ℝ in Iic x, thetaCuspFourierLaplaceIntegrand w y) +
          (∫ y : ℝ in Ioi x, thetaCuspFourierLaplaceIntegrand w y) =
        ∫ y : ℝ, thetaCuspFourierLaplaceIntegrand w y := by
    simpa only [compl_Iic] using
      integral_add_compl (f := thetaCuspFourierLaplaceIntegrand w)
        measurableSet_Iic hwInt
  have hwStrip : w ∈ thetaCuspFourierLaplaceStrip := by
    rw [thetaCuspFourierLaplaceStrip]
    exact abs_lt.mp hw
  have hXi : thetaCuspFourierLaplace w = XiC w :=
    thetaCuspFourierLaplace_eq_XiC_on_strip hwStrip
  have hexp :
      Complex.exp (I * (-w) * ((-x : ℝ) : ℂ)) =
        Complex.exp (I * w * (x : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [thetaCuspBoundaryPrimitive, thetaCuspBoundaryPrimitive, hexp,
    integral_thetaCuspFourierLaplaceIntegrand_reflection]
  rw [← mul_add, hsplit, ← thetaCuspFourierLaplace, hXi]

/-- The boundary reflection defect is the centered Xi function in the explicit nonvanishing
exponential gauge determined by the cut. -/
theorem thetaCuspBoundaryReflectionDefect_eq
    {w : ℂ} (hw : |w.im| < 1) (x : ℝ) :
    thetaCuspBoundaryReflectionDefect x w =
      Complex.exp (I * w * (x : ℂ)) * XiC w := by
  simpa only [thetaCuspBoundaryReflectionDefect] using
    thetaCuspBoundaryPrimitive_reflection_defect hw x

/-- **All-order boundary-defect jet law.**  Every spectral jet of the unnormalized one-sided
reflection defect is the triangular Leibniz transform of the centered Xi jet by the cut-dependent
exponential gauge. -/
theorem iteratedDeriv_thetaCuspBoundaryReflectionDefect
    (k : ℕ) {w : ℂ} (hw : |w.im| < 1) (x : ℝ) :
    iteratedDeriv k (thetaCuspBoundaryReflectionDefect x) w =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) *
          ((I * (x : ℂ)) ^ i * Complex.exp (I * w * (x : ℂ))) *
            iteratedDeriv (k - i) XiC w := by
  have hopen : IsOpen {z : ℂ | |z.im| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have heq : thetaCuspBoundaryReflectionDefect x =ᶠ[𝓝 w]
      fun z : ℂ => Complex.exp (I * z * (x : ℂ)) * XiC z := by
    filter_upwards [hopen.mem_nhds hw] with z hz
    exact thetaCuspBoundaryReflectionDefect_eq hz x
  rw [heq.iteratedDeriv_eq k]
  change iteratedDeriv k
    ((fun z : ℂ => Complex.exp (I * z * (x : ℂ))) * XiC) w = _
  rw [iteratedDeriv_mul
    (by fun_prop : ContDiffAt ℂ k
      (fun z : ℂ => Complex.exp (I * z * (x : ℂ))) w)
    ((XiC_analytic w (Set.mem_univ w)).contDiffAt.of_le le_top)]
  apply Finset.sum_congr rfl
  intro i hi
  have hexp :
      iteratedDeriv i (fun z : ℂ => Complex.exp (I * z * (x : ℂ))) w =
        (I * (x : ℂ)) ^ i * Complex.exp (I * w * (x : ℂ)) := by
    rw [show (fun z : ℂ => Complex.exp (I * z * (x : ℂ))) =
        fun z : ℂ => Complex.exp ((I * (x : ℂ)) * z) by
      funext z
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      congrFun (iteratedDeriv_cexp_const_mul i (I * (x : ℂ))) w
  rw [hexp]

/-- At the fixed logarithmic boundary, the two reflected one-sided source values add to the
completed Xi value. -/
theorem thetaCuspBoundaryPrimitive_midpoint_value_relation
    {w : ℂ} (hw : |w.im| < 1) :
    thetaCuspBoundaryPrimitive w 0 +
        thetaCuspBoundaryPrimitive (-w) 0 = XiC w := by
  simpa using thetaCuspBoundaryPrimitive_reflection_defect hw 0

/-- The static anti-reflection boundary constraint is pointwise equivalent to the completed
Xi zero relation. -/
theorem thetaCuspBoundaryPrimitive_anti_reflection_iff_XiC_eq_zero
    {w : ℂ} (hw : |w.im| < 1) (x : ℝ) :
    thetaCuspBoundaryPrimitive w x +
        thetaCuspBoundaryPrimitive (-w) (-x) = 0 ↔
      XiC w = 0 := by
  rw [thetaCuspBoundaryPrimitive_reflection_defect hw]
  exact mul_eq_zero.trans (or_iff_right (Complex.exp_ne_zero _))

/-- The source-only inversion constraint for the Hedenmalm boundary primitive. -/
def ThetaCuspBoundaryAntiReflection (w : ℂ) : Prop :=
  ∀ x : ℝ,
    thetaCuspBoundaryPrimitive w x +
      thetaCuspBoundaryPrimitive (-w) (-x) = 0

/-- On the natural Fourier--Laplace strip, the source-only inversion constraint is exactly the
completed Xi zero relation. -/
theorem thetaCuspBoundaryAntiReflection_iff_XiC_eq_zero
    {w : ℂ} (hw : |w.im| < 1) :
    ThetaCuspBoundaryAntiReflection w ↔ XiC w = 0 := by
  constructor
  · intro h
    exact (thetaCuspBoundaryPrimitive_anti_reflection_iff_XiC_eq_zero hw 0).mp (h 0)
  · intro h x
    exact (thetaCuspBoundaryPrimitive_anti_reflection_iff_XiC_eq_zero hw x).mpr h

end RHTower
