import GaloisForLFunctions.HTGeometry.DirichletLSeriesUpperEnd
import GaloisForLFunctions.HTGeometry.OperatorTailDirichletMatroid
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialField
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Differential compatibility of the faithful L-series realization

For `s = -I z`, differentiation in `z` corresponds to `I` times the logarithmic coefficient
derivation.  This file internalizes that rotation on the right-half-plane arithmetic subring and
proves that the faithful analytic-germ embedding intertwines the two derivations.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Filter Set Topology

noncomputable section

open scoped LSeries.notation

/-- Mathlib's complex logarithmic coefficient weight agrees with the project's real-log arithmetic
weight on natural-number coefficients. -/
theorem lSeries_logMul_eq_logWeight (f : ArithmeticFunction ℂ) :
    LSeries.logMul (fun n => f n) = fun n => logWeight f n := by
  funext n
  rw [logWeight_apply]
  change Complex.log (n : ℂ) * f n = (Real.log n : ℂ) * f n
  have hlog := Complex.ofReal_log (Nat.cast_nonneg n)
  have hcast : (((n : ℕ) : ℝ) : ℂ) = (n : ℂ) := by norm_num
  rw [hcast] at hlog
  rw [hlog]

/-- The logarithmic coefficient weight preserves absolute convergence on `Re s > 1`. -/
def rightHalfPlaneLogWeight (f : rightHalfPlaneArithmeticSubalgebra) :
    rightHalfPlaneArithmeticSubalgebra := by
  refine ⟨logWeight f.1, ?_⟩
  intro y hy
  have hlt : LSeries.abscissaOfAbsConv (fun n => f.1 n) < ((y : ℝ) : EReal) :=
    lt_of_le_of_lt (rightHalfPlaneArithmeticSubalgebra_abscissa_le_one f)
      (EReal.coe_lt_coe_iff.mpr hy)
  have hs := LSeriesSummable_logMul_of_lt_re
    (s := (y : ℂ)) (by simpa only [Complex.ofReal_re] using hlt)
  rw [lSeries_logMul_eq_logWeight] at hs
  exact hs

/-- The rotated differential coefficient operator: `D_z = I logWeight`. -/
def rightHalfPlaneRotatedDeriv (f : rightHalfPlaneArithmeticSubalgebra) :
    rightHalfPlaneArithmeticSubalgebra := by
  refine ⟨Complex.I • (rightHalfPlaneLogWeight f).1, ?_⟩
  intro y hy
  exact ((rightHalfPlaneLogWeight f).2 y hy).smul Complex.I

@[simp]
theorem rightHalfPlaneRotatedDeriv_apply
    (f : rightHalfPlaneArithmeticSubalgebra) (n : ℕ) :
    (rightHalfPlaneRotatedDeriv f).1 n =
      Complex.I * (Real.log n : ℂ) * f.1 n := by
  simp [rightHalfPlaneRotatedDeriv, rightHalfPlaneLogWeight,
    ArithmeticFunction.smul_map, logWeight_apply]
  ring

/-- The rotated coefficient operator is additive. -/
theorem rightHalfPlaneRotatedDeriv_add
    (f g : rightHalfPlaneArithmeticSubalgebra) :
    rightHalfPlaneRotatedDeriv (f + g) =
      rightHalfPlaneRotatedDeriv f + rightHalfPlaneRotatedDeriv g := by
  apply Subtype.ext
  ext n
  simp only [rightHalfPlaneRotatedDeriv_apply, Subalgebra.coe_add,
    ArithmeticFunction.add_apply]
  ring

/-- The rotated coefficient operator satisfies Leibniz for Dirichlet convolution. -/
theorem rightHalfPlaneRotatedDeriv_leibniz
    (f g : rightHalfPlaneArithmeticSubalgebra) :
    rightHalfPlaneRotatedDeriv (f * g) =
      rightHalfPlaneRotatedDeriv f * g + f * rightHalfPlaneRotatedDeriv g := by
  apply Subtype.ext
  change Complex.I • logWeight (f.1 * g.1) =
    Complex.I • logWeight f.1 * g.1 + f.1 * (Complex.I • logWeight g.1)
  rw [logWeight_leibniz, smul_add, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm]

/-- **Differential L-series transfer.**  Differentiating the rotated analytic L-series germ is
exactly the L-series germ of `I logWeight f`. -/
theorem upperEndAnalyticDeriv_rightHalfPlaneLSeries
    (f : rightHalfPlaneArithmeticSubalgebra) :
    upperEndAnalyticDeriv (rightHalfPlaneLSeriesToUpperEndAnalytic f) =
      rightHalfPlaneLSeriesToUpperEndAnalytic (rightHalfPlaneRotatedDeriv f) := by
  apply Subtype.ext
  change upperEndGermDeriv
      (Germ.coeRingHom upperEndFilter
        (fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z))) =
    Germ.coeRingHom upperEndFilter
      (fun z : ℂ => LSeries (fun n => (rightHalfPlaneRotatedDeriv f).1 n)
        (-Complex.I * z))
  change upperEndGermDeriv
      (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
        Germ upperEndFilter ℂ) =
    (↑(fun z : ℂ => LSeries (fun n => (rightHalfPlaneRotatedDeriv f).1 n)
      (-Complex.I * z)) : Germ upperEndFilter ℂ)
  rw [upperEndGermDeriv_coe]
  rw [Germ.coe_eq]
  change ∀ᶠ z in upperEndFilter,
    deriv (fun w : ℂ => LSeries (fun n => f.1 n) (-Complex.I * w)) z =
      LSeries (fun n => (rightHalfPlaneRotatedDeriv f).1 n) (-Complex.I * z)
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨1, trivial, fun z hz => ?_⟩
  have hlt : LSeries.abscissaOfAbsConv (fun n => f.1 n) <
      (((-Complex.I * z).re : ℝ) : EReal) := by
    have hre : (-Complex.I * z).re = z.im := by simp [Complex.mul_re]
    rw [hre]
    exact lt_of_le_of_lt (rightHalfPlaneArithmeticSubalgebra_abscissa_le_one f)
      (EReal.coe_lt_coe_iff.mpr (by simpa [upperTail] using hz))
  have houter := LSeries_hasDerivAt
    (s := -Complex.I * z) (f := fun n => f.1 n)
    (by simpa only using hlt)
  have hinner : HasDerivAt (fun w : ℂ => -Complex.I * w) (-Complex.I) z := by
    simpa only [mul_one] using (hasDerivAt_id z).const_mul (-Complex.I)
  have hcomp := houter.comp z hinner
  have hderiv : deriv (fun w : ℂ => LSeries (fun n => f.1 n) (-Complex.I * w)) z =
      (-LSeries (LSeries.logMul (fun n => f.1 n)) (-Complex.I * z)) *
        (-Complex.I) := by
    simpa only [Function.comp_apply] using hcomp.deriv
  rw [hderiv]
  have hcoeff : (fun n => (rightHalfPlaneRotatedDeriv f).1 n) =
      Complex.I • (fun n => logWeight f.1 n) := by
    funext n
    simp [rightHalfPlaneRotatedDeriv_apply]
    ring
  rw [hcoeff, LSeries_smul, ← lSeries_logMul_eq_logWeight]
  ring

end

end GaloisForLFunctions.HTGeometry
