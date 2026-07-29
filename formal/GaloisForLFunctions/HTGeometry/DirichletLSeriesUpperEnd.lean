import GaloisForLFunctions.HTGeometry.UpperEndMeromorphicField
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Faithful Dirichlet-series realization at the upper end

Arithmetic functions whose L-series converge absolutely throughout `Re s > 1` form a subring.
After the rotation `s = -I z`, their L-series are analytic on the upper half-plane `Im z > 1` and
therefore define upper-end analytic germs.  Dirichlet convolution becomes multiplication, and
Dirichlet coefficient uniqueness makes the realization injective.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Filter Set Topology

noncomputable section

open scoped LSeries.notation

/-- Arithmetic functions whose L-series converge absolutely on the full right half-plane
`Re s > 1`. -/
def rightHalfPlaneArithmeticSubalgebra : Subalgebra ℂ (ArithmeticFunction ℂ) where
  carrier := {f | ∀ y : ℝ, 1 < y → LSeriesSummable (fun n => f n) (y : ℂ)}
  zero_mem' := by
    intro y hy
    change LSeriesSummable (0 : ℕ → ℂ) (y : ℂ)
    rw [LSeriesSummable]
    convert (summable_zero : Summable (0 : ℕ → ℂ)) using 1
    funext n
    simp [LSeries.term]
  one_mem' := by
    intro y hy
    change LSeriesSummable (fun n => (1 : ArithmeticFunction ℂ) n) (y : ℂ)
    rw [LSeriesSummable]
    have hdelta : (fun n => (1 : ArithmeticFunction ℂ) n) = LSeries.delta := by
      funext n
      exact ArithmeticFunction.one_apply
    rw [hdelta]
    apply summable_of_hasFiniteSupport
    refine Set.Finite.subset (Set.finite_singleton 1) ?_
    intro n hn
    simpa [Function.support, LSeries.term_delta] using hn
  add_mem' := by
    intro f g hf hg y hy
    exact (hf y hy).add (hg y hy)
  mul_mem' := by
    intro f g hf hg y hy
    exact ArithmeticFunction.LSeriesSummable_mul (hf y hy) (hg y hy)
  algebraMap_mem' := by
    intro c y hy
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := ‖c‖)
    · intro n hn
      by_cases h1 : n = 1 <;>
        simp [Algebra.algebraMap_eq_smul_one, ArithmeticFunction.smul_map, h1]
    · simpa using hy

/-- Every member has absolute-convergence abscissa at most one. -/
theorem rightHalfPlaneArithmeticSubalgebra_abscissa_le_one
    (f : rightHalfPlaneArithmeticSubalgebra) :
    LSeries.abscissaOfAbsConv (fun n => f.1 n) ≤ (1 : ℝ) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable f.2

/-- Rotating a right-half-plane L-series produces an analytic function on the upper tail
`Im z > 1`. -/
theorem analyticOnNhd_rotatedLSeries (f : rightHalfPlaneArithmeticSubalgebra) :
    AnalyticOnNhd ℂ (fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z))
      (upperTail 1) := by
  have hinner : AnalyticOnNhd ℂ (fun z : ℂ => -Complex.I * z) (upperTail 1) :=
    analyticOnNhd_const.mul analyticOnNhd_id
  exact (LSeries_analyticOnNhd (fun n => f.1 n)).comp hinner (by
    intro z hz
    simp only [upperTail, mem_setOf_eq] at hz
    change LSeries.abscissaOfAbsConv (fun n => f.1 n) <
      (((-Complex.I * z).re : ℝ) : EReal)
    have hre : (-Complex.I * z).re = z.im := by
      simp [Complex.mul_re]
    rw [hre]
    exact lt_of_le_of_lt (rightHalfPlaneArithmeticSubalgebra_abscissa_le_one f)
      (EReal.coe_lt_coe_iff.mpr hz))

/-- A convergent arithmetic function as an eventual analytic upper-end germ. -/
def rotatedLSeriesUpperEndAnalytic (f : rightHalfPlaneArithmeticSubalgebra) :
    upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter
      (fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)),
    (fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)), 1,
    analyticOnNhd_rotatedLSeries f, rfl⟩

/-- Absolute summability at the rotated point follows from upper-tail membership. -/
theorem rightHalfPlaneArithmeticSubalgebra_summable_rotated
    (f : rightHalfPlaneArithmeticSubalgebra) {z : ℂ} (hz : z ∈ upperTail 1) :
    LSeriesSummable (fun n => f.1 n) (-Complex.I * z) := by
  have hreal := f.2 z.im (by simpa [upperTail] using hz)
  exact (LSeriesSummable_iff_of_re_eq_re (by simp [Complex.mul_re])).mpr hreal

/-- **Faithful analytic L-series realization.**  The rotated L-series construction is a ring
homomorphism from the right-half-plane convolution algebra to upper-end analytic germs. -/
noncomputable def rightHalfPlaneLSeriesToUpperEndAnalytic :
    rightHalfPlaneArithmeticSubalgebra →+* upperEndAnalyticSubring where
  toFun := rotatedLSeriesUpperEndAnalytic
  map_zero' := by
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    change Germ.coeRingHom upperEndFilter
      (fun z : ℂ => LSeries (0 : ℕ → ℂ) (-Complex.I * z)) = 0
    simp only [LSeries_zero, Pi.zero_apply]
    change Germ.coeRingHom upperEndFilter (0 : ℂ → ℂ) = 0
    exact (Germ.coeRingHom upperEndFilter).map_zero
  map_one' := by
    apply Subtype.ext
    rw [OneMemClass.coe_one]
    change Germ.coeRingHom upperEndFilter
      (fun z : ℂ => LSeries (fun n => (1 : ArithmeticFunction ℂ) n) (-Complex.I * z)) = 1
    have hdelta : (fun n => (1 : ArithmeticFunction ℂ) n) = LSeries.delta := by
      funext n
      exact ArithmeticFunction.one_apply
    rw [hdelta, LSeries_delta]
    exact (Germ.coeRingHom upperEndFilter).map_one
  map_add' f g := by
    apply Subtype.ext
    change Germ.coeRingHom upperEndFilter
        (fun z : ℂ => LSeries (fun n => (f + g : rightHalfPlaneArithmeticSubalgebra).1 n)
          (-Complex.I * z)) =
      Germ.coeRingHom upperEndFilter
        (fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) +
      Germ.coeRingHom upperEndFilter
        (fun z : ℂ => LSeries (fun n => g.1 n) (-Complex.I * z))
    change (↑(fun z : ℂ =>
        LSeries (fun n => (f + g : rightHalfPlaneArithmeticSubalgebra).1 n)
          (-Complex.I * z)) : Germ upperEndFilter ℂ) =
      (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ) +
        (↑(fun z : ℂ => LSeries (fun n => g.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ)
    rw [← Germ.coe_add, Germ.coe_eq]
    change ∀ᶠ z in upperEndFilter,
      LSeries (fun n => (f + g : rightHalfPlaneArithmeticSubalgebra).1 n) (-Complex.I * z) =
        LSeries (fun n => f.1 n) (-Complex.I * z) +
          LSeries (fun n => g.1 n) (-Complex.I * z)
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨1, trivial, fun z hz => ?_⟩
    exact LSeries_add (rightHalfPlaneArithmeticSubalgebra_summable_rotated f hz)
      (rightHalfPlaneArithmeticSubalgebra_summable_rotated g hz)
  map_mul' f g := by
    apply Subtype.ext
    change Germ.coeRingHom upperEndFilter
        (fun z : ℂ => LSeries (fun n => (f * g : rightHalfPlaneArithmeticSubalgebra).1 n)
          (-Complex.I * z)) =
      Germ.coeRingHom upperEndFilter
        (fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) *
      Germ.coeRingHom upperEndFilter
        (fun z : ℂ => LSeries (fun n => g.1 n) (-Complex.I * z))
    change (↑(fun z : ℂ =>
        LSeries (fun n => (f * g : rightHalfPlaneArithmeticSubalgebra).1 n)
          (-Complex.I * z)) : Germ upperEndFilter ℂ) =
      (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ) *
        (↑(fun z : ℂ => LSeries (fun n => g.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ)
    rw [← Germ.coe_mul, Germ.coe_eq]
    change ∀ᶠ z in upperEndFilter,
      LSeries (fun n => (f * g : rightHalfPlaneArithmeticSubalgebra).1 n) (-Complex.I * z) =
        LSeries (fun n => f.1 n) (-Complex.I * z) *
          LSeries (fun n => g.1 n) (-Complex.I * z)
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨1, trivial, fun z hz => ?_⟩
    exact ArithmeticFunction.LSeries_mul'
      (rightHalfPlaneArithmeticSubalgebra_summable_rotated f hz)
      (rightHalfPlaneArithmeticSubalgebra_summable_rotated g hz)

/-- Equality of realized upper-end germs forces equality of every Dirichlet coefficient. -/
theorem rightHalfPlaneLSeriesToUpperEndAnalytic_injective :
    Function.Injective rightHalfPlaneLSeriesToUpperEndAnalytic := by
  intro f g hfg
  have hgerm := congrArg Subtype.val hfg
  change Germ.coeRingHom upperEndFilter
      (fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) =
    Germ.coeRingHom upperEndFilter
      (fun z : ℂ => LSeries (fun n => g.1 n) (-Complex.I * z)) at hgerm
  change (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
      Germ upperEndFilter ℂ) =
    (↑(fun z : ℂ => LSeries (fun n => g.1 n) (-Complex.I * z)) :
      Germ upperEndFilter ℂ) at hgerm
  rw [Germ.coe_eq] at hgerm
  change ∀ᶠ z in upperEndFilter,
    LSeries (fun n => f.1 n) (-Complex.I * z) =
      LSeries (fun n => g.1 n) (-Complex.I * z) at hgerm
  rw [upperEndFilter_basis.eventually_iff] at hgerm
  obtain ⟨H, -, hH⟩ := hgerm
  have hevent : (fun x : ℝ => LSeries (fun n => f.1 n) (x : ℂ)) =ᶠ[atTop]
      (fun x : ℝ => LSeries (fun n => g.1 n) (x : ℂ)) := by
    filter_upwards [eventually_gt_atTop H] with x hx
    have hz := hH (show Complex.I * (x : ℂ) ∈ upperTail H by
      simpa [upperTail, Complex.mul_im] using hx)
    have hrot : -Complex.I * (Complex.I * (x : ℂ)) = (x : ℂ) := by
      calc
        -Complex.I * (Complex.I * (x : ℂ)) =
            (-Complex.I * Complex.I) * (x : ℂ) := (mul_assoc _ _ _).symm
        _ = (x : ℂ) := by rw [neg_mul, Complex.I_mul_I]; ring
    simpa only [hrot] using hz
  apply Subtype.ext
  apply ArithmeticFunction.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero]
  · exact LSeries.eq_of_LSeries_eventually_eq
      ((rightHalfPlaneArithmeticSubalgebra_abscissa_le_one f).trans_lt
        (EReal.coe_lt_top (1 : ℝ)))
      ((rightHalfPlaneArithmeticSubalgebra_abscissa_le_one g).trans_lt
        (EReal.coe_lt_top (1 : ℝ)))
      hevent hn

end

end GaloisForLFunctions.HTGeometry
