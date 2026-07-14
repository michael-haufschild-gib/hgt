import GaloisForLFunctions.HTGeometry.DirichletLSeriesUpperEnd

/-!
# Finite-abscissa Dirichlet series at the complex upper end

Arithmetic functions whose Dirichlet series has some finite abscissa of absolute convergence form
a complex algebra. Rotation by `s = -I z` realizes this algebra faithfully as analytic germs at
the upper end. Unlike the fixed half-plane algebra, this carrier is stable under arbitrary finite
translations of the Dirichlet variable.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Filter Set Topology

noncomputable section

open scoped LSeries.notation

/-- Arithmetic functions absolutely summable to the right of some finite vertical line. -/
def finiteAbscissaArithmeticSubalgebra : Subalgebra ℂ (ArithmeticFunction ℂ) where
  carrier := {f | ∃ H : ℝ, ∀ y : ℝ, H < y →
    LSeriesSummable (fun n => f n) (y : ℂ)}
  zero_mem' := by
    refine ⟨0, fun y hy => ?_⟩
    change LSeriesSummable (0 : ℕ → ℂ) (y : ℂ)
    rw [LSeriesSummable]
    convert (summable_zero : Summable (0 : ℕ → ℂ)) using 1
    funext n
    simp [LSeries.term]
  one_mem' := by
    refine ⟨0, fun y hy => ?_⟩
    change LSeriesSummable (fun n => (1 : ArithmeticFunction ℂ) n) (y : ℂ)
    have hdelta : (fun n => (1 : ArithmeticFunction ℂ) n) = LSeries.delta := by
      funext n
      exact ArithmeticFunction.one_apply
    rw [hdelta, LSeriesSummable]
    apply summable_of_hasFiniteSupport
    refine Set.Finite.subset (Set.finite_singleton 1) ?_
    intro n hn
    simpa [Function.support, LSeries.term_delta] using hn
  add_mem' := by
    rintro f g ⟨H, hH⟩ ⟨K, hK⟩
    refine ⟨max H K, fun y hy => (hH y (lt_of_le_of_lt (le_max_left H K) hy)).add
      (hK y (lt_of_le_of_lt (le_max_right H K) hy))⟩
  mul_mem' := by
    rintro f g ⟨H, hH⟩ ⟨K, hK⟩
    refine ⟨max H K, fun y hy => ArithmeticFunction.LSeriesSummable_mul
      (hH y (lt_of_le_of_lt (le_max_left H K) hy))
      (hK y (lt_of_le_of_lt (le_max_right H K) hy))⟩
  algebraMap_mem' := by
    intro c
    refine ⟨1, fun y hy => ?_⟩
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := ‖c‖)
    · intro n hn
      by_cases h1 : n = 1 <;>
        simp [Algebra.algebraMap_eq_smul_one, ArithmeticFunction.smul_map,
          ArithmeticFunction.one_apply, h1]
    · simpa using hy

/-- A finite-abscissa element has absolute-convergence abscissa bounded by one of its witnesses. -/
theorem finiteAbscissaArithmetic_abscissa_le
    (f : finiteAbscissaArithmeticSubalgebra) :
    ∃ H : ℝ, LSeries.abscissaOfAbsConv (fun n => f.1 n) ≤ H := by
  obtain ⟨H, hH⟩ := f.2
  exact ⟨H, LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable hH⟩

/-- Rotation produces an analytic representative above a sufficiently high horizontal line. -/
theorem finiteAbscissa_rotatedLSeries_eventuallyAnalytic
    (f : finiteAbscissaArithmeticSubalgebra) :
    ∃ H : ℝ, AnalyticOnNhd ℂ
      (fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) (upperTail H) := by
  obtain ⟨H, hH⟩ := finiteAbscissaArithmetic_abscissa_le f
  refine ⟨H, (LSeries_analyticOnNhd (fun n => f.1 n)).comp
    (analyticOnNhd_const.mul analyticOnNhd_id) ?_⟩
  intro z hz
  change LSeries.abscissaOfAbsConv (fun n => f.1 n) <
    (((-Complex.I * z).re : ℝ) : EReal)
  have hre : (-Complex.I * z).re = z.im := by simp [Complex.mul_re]
  rw [hre]
  exact lt_of_le_of_lt hH (EReal.coe_lt_coe_iff.mpr (by simpa [upperTail] using hz))

/-- Constant complex germs as a ring homomorphism. -/
def complexToUpperEndGerm : ℂ →+* Germ upperEndFilter ℂ where
  toFun c := (c : Germ upperEndFilter ℂ)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The canonical complex-algebra structure on upper-end germs. -/
noncomputable instance upperEndGermAlgebra : Algebra ℂ (Germ upperEndFilter ℂ) :=
  complexToUpperEndGerm.toAlgebra

/-- Faithful rotated L-series realization for every finite absolute-convergence abscissa. -/
noncomputable def finiteAbscissaLSeriesToUpperEndGerm :
    finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] Germ upperEndFilter ℂ where
  toFun f := Germ.coeRingHom upperEndFilter
    (fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z))
  map_zero' := by
    change Germ.coeRingHom upperEndFilter
      (fun z : ℂ => LSeries (0 : ℕ → ℂ) (-Complex.I * z)) = 0
    simpa only [LSeries_zero, Pi.zero_apply] using
      (Germ.coeRingHom upperEndFilter).map_zero
  map_one' := by
    change Germ.coeRingHom upperEndFilter
      (fun z : ℂ => LSeries (fun n => (1 : ArithmeticFunction ℂ) n) (-Complex.I * z)) = 1
    have hdelta : (fun n => (1 : ArithmeticFunction ℂ) n) = LSeries.delta := by
      funext n
      exact ArithmeticFunction.one_apply
    rw [hdelta, LSeries_delta]
    exact (Germ.coeRingHom upperEndFilter).map_one
  map_add' := by
    intro f g
    obtain ⟨H, hH⟩ := f.2
    obtain ⟨K, hK⟩ := g.2
    change (↑(fun z : ℂ =>
        LSeries (fun n => (f + g : finiteAbscissaArithmeticSubalgebra).1 n)
          (-Complex.I * z)) : Germ upperEndFilter ℂ) =
      (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ) +
        (↑(fun z : ℂ => LSeries (fun n => g.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ)
    rw [← Germ.coe_add, Germ.coe_eq]
    change ∀ᶠ z in upperEndFilter,
      LSeries (fun n => (f + g : finiteAbscissaArithmeticSubalgebra).1 n)
          (-Complex.I * z) =
        LSeries (fun n => f.1 n) (-Complex.I * z) +
          LSeries (fun n => g.1 n) (-Complex.I * z)
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨max H K + 1, trivial, fun z hz => ?_⟩
    have hz' : max H K + 1 < z.im := by simpa [upperTail] using hz
    have hmax : max H K < z.im := (lt_add_one (max H K)).trans hz'
    apply LSeries_add
    · exact hH z.im (lt_of_le_of_lt (le_max_left H K) hmax)
    · exact hK z.im (lt_of_le_of_lt (le_max_right H K) hmax)
  map_mul' := by
    intro f g
    obtain ⟨H, hH⟩ := f.2
    obtain ⟨K, hK⟩ := g.2
    change (↑(fun z : ℂ =>
        LSeries (fun n => (f * g : finiteAbscissaArithmeticSubalgebra).1 n)
          (-Complex.I * z)) : Germ upperEndFilter ℂ) =
      (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ) *
        (↑(fun z : ℂ => LSeries (fun n => g.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ)
    rw [← Germ.coe_mul, Germ.coe_eq]
    change ∀ᶠ z in upperEndFilter,
      LSeries (fun n => (f * g : finiteAbscissaArithmeticSubalgebra).1 n)
          (-Complex.I * z) =
        LSeries (fun n => f.1 n) (-Complex.I * z) *
          LSeries (fun n => g.1 n) (-Complex.I * z)
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨max H K + 1, trivial, fun z hz => ?_⟩
    have hz' : max H K + 1 < z.im := by simpa [upperTail] using hz
    have hmax : max H K < z.im := (lt_add_one (max H K)).trans hz'
    apply ArithmeticFunction.LSeries_mul'
    · exact hH z.im (lt_of_le_of_lt (le_max_left H K) hmax)
    · exact hK z.im (lt_of_le_of_lt (le_max_right H K) hmax)
  commutes' := by
    intro c
    change Germ.coeRingHom upperEndFilter
        (fun z : ℂ => LSeries
          (fun n => (algebraMap ℂ (ArithmeticFunction ℂ) c) n) (-Complex.I * z)) =
      algebraMap ℂ (Germ upperEndFilter ℂ) c
    have hcoeff : (fun n => (algebraMap ℂ (ArithmeticFunction ℂ) c) n) =
        c • LSeries.delta := by
      funext n
      simp [Algebra.algebraMap_eq_smul_one, ArithmeticFunction.smul_map,
        ArithmeticFunction.one_apply, LSeries.delta]
    rw [hcoeff]
    change (↑(fun z : ℂ => LSeries (c • LSeries.delta) (-Complex.I * z)) :
      Germ upperEndFilter ℂ) = algebraMap ℂ (Germ upperEndFilter ℂ) c
    have hfun : (fun z : ℂ => LSeries (c • LSeries.delta) (-Complex.I * z)) =
        fun _ => c := by
      funext z
      rw [LSeries_smul, LSeries_delta]
      simp
    rw [hfun]
    rfl

end

end GaloisForLFunctions.HTGeometry
