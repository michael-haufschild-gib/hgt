import GaloisForLFunctions.HTGeometry.AffineDynamics.PolynomialPeriodCentralizer
import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import Mathlib.Topology.Homeomorph.Defs

/-!
# Smooth function subgroups in the period centralizer

A Schwartz function of any one period coordinate generates a complete
vertical flow. Its time-one map and inverse are smooth, commute with every
period shear, and recover the entire Schwartz parameter. Polynomial-Gaussian
functions inject linearly into the parameter space.

This realizes the invariant-function and invariant-vector-field mechanism
of Proposition 3.1 of https://arxiv.org/abs/2611.14187 on the existing period
coordinates, including actual smooth maps and complete flows.
-/

noncomputable section
open scoped ContDiff
namespace GaloisForLFunctions.HTGeometry
variable {ι : Type*} [Fintype ι]

/-- Time-one translation with a rapidly decreasing smooth function as parameter. -/
def schwartzPeriodTranslation (i : ι) (f : SchwartzMap ℝ ℝ) :
    Equiv.Perm (PeriodCoordinates ℝ ι) :=
  invariantPeriodTranslation (fun w => f (w i))

theorem schwartzPeriodTranslation_contDiff (i : ι) (f : SchwartzMap ℝ ℝ) :
    ContDiff ℝ ∞ (schwartzPeriodTranslation i f : PeriodCoordinates ℝ ι → _) := by
  exact (contDiff_fst.add ((f.smooth ⊤).comp
    ((contDiff_apply ℝ ℝ i).comp contDiff_snd))).prodMk contDiff_snd

theorem schwartzPeriodTranslation_symm_contDiff (i : ι) (f : SchwartzMap ℝ ℝ) :
    ContDiff ℝ ∞ ((schwartzPeriodTranslation i f).symm : PeriodCoordinates ℝ ι → _) := by
  exact (contDiff_fst.sub ((f.smooth ⊤).comp
    ((contDiff_apply ℝ ℝ i).comp contDiff_snd))).prodMk contDiff_snd

/-- The translation is a homeomorphism with smooth inverse. -/
def schwartzPeriodHomeomorph (i : ι) (f : SchwartzMap ℝ ℝ) :
    PeriodCoordinates ℝ ι ≃ₜ PeriodCoordinates ℝ ι where
  toEquiv := schwartzPeriodTranslation i f
  continuous_toFun := (schwartzPeriodTranslation_contDiff i f).continuous
  continuous_invFun := (schwartzPeriodTranslation_symm_contDiff i f).continuous

omit [Fintype ι] in
theorem schwartzPeriodTranslation_commutes (i j : ι) (f : SchwartzMap ℝ ℝ)
    (q : PeriodCoordinates ℝ ι) :
    schwartzPeriodTranslation i f (periodShear j q) =
      periodShear j (schwartzPeriodTranslation i f q) :=
  invariantPeriodTranslation_commutes _ _ _

/-- Addition of functions is exactly composition of the corresponding symmetries. -/
def schwartzPeriodAction (i : ι) :
    Multiplicative (SchwartzMap ℝ ℝ) →* Equiv.Perm (PeriodCoordinates ℝ ι) where
  toFun f := schwartzPeriodTranslation i f.toAdd
  map_one' := by ext q <;> simp [schwartzPeriodTranslation, invariantPeriodTranslation]
  map_mul' f g := by
    change invariantPeriodTranslation (fun w => (f.toAdd + g.toAdd) (w i)) = _
    exact invariantPeriodTranslation_add _ _

omit [Fintype ι] in
/-- The action loses no parameter: evaluate on points with constant period coordinates. -/
theorem schwartzPeriodTranslation_injective (i : ι) :
    Function.Injective (schwartzPeriodTranslation i) := by
  intro f g h
  apply SchwartzMap.ext
  intro x
  have he := invariantPeriodTranslation_injective h
  exact congrFun he (fun _ => x)

omit [Fintype ι] in
theorem schwartzPeriodAction_injective (i : ι) :
    Function.Injective (schwartzPeriodAction i) := by
  intro f g h
  exact schwartzPeriodTranslation_injective i h

/-- A complete one-parameter flow, defined for every real time. -/
def schwartzPeriodFlow (i : ι) (f : SchwartzMap ℝ ℝ) (t : ℝ) :
    Equiv.Perm (PeriodCoordinates ℝ ι) := schwartzPeriodTranslation i (t • f)

omit [Fintype ι] in
theorem schwartzPeriodFlow_zero (i : ι) (f : SchwartzMap ℝ ℝ) :
    schwartzPeriodFlow i f 0 = 1 := by
  ext q <;> simp [schwartzPeriodFlow, schwartzPeriodTranslation, invariantPeriodTranslation]

omit [Fintype ι] in
theorem schwartzPeriodFlow_add (i : ι) (f : SchwartzMap ℝ ℝ) (s t : ℝ) :
    schwartzPeriodFlow i f (s + t) = schwartzPeriodFlow i f s * schwartzPeriodFlow i f t := by
  unfold schwartzPeriodFlow
  rw [add_smul]
  exact (schwartzPeriodAction i).map_mul (Multiplicative.ofAdd (s • f))
    (Multiplicative.ofAdd (t • f))

/-- Smoothness holds jointly in time and the initial point. -/
theorem schwartzPeriodFlow_contDiff (i : ι) (f : SchwartzMap ℝ ℝ) :
    ContDiff ℝ ∞ (fun tq : ℝ × PeriodCoordinates ℝ ι =>
      schwartzPeriodFlow i f tq.1 tq.2) := by
  have hf := f.smooth ⊤
  have h : ContDiff ℝ ∞ (fun tq : ℝ × PeriodCoordinates ℝ ι =>
      (tq.2.1 + tq.1 * f (tq.2.2 i), tq.2.2)) := by fun_prop
  simpa [schwartzPeriodFlow, schwartzPeriodTranslation, invariantPeriodTranslation,
    smul_eq_mul] using h

/-- The generating vector field is the actual time derivative of the complete flow. -/
theorem hasDerivAt_schwartzPeriodFlow (i : ι) (f : SchwartzMap ℝ ℝ)
    (q : PeriodCoordinates ℝ ι) (t : ℝ) :
    HasDerivAt (fun s => schwartzPeriodFlow i f s q) (f (q.2 i), 0) t := by
  have h := ((hasDerivAt_const t q.1).add
    ((hasDerivAt_id t).mul_const (f (q.2 i)))).prodMk (hasDerivAt_const t q.2)
  simpa [schwartzPeriodFlow, schwartzPeriodTranslation, invariantPeriodTranslation,
    smul_eq_mul] using h

/-- Polynomial multiples of a positive Gaussian embed into the symmetry parameters. -/
def polynomialGaussianParameter : Polynomial ℝ →ₗ[ℝ] SchwartzMap ℝ ℝ where
  toFun := polyGaussSchwartzReal
  map_add' P Q := by ext x; simp [polyGaussSchwartzReal_apply, add_mul]
  map_smul' c P := by ext x; simp [polyGaussSchwartzReal_apply, mul_assoc]

theorem polynomialGaussianParameter_injective : Function.Injective polynomialGaussianParameter := by
  intro P Q h
  apply Polynomial.funext
  intro x
  have he := congrArg (fun f : SchwartzMap ℝ ℝ => f x) h
  exact mul_right_cancel₀ (gaussReal_pos x).ne' he

/-- The smooth symmetry parameters are not a finite-dimensional vector space. -/
theorem schwartzParameters_infiniteDimensional : ¬ Module.Finite ℝ (SchwartzMap ℝ ℝ) := by
  intro h
  letI := h
  exact Polynomial.not_finite (Module.Finite.of_injective polynomialGaussianParameter
    polynomialGaussianParameter_injective)

omit [Fintype ι] in
/-- Distinct polynomial-Gaussian profiles give distinct smooth centralizing maps. -/
theorem polynomialGaussian_symmetries_injective (i : ι) :
    Function.Injective (fun P => schwartzPeriodTranslation i (polynomialGaussianParameter P)) :=
  (schwartzPeriodTranslation_injective i).comp polynomialGaussianParameter_injective

#print axioms schwartzPeriodTranslation_contDiff
#print axioms schwartzPeriodTranslation_symm_contDiff
#print axioms schwartzPeriodTranslation_injective
#print axioms schwartzPeriodAction_injective
#print axioms schwartzPeriodFlow_contDiff
#print axioms hasDerivAt_schwartzPeriodFlow
#print axioms polynomialGaussian_symmetries_injective
#print axioms schwartzParameters_infiniteDimensional
end GaloisForLFunctions.HTGeometry
