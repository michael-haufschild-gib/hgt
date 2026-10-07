import GaloisForLFunctions.HTGeometry.MeromorphicPlaneCubicRoot
import GaloisForLFunctions.RHTower.XiCubicStripNoLift
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot

/-!
# Irreducibility of the actual tilted Xi cubic

The entire no-lift theorem, combined with local removal of meromorphic poles,
excludes every root of the actual cubic over the global meromorphic plane.
The cubic is therefore irreducible and its root algebra has dimension three.
-/

open GaloisForLFunctions.HTGeometry
namespace RHTower

/-- The actual entire Xi function with a real exponential tilt. -/
noncomputable def xiCubicParameter (a : ℝ) (z : ℂ) : ℂ :=
  xi z * Complex.exp (-(a : ℂ) * z)

theorem xiCubicParameter_differentiable (a : ℝ) : Differentiable ℂ (xiCubicParameter a) := by
  unfold xiCubicParameter
  exact xi_differentiable.mul (by fun_prop)

/-- The actual tilted source as an element of the global meromorphic plane field. -/
noncomputable def xiCubicParameterElement (a : ℝ) : MeromorphicPlane :=
  ofMeromorphic (xiCubicParameter a)
    (fun z => ((xiCubicParameter_differentiable a).analyticAt z).meromorphicAt)

/-- The monic cubic whose roots would be cubic lifts of the actual source. -/
noncomputable def xiCubicPolynomial (a : ℝ) : Polynomial MeromorphicPlane :=
  (⟨1, 0, -3, -(2 + 4 * xiCubicParameterElement a)⟩ : Cubic MeromorphicPlane).toPoly

theorem xiCubicPolynomial_monic (a : ℝ) : (xiCubicPolynomial a).Monic :=
  Cubic.monic_of_a_eq_one rfl

theorem xiCubicPolynomial_natDegree (a : ℝ) : (xiCubicPolynomial a).natDegree = 3 :=
  Cubic.natDegree_of_a_ne_zero one_ne_zero

/-- No element of the actual global meromorphic field is a root of this cubic. -/
theorem xiCubicPolynomial_not_isRoot (a : ℝ) (ha : 0 ≤ a) (x : MeromorphicPlane) :
    ¬ Polynomial.IsRoot (xiCubicPolynomial a) x := by
  intro hx
  have hx' : x ^ 3 - 3 * x - (2 + 4 * xiCubicParameterElement a) = 0 := by
    simpa [Polynomial.IsRoot, xiCubicPolynomial, Cubic.toPoly, sub_eq_add_neg] using hx
  have hd : Differentiable ℂ (fun z => (4 : ℂ) * xiCubicParameter a z) :=
    (xiCubicParameter_differentiable a).const_mul 4
  have hr : ((x + 1) - 3) * (x + 1) ^ 2 =
      ofMeromorphic (fun z => (4 : ℂ) * xiCubicParameter a z)
        (fun z => (hd.analyticAt z).meromorphicAt) := by
    calc
      _ = 4 * xiCubicParameterElement a := by linear_combination hx'
      _ = _ := rfl
  obtain ⟨h, hh, hrel⟩ := entire_cubic_factor_of_plane hd (x + 1) hr
  apply no_entire_xi_cubic_lift a ha
  refine ⟨fun z => h z - 1, by fun_prop, fun z => ?_⟩
  change ((h z - 1) ^ 3 - 3 * (h z - 1) - 2) / 4 = xiCubicParameter a z
  linear_combination (1 / 4 : ℂ) * hrel z

/-- The actual source cubic is irreducible over the global meromorphic plane field. -/
theorem xiCubicPolynomial_irreducible (a : ℝ) (ha : 0 ≤ a) :
    Irreducible (xiCubicPolynomial a) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [xiCubicPolynomial_natDegree]
    simp
  · exact xiCubicPolynomial_not_isRoot a ha

/-- The algebra obtained by adjoining a source-cubic root has dimension three. -/
theorem xiCubicPolynomial_adjoinRoot_finrank (a : ℝ) :
    Module.finrank MeromorphicPlane (AdjoinRoot (xiCubicPolynomial a)) = 3 := by
  have h := (AdjoinRoot.powerBasis (xiCubicPolynomial_monic a).ne_zero).finrank
  simpa only [AdjoinRoot.powerBasis_dim, xiCubicPolynomial_natDegree] using h

end RHTower
