import GaloisForLFunctions.RHTower.XiCubicMeromorphic
import GaloisForLFunctions.HTGeometry.EntireOddDivisorSquareClass

/-!
# The actual Xi cubic has nonsquare discriminant

Its discriminant is `-432 * delta * (delta + 1)`. At an actual odd Xi zero,
the exponential mark and `delta + 1` are units. The existing odd-divisor
square-class obstruction therefore proves nonsquareness over the actual
global meromorphic plane field, without any simplicity hypothesis.
-/

open GaloisForLFunctions.HTGeometry Filter Topology
namespace RHTower

/-- The discriminant of the actual source cubic. -/
noncomputable def xiCubicDiscriminant (a : ℝ) : MeromorphicPlane :=
  (⟨1, 0, -3, -(2 + 4 * xiCubicParameterElement a)⟩ : Cubic MeromorphicPlane).discr

theorem xiCubicDiscriminant_eq (a : ℝ) :
    xiCubicDiscriminant a =
      -432 * xiCubicParameterElement a * (xiCubicParameterElement a + 1) := by
  simp only [xiCubicDiscriminant, Cubic.discr]
  ring

/-- An actual odd Xi zero makes the cubic discriminant nonsquare, for every real tilt. -/
theorem xiCubicDiscriminant_not_isSquare (a : ℝ) : ¬ IsSquare (xiCubicDiscriminant a) := by
  obtain ⟨z, hz, ho⟩ := exists_odd_order_zero_xi
  let g : ℂ → ℂ := fun w => -432 * Complex.exp (-(a : ℂ) * w) * (xiCubicParameter a w + 1)
  have hg : Differentiable ℂ g := by
    dsimp [g]
    exact ((by fun_prop : Differentiable ℂ (fun w : ℂ =>
      (-432 : ℂ) * Complex.exp (-(a : ℂ) * w)))).mul
        ((xiCubicParameter_differentiable a).add_const 1)
  have hg0 : g z ≠ 0 := by
    simp only [g, xiCubicParameter, hz, zero_mul, zero_add, mul_one]
    exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  have hns := not_isSquare_plane_mul_of_odd_order xi_differentiable hg ho hg0
  have he : xiCubicDiscriminant a =
      ofMeromorphic xi (fun z => (xi_differentiable.analyticAt z).meromorphicAt) *
      ofMeromorphic g (fun z => (hg.analyticAt z).meromorphicAt) := by
    rw [xiCubicDiscriminant_eq]
    apply MeromorphicPlane.germ_injective
    change ((fun w : ℂ => -432 * xiCubicParameter a w * (xiCubicParameter a w + 1)) :
      Germ planeCodiscrete ℂ) = ((fun w => xi w * g w) : Germ planeCodiscrete ℂ)
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun w => by dsimp [g, xiCubicParameter]; ring)
  rwa [he]

end RHTower
