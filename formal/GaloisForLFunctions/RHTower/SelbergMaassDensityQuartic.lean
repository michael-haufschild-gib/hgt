import GaloisForLFunctions.RHTower.SelbergMaassTraceRadial

/-!
# Exact quartic density equation for the actual Maass source

The full modular trace density of a congruence Maass eigenform has an exact
square-density equation.  The two terms retained after squaring are the literal
scalar density-gradient square and the angular residual of the finite deck family.
This is a pointwise identity.  It does not supply the global coercive inequality
needed for Selberg's quarter bound.
-/

open Complex Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassDensityQuartic
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassTraceBoundary
  SelbergMaassTraceRadial
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Squaring the literal finite deck density retains its two real directional current squares. -/
theorem density_sq_realLaplacian (z : ℍ) :
    realLaplacian (fun w => (density N f (ofComplex w)) ^ 2) (z : ℂ) =
      2 * density N f z * realLaplacian (density N f ∘ ofComplex) (z : ℂ) +
        2 * (current N f 1 z ^ 2 + current N f Complex.I z ^ 2) := by
  have hF := (density_contDiffOn N f).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  change realLaplacian (fun w => ((density N f ∘ ofComplex) w) ^ 2) (z : ℂ) = _
  rw [realLaplacian_sq hF]
  unfold current dir
  simp only [Function.comp_apply, ofComplex_apply]

/-- The hyperbolic square-density equation retains the density-gradient and angular source terms. -/
theorem density_sq_hyperbolic_laplacian (z : ℍ) :
    -z.im ^ 2 * realLaplacian (fun w => (density N f (ofComplex w)) ^ 2) (z : ℂ) =
      4 * lam * density N f z ^ 2 -
        3 * z.im ^ 2 * (current N f 1 z ^ 2 + current N f Complex.I z ^ 2) -
          4 * z.im ^ 2 * density N f z * angularEnergy N f z := by
  rw [density_sq_realLaplacian, trace_laplacian]
  calc
    _ = 4 * lam * density N f z ^ 2 -
        4 * z.im ^ 2 * (density N f z * gradientDensity N f (z : ℂ)) -
          2 * z.im ^ 2 * (current N f 1 z ^ 2 + current N f Complex.I z ^ 2) := by
      field_simp [z.im_pos.ne']
      ring
    _ = _ := by
      rw [density_mul_gradientDensity]
      ring

end
end GaloisForLFunctions.RHTower.SelbergMaassDensityQuartic
