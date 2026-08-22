import GaloisForLFunctions.HTGeometry.Octonion.Coordinate
import GaloisForLFunctions.HTGeometry.Octonion.SliceResolvent

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- Extension of a map on the real part of `𝕆` using the fixed standard real basis.
This is the one-dimensional specialization of the paper's extension map. -/
def extendFromRealPart (f : ℝ → RealOctonion) : RealOctonion → RealOctonion := fun x =>
  ∑ i, f (standardBasis.repr x i) * standardBasis i

/-- Extending scalar left multiplication from the real part recovers left multiplication
on all octonions. -/
theorem extendFromRealPart_eq_leftAction
    (f : ℝ → RealOctonion) (a : RealOctonion)
    (hf : ∀ r : ℝ, f r = a * scalarEmbed r) :
    extendFromRealPart f = leftAction a := by
  funext x
  unfold extendFromRealPart leftAction
  calc
    (∑ i, f (standardBasis.repr x i) * standardBasis i) =
      ∑ i, (a * scalarEmbed (standardBasis.repr x i)) * standardBasis i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hf]
    _ = ∑ i, a * (scalarEmbed (standardBasis.repr x i) * standardBasis i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_scalarEmbed_associates a (standardBasis.repr x i) (standardBasis i)
    _ = a * ∑ i, scalarEmbed (standardBasis.repr x i) * standardBasis i := by
      rw [Finset.mul_sum]
    _ = a * x := by
      congr 1
      simpa only [scalarEmbed_mul] using standardBasis.sum_repr x

/-- The real-linear equivalence `R_s - L_q` when the quadratic denominator is nonzero. -/
def sylvesterDifferenceEquiv (s q : RealOctonion)
    (hquad : quadratic s q ≠ 0) : RealOctonion ≃ₗ[ℝ] RealOctonion :=
  LinearEquiv.ofBijective (sylvesterDifferenceLinear s q) <| by
    apply (sylvesterDifferenceLinear_bijective_iff_not_mem_conjugacySphere s q).mpr
    intro hmem
    exact hquad ((mem_conjugacySphere_iff_quadratic_eq_zero s q).mp hmem)

/-- The right regular inverse of `R_s - L_q` in the one-dimensional octonion module,
defined by extension of its real-part inverse. -/
def rightRegularInverse (s q : RealOctonion)
    (hquad : quadratic s q ≠ 0) : RealOctonion → RealOctonion :=
  extendFromRealPart (fun r =>
    (sylvesterDifferenceEquiv s q hquad).symm (scalarEmbed r))

/-- Paper equation (8.9): the right regular inverse of `R_s - L_q` is the displayed
left-multiplication operator. -/
theorem rightRegularInverse_eq_leftAction_formula
    (s q : RealOctonion) (hquad : quadratic s q ≠ 0) :
    rightRegularInverse s q hquad =
      leftAction (inverse (quadratic s q) * (star s - q)) := by
  apply extendFromRealPart_eq_leftAction
  intro r
  let e := sylvesterDifferenceEquiv s q hquad
  apply e.injective
  calc
    e (e.symm (scalarEmbed r)) = scalarEmbed r := e.apply_symm_apply _
    _ = resolventDifference s q
        ((inverse (quadratic s q) * (star s - q)) * scalarEmbed r) :=
      (resolventDifference_regularInverse_apply_scalar s q r hquad).symm
    _ = e ((inverse (quadratic s q) * (star s - q)) * scalarEmbed r) := by
      rfl

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
