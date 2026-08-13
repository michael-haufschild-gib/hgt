import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Bounded logarithmic prime--infinity shear

A rank-one port into a diagonal operator domain splits by an explicit bounded upper shear whenever
the port vector has an admitted inverse image.  Taking that inverse image through the bounded
coordinate multiplier `1 / log p` is the solid-sequence-space specialization.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k X D : Type*}
variable [NontriviallyNormedField k]
variable [NormedAddCommGroup X] [NormedSpace k X]
variable [NormedAddCommGroup D] [NormedSpace k D]

/-- Bounded upper shear `(x,c) |-> (x + c h,c)`. -/
def boundedUpperShear (h : X) : X × k →L[k] X × k :=
  ((ContinuousLinearMap.fst k X k) +
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.snd k X k) h)).prod
    (ContinuousLinearMap.snd k X k)

@[simp]
theorem boundedUpperShear_apply (h : X) (z : X × k) :
    boundedUpperShear h z = (z.1 + z.2 • h, z.2) := by
  rfl

/-- Upper shears with opposite parameters are bounded two-sided inverses. -/
theorem boundedUpperShear_neg_comp (h : X) :
    (boundedUpperShear (-h)).comp (boundedUpperShear h) =
      ContinuousLinearMap.id k (X × k) := by
  ext z <;> simp [boundedUpperShear]

theorem boundedUpperShear_comp_neg (h : X) :
    (boundedUpperShear h).comp (boundedUpperShear (-h)) =
      ContinuousLinearMap.id k (X × k) := by
  simpa only [neg_neg] using boundedUpperShear_neg_comp (-h)

/-- Rank-one extension of an operator on its normed domain.  The norm on `D` may be the graph norm
of an unbounded ambient operator, so this is the bounded map between graph domain and ambient
space used by the paper theorem. -/
def rankOnePortOperator (Lambda : D →L[k] X) (b : X) : D × k →L[k] X × k :=
  ((Lambda.comp (ContinuousLinearMap.fst k D k)) +
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.snd k D k) b)).prod 0

@[simp]
theorem rankOnePortOperator_apply (Lambda : D →L[k] X) (b : X) (z : D × k) :
    rankOnePortOperator Lambda b z = (Lambda z.1 + z.2 • b, 0) := by
  rfl

/-- Exact bounded similarity.  `h` belongs to the graph domain and solves `Lambda h = -b`; both
domain and ambient shears are bounded, preserve the domain by construction, and remove the port. -/
theorem rankOnePortOperator_boundedly_similar_to_split
    (incl : D →L[k] X) (Lambda : D →L[k] X) (b : X) (h : D)
    (hh : Lambda h = -b) (z : D × k) :
    boundedUpperShear (-(incl h))
        (rankOnePortOperator Lambda b (boundedUpperShear h z)) =
      rankOnePortOperator Lambda 0 z := by
  ext <;> simp [hh, add_assoc]

/-- A bounded inverse multiplier from ambient sequence space into the logarithmic graph domain. -/
structure BoundedLogarithmicDomain where
  inclusion : D →L[k] X
  logarithmicOperator : D →L[k] X
  inverseMultiplier : X →L[k] D
  rightInverse : Function.RightInverse inverseMultiplier logarithmicOperator

/-- Unconditional packaged form: every bounded rank-one port splits when the logarithmic domain
carries its bounded inverse multiplier. -/
theorem boundedLogarithmicPrimeInfinityCoupling_splits
    (L : BoundedLogarithmicDomain (k := k) (X := X) (D := D)) (b : X) (z : D × k) :
    boundedUpperShear (-(L.inclusion (-L.inverseMultiplier b)))
        (rankOnePortOperator L.logarithmicOperator b
          (boundedUpperShear (-L.inverseMultiplier b) z)) =
      rankOnePortOperator L.logarithmicOperator 0 z := by
  apply rankOnePortOperator_boundedly_similar_to_split
  simp [L.rightInverse b]

end

end GaloisForLFunctions.HTGeometry
