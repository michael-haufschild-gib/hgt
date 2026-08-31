import GaloisForLFunctions.HTGeometry.RatFuncCompositionDegree

/-!
# Rational functions fixed by substitution

Substitution by a rational map multiplies the degree of a rational function by the degree of the
map.  So a rational function fixed by substituting a map of degree at least two has degree zero, and
a rational function of degree zero is a constant.

This is the sharpening the degenerate branch of the tower alternative needs: the branch produces a
nonzero base element fixed by the base shift, and for a map of degree at least two that element can
only be a constant.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- A rational function of degree zero is a constant. -/
theorem eq_C_of_ratFuncDegree_eq_zero {a : RatFunc K} (h : ratFuncDegree a = 0) :
    ∃ c : K, a = RatFunc.C c := by
  rw [RatFunc.eq_C_iff]
  exact Nat.max_eq_zero_iff.mp h

/-- **A rational function fixed by substituting a map of degree at least two is constant.** -/
theorem eq_C_of_substitution_fixed {R : RatFunc K}
    (hR : ¬ ∃ c : K, R = RatFunc.C c) (hdeg : 2 ≤ ratFuncDegree R)
    {a : RatFunc K} (hfix : ratFuncSubstitutionAlgHom R hR a = a) :
    ∃ c : K, a = RatFunc.C c := by
  refine eq_C_of_ratFuncDegree_eq_zero ?_
  have h := ratFuncDegree_substitution R a hR
  rw [hfix] at h
  by_contra hne
  have hpos : 0 < ratFuncDegree a := Nat.pos_of_ne_zero hne
  have hle : ratFuncDegree a * 2 ≤ ratFuncDegree a * ratFuncDegree R :=
    Nat.mul_le_mul_left _ hdeg
  omega

end GaloisForLFunctions.HTGeometry
