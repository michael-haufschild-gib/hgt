import Mathlib

/-!
# Reflected removable divided differences

The first divided difference absorbs the two signs in an anti-reflection: one from the
numerator and one from reflection of the affine denominator.  The identity remains exact on
the diagonal because `dslope` uses the derivative there.  Applied to a two-variable numerator,
this says that an anti-invariant numerator has a reflection-invariant removable diagonal
quotient.

This is source-independent bridge infrastructure.  It is an elementary law of divided
differences, not a new hypertranscendence theorem.
-/

open Complex

namespace HTGeometry

noncomputable section

/-- **Reflected divided-difference law.**  Simultaneous negation of the argument and anchor,
together with negation of the reflected function, leaves the removable divided difference
unchanged.  No differentiability hypothesis is needed: at the diagonal the two chain-rule signs
cancel, while away from it the two quotient signs cancel algebraically. -/
theorem dslope_neg_comp_neg (T : ℂ → ℂ) (a z : ℂ) :
    dslope (fun w => -T (-w)) (-a) z = dslope T a (-z) := by
  by_cases hz : z = -a
  · subst z
    rw [dslope_same, neg_neg, dslope_same]
    have hcomp := iteratedDeriv_comp_neg 1 T (-a)
    have hneg := iteratedDeriv_neg 1 (fun w : ℂ => T (-w)) (-a)
    rw [iteratedDeriv_one, iteratedDeriv_one] at hcomp
    rw [iteratedDeriv_one, iteratedDeriv_one] at hneg
    have hfun : (fun w : ℂ => -T (-w)) = -(fun w : ℂ => T (-w)) := rfl
    rw [hfun, hneg, hcomp]
    ring
  · have hnz : -z ≠ a := by
      intro h
      apply hz
      simpa using congrArg Neg.neg h
    rw [dslope_of_ne _ hz, dslope_of_ne _ hnz,
      slope_def_module, slope_def_module]
    simp only [neg_neg, smul_eq_mul]
    have hden : -z - a = -(z - -a) := by ring
    have hnum : -T (-z) - -T a = -(T (-z) - T a) := by ring
    rw [hden, hnum, inv_neg]
    ring

/-- The removable diagonal quotient of a two-variable numerator. -/
def diagonalDslopeKernel (K : ℂ → ℂ → ℂ) (z v : ℂ) : ℂ :=
  dslope (K z) z v

/-- **Anti-reflection quotient law.**  A two-variable numerator that changes sign under
simultaneous centered reflection has a removable diagonal quotient that is exactly reflection
invariant, including at `v = z`. -/
theorem diagonalDslopeKernel_neg_neg_of_antiInvariant
    (K : ℂ → ℂ → ℂ)
    (hreflect : ∀ z v, K (-z) (-v) = -K z v) (z v : ℂ) :
    diagonalDslopeKernel K (-z) (-v) = diagonalDslopeKernel K z v := by
  have hfun : K (-z) = fun w => -K z (-w) := by
    funext w
    simpa using hreflect z (-w)
  rw [diagonalDslopeKernel, diagonalDslopeKernel, hfun]
  simpa using dslope_neg_comp_neg (K z) z (-v)

end

end HTGeometry
