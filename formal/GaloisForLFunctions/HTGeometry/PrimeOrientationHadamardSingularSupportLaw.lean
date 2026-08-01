import GaloisForLFunctions.HTGeometry.TailHadamardReducedProduct
import GaloisForLFunctions.HTGeometry.ReflectionOrientationSingularSupportLaw

/-!
# Positive prime orientation is the regular symmetric locus

In the Hadamard algebra of real prime-coefficient tails modulo finite support, a Boolean
orientation is positive exactly when its reflection-symmetric channel is regular, and exactly
when that channel is invertible.  Every non-positive orientation supplies its own explicit
nonzero annihilator.

This is the prime-source realization of the abstract reflection-orientation support law.  The
Hadamard product here is coefficientwise; no ordinary Dirichlet-series multiplication is used.
-/

namespace HTGeometry

noncomputable section

/-- The constant class `2` is a unit in every real tail Hadamard reduced product. -/
theorem isUnit_two_tailHadamardReducedProduct (P : Type*) :
    IsUnit (2 : TailHadamardReducedProduct P) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨tailHadamardClass (fun _ : P => (1 / 2 : ℝ)), ?_⟩
  change
    tailHadamardClass (fun _ : P => (2 : ℝ)) *
        tailHadamardClass (fun _ : P => (1 / 2 : ℝ)) =
      tailHadamardClass (fun _ : P => (1 : ℝ))
  rw [← tailHadamardClass_mul]
  exact congrArg tailHadamardClass (by
    funext p
    norm_num)

/-- The constant class `2` is therefore regular. -/
theorem isRegular_two_tailHadamardReducedProduct (P : Type*) :
    IsRegular (2 : TailHadamardReducedProduct P) :=
  (isUnit_two_tailHadamardReducedProduct P).isRegular

/-- **Positive--regular classification.**  A Boolean prime orientation has a positive tail
representative exactly when its symmetric channel is a non-zero-divisor. -/
theorem primeOrientationHadamardTail_positive_iff_hyperbolic_regular
    {P : Type*} (epsilon : P → Bool) :
    TailHadamardPositive (primeOrientationHadamardTail epsilon) ↔
      IsRegular (1 + primeOrientationHadamardTail epsilon) := by
  constructor
  · intro hpositive
    have heq :=
      (primeOrientationHadamardTail_positive_iff_eq_one epsilon).mp hpositive
    rw [heq, one_add_one_eq_two]
    exact isRegular_two_tailHadamardReducedProduct P
  · intro hregular
    apply (primeOrientationHadamardTail_positive_iff_eq_one epsilon).mpr
    exact
      GaloisForLFunctions.HTGeometry.reflectionOrientation_eq_one_of_hyperbolic_regular
        (primeOrientationHadamardTail epsilon)
        (primeOrientationHadamardTail_sq epsilon) hregular

/-- **Positive--unit classification.**  On Boolean prime tails, regularity of the symmetric
channel automatically upgrades to invertibility because both are equivalent to positivity. -/
theorem primeOrientationHadamardTail_positive_iff_hyperbolic_isUnit
    {P : Type*} (epsilon : P → Bool) :
    TailHadamardPositive (primeOrientationHadamardTail epsilon) ↔
      IsUnit (1 + primeOrientationHadamardTail epsilon) := by
  constructor
  · intro hpositive
    have heq :=
      (primeOrientationHadamardTail_positive_iff_eq_one epsilon).mp hpositive
    rw [heq, one_add_one_eq_two]
    exact isUnit_two_tailHadamardReducedProduct P
  · intro hunit
    exact
      (primeOrientationHadamardTail_positive_iff_hyperbolic_regular epsilon).mpr
        hunit.isRegular

/-- Every non-positive Boolean prime orientation is supported by an explicit nonzero annihilator
of its symmetric channel. -/
theorem primeOrientationHadamardTail_nontrivial_has_hyperbolic_annihilator
    {P : Type*} (epsilon : P → Bool)
    (hne : primeOrientationHadamardTail epsilon ≠ 1) :
    1 - primeOrientationHadamardTail epsilon ≠ 0 ∧
      (1 - primeOrientationHadamardTail epsilon) *
          (1 + primeOrientationHadamardTail epsilon) = 0 := by
  constructor
  · exact sub_ne_zero.mpr (Ne.symm hne)
  · exact
      GaloisForLFunctions.HTGeometry.reflectionOrientation_mul_hyperbolic_eq_zero
        (primeOrientationHadamardTail epsilon)
        (primeOrientationHadamardTail_sq epsilon)

end

end HTGeometry
