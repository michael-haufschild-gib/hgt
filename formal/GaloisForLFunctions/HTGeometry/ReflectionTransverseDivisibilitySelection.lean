import GaloisForLFunctions.HTGeometry.ReflectedOrbitCharge
import GaloisForLFunctions.HTGeometry.ConstitutiveDivisibleFormationSelection

/-!
# Reflection-transverse divisibility selection

This file isolates the discrete algebraic survivor of the equivariant-completion
proposal.  For an integral finitely supported charge and a reflection, split the
charge into its fixed-label part and its transverse remainder.  If the remainder
admits integral formation divisors of unbounded depth in the *original charge
lattice*, then the remainder vanishes.  Consequently every charged label is fixed.

Unlike an untwisted root-tower argument, this does not annihilate fixed-point
multiplicity.  Unlike divisibility after embedding into an auxiliary regular
representation, the divisor witnesses live in the original `Finsupp` lattice.

This module does not construct the formation divisors from Euler/Gamma source
operations and does not identify the charge with the divisor of Xi.  Those are the
source and landing obligations of the proposed RH route.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {ι : Type u}

/-- Part of an integral charge supported on labels fixed by `r`. -/
noncomputable def reflectionFixedIntegralPart
    (r : ι ≃ ι) (q : ι →₀ ℤ) : ι →₀ ℤ := by
  classical
  exact Finsupp.filter (fun i => r i = i) q

/-- Remainder after removing the fixed-label part of an integral charge. -/
def reflectionTransverseIntegralPart
    (r : ι ≃ ι) (q : ι →₀ ℤ) : ι →₀ ℤ :=
  q - reflectionFixedIntegralPart r q

/-- The charge has integral divisors at arbitrarily large formation depths. -/
def HasUnboundedIntegralFormationDivisors (q : ι →₀ ℤ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ d : ι →₀ ℤ, n • d = q

theorem reflectionFixedIntegralPart_apply_of_fixed
    (r : ι ≃ ι) (q : ι →₀ ℤ) {i : ι} (hi : r i = i) :
    reflectionFixedIntegralPart r q i = q i := by
  classical
  simp [reflectionFixedIntegralPart, hi]

theorem reflectionFixedIntegralPart_apply_of_not_fixed
    (r : ι ≃ ι) (q : ι →₀ ℤ) {i : ι} (hi : r i ≠ i) :
    reflectionFixedIntegralPart r q i = 0 := by
  classical
  simp [reflectionFixedIntegralPart, hi]

/-- Fixed-label extraction is a projection. -/
theorem reflectionFixedIntegralPart_idempotent
    (r : ι ≃ ι) (q : ι →₀ ℤ) :
    reflectionFixedIntegralPart r (reflectionFixedIntegralPart r q) =
      reflectionFixedIntegralPart r q := by
  classical
  ext i
  by_cases hi : r i = i <;>
    simp [reflectionFixedIntegralPart, hi]

/-- Fixed-label extraction annihilates the complementary transverse part. -/
theorem reflectionFixedIntegralPart_transverse_eq_zero
    (r : ι ≃ ι) (q : ι →₀ ℤ) :
    reflectionFixedIntegralPart r (reflectionTransverseIntegralPart r q) = 0 := by
  classical
  ext i
  by_cases hi : r i = i <;>
    simp [reflectionFixedIntegralPart, reflectionTransverseIntegralPart, hi]

/-- Transverse extraction is the complementary projection. -/
theorem reflectionTransverseIntegralPart_idempotent
    (r : ι ≃ ι) (q : ι →₀ ℤ) :
    reflectionTransverseIntegralPart r (reflectionTransverseIntegralPart r q) =
      reflectionTransverseIntegralPart r q := by
  classical
  ext i
  by_cases hi : r i = i <;>
    simp [reflectionFixedIntegralPart, reflectionTransverseIntegralPart, hi]

/-- Fixed extraction retains a fixed point charge with its full integer multiplicity. -/
theorem reflectionFixedIntegralPart_single_of_fixed
    [DecidableEq ι] (r : ι ≃ ι) {i : ι} (m : ℤ) (hi : r i = i) :
    reflectionFixedIntegralPart r (Finsupp.single i m) = Finsupp.single i m := by
  classical
  ext j
  by_cases hj : r j = j
  · simp [reflectionFixedIntegralPart, hj]
  · have hji : j ≠ i := by
      intro h
      subst j
      exact hj hi
    simp [reflectionFixedIntegralPart, hj, hji]

/--
Algebraic geometric-fixed shadow: a charge-conjugate pair on a free reflection orbit has no
fixed-label component.  This statement does not construct genuine equivariant geometric fixed
points; it records their coefficient-level support behavior.
-/
theorem reflectionFixedIntegralPart_reflectionAntiInvariantPair_eq_zero_of_free
    [DecidableEq ι] (r : ι ≃ ι) (hr : Function.Involutive r)
    {i : ι} (m : ℤ) (hi : r i ≠ i) :
    reflectionFixedIntegralPart r
      (GaloisForLFunctions.reflectionAntiInvariantPair r i m) = 0 := by
  classical
  ext j
  by_cases hj : r j = j
  · have hji : j ≠ i := by
      intro h
      subst j
      exact hi hj
    have hjri : j ≠ r i := by
      intro h
      subst j
      have hir : i = r i := (hr i).symm.trans hj
      exact hi hir.symm
    simp [reflectionFixedIntegralPart,
      GaloisForLFunctions.reflectionAntiInvariantPair, hj, hji, hjri]
  · simp [reflectionFixedIntegralPart, hj]

@[simp]
theorem reflectionTransverseIntegralPart_apply_of_fixed
    (r : ι ≃ ι) (q : ι →₀ ℤ) {i : ι} (hi : r i = i) :
    reflectionTransverseIntegralPart r q i = 0 := by
  classical
  simp [reflectionTransverseIntegralPart, reflectionFixedIntegralPart, hi]

theorem reflectionFixedIntegralPart_add_transverse
    (r : ι ≃ ι) (q : ι →₀ ℤ) :
    reflectionFixedIntegralPart r q + reflectionTransverseIntegralPart r q = q := by
  simp [reflectionTransverseIntegralPart]

/-- Discreteness law: an integral finite charge with unbounded integral divisors is zero. -/
theorem integralCharge_eq_zero_of_unboundedFormationDivisors
    (q : ι →₀ ℤ) (h : HasUnboundedIntegralFormationDivisors q) : q = 0 := by
  ext i
  apply int_eq_zero_of_unbounded_natCast_dvd
  intro N
  obtain ⟨n, hn, d, hd⟩ := h N
  refine ⟨n, hn, ⟨d i, ?_⟩⟩
  have hi := congrArg (fun x : ι →₀ ℤ => x i) hd
  simpa [nsmul_eq_mul] using hi.symm

/-- Vanishing transverse charge says that every label in the original support is fixed. -/
theorem support_fixed_of_reflectionTransverseIntegralPart_eq_zero
    (r : ι ≃ ι) (q : ι →₀ ℤ)
    (hzero : reflectionTransverseIntegralPart r q = 0) :
    ∀ i ∈ q.support, r i = i := by
  classical
  intro i hi
  by_contra hri
  have hz := congrArg (fun x : ι →₀ ℤ => x i) hzero
  simp [reflectionTransverseIntegralPart, reflectionFixedIntegralPart, hri] at hz
  exact (Finsupp.mem_support_iff.mp hi) hz

theorem reflectionTransverseIntegralPart_eq_zero_of_unboundedFormationDivisors
    (r : ι ≃ ι) (q : ι →₀ ℤ)
    (hdiv : HasUnboundedIntegralFormationDivisors
      (reflectionTransverseIntegralPart r q)) :
    reflectionTransverseIntegralPart r q = 0 :=
  integralCharge_eq_zero_of_unboundedFormationDivisors _ hdiv

/--
Core selection theorem: unbounded divisibility of only the transverse charge
confines the full integral charge to reflection-fixed labels without erasing their
coefficients.
-/
theorem support_fixed_of_reflectionTransverse_unboundedFormationDivisors
    (r : ι ≃ ι) (q : ι →₀ ℤ)
    (hdiv : HasUnboundedIntegralFormationDivisors
      (reflectionTransverseIntegralPart r q)) :
    ∀ i ∈ q.support, r i = i :=
  support_fixed_of_reflectionTransverseIntegralPart_eq_zero r q
    (reflectionTransverseIntegralPart_eq_zero_of_unboundedFormationDivisors r q hdiv)

/-- Point-charge form of the transverse selection theorem. -/
theorem fixed_of_single_reflectionTransverse_unboundedFormationDivisors
    [DecidableEq ι] (r : ι ≃ ι) {i : ι} {m : ℤ} (hm : m ≠ 0)
    (hdiv : HasUnboundedIntegralFormationDivisors
      (reflectionTransverseIntegralPart r (Finsupp.single i m))) :
    r i = i := by
  apply support_fixed_of_reflectionTransverse_unboundedFormationDivisors
    r (Finsupp.single i m) hdiv i
  simp [hm]

end

end GaloisForLFunctions.HTGeometry
