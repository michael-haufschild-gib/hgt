import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Polynomial saturation of simple-spectrum ray clocks

This file isolates the positive algebraic law behind the prime-clock quotient.  For a clock with
simple spectrum, applying a nonzero polynomial in the clock preserves finite-ray locality in both
directions.  Equivalently, quotienting profiles by finite-ray profiles produces a torsion-free
polynomial-clock module.

The theorem is first proved for an arbitrary ray map and an injective complex clock, then
specialized to the prime-power clock `(p,r) |-> r log p`.  No convergence or analytic realization
is used in this leaf.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- The ray directions on which a scalar profile is nonzero. -/
def rayActivity {Omega P : Type*} (ray : Omega -> P) (a : Omega -> ℂ) : Set P :=
  {p | Exists fun omega => ray omega = p ∧ a omega ≠ 0}

/-- A profile is local when only finitely many ray directions are active. -/
def RayLocal {Omega P : Type*} (ray : Omega -> P) (a : Omega -> ℂ) : Prop :=
  (rayActivity ray a).Finite

/-- Pointwise action of a polynomial in a diagonal clock. -/
def polynomialClockApply {Omega : Type*}
    (weight : Omega -> ℂ) (P : ℂ[X]) (a : Omega -> ℂ) : Omega -> ℂ :=
  fun omega => P.eval (weight omega) * a omega

/-- A polynomial clock cannot create a new active ray. -/
theorem rayActivity_polynomialClockApply_subset
    {Omega P : Type*} (ray : Omega -> P) (weight : Omega -> ℂ)
    (Q : ℂ[X]) (a : Omega -> ℂ) :
    rayActivity ray (polynomialClockApply weight Q a) ⊆ rayActivity ray a := by
  rintro p ⟨omega, homega, hne⟩
  refine ⟨omega, homega, ?_⟩
  exact fun ha => hne (by simp [polynomialClockApply, ha])

/-- The indices at which a nonzero polynomial kills an injective clock form a finite set. -/
theorem finite_polynomialClock_zeroSet
    {Omega : Type*} (weight : Omega -> ℂ) (hweight : Function.Injective weight)
    (P : ℂ[X]) (hP : P ≠ 0) :
    {omega | P.eval (weight omega) = 0}.Finite := by
  have hroots : {z : ℂ | P.eval z = 0}.Finite :=
    Polynomial.finite_setOf_isRoot hP
  exact hroots.preimage hweight.injOn

/-- **Polynomial clock-saturation law.**  For a simple-spectrum diagonal clock, every nonzero
polynomial in the clock preserves finite-ray locality exactly.  The reverse implication is the
substantive direction: a polynomial has only finitely many clock roots, so it can erase only
finitely many additional rays. -/
theorem rayLocal_polynomialClockApply_iff
    {Omega P : Type*} (ray : Omega -> P) (weight : Omega -> ℂ)
    (hweight : Function.Injective weight) (Q : ℂ[X]) (hQ : Q ≠ 0)
    (a : Omega -> ℂ) :
    RayLocal ray (polynomialClockApply weight Q a) ↔ RayLocal ray a := by
  constructor
  · intro hlocal
    let roots : Set Omega := {omega | Q.eval (weight omega) = 0}
    have hroots : roots.Finite := by
      simpa only [roots] using finite_polynomialClock_zeroSet weight hweight Q hQ
    have hrootRays : (ray '' roots).Finite := hroots.image ray
    apply (hrootRays.union hlocal).subset
    rintro p ⟨omega, homega, ha⟩
    by_cases hroot : Q.eval (weight omega) = 0
    · exact Set.mem_union_left _ ⟨omega, hroot, homega⟩
    · exact Set.mem_union_right _
        ⟨omega, homega, mul_ne_zero hroot ha⟩
  · intro hlocal
    exact hlocal.subset
      (rayActivity_polynomialClockApply_subset ray weight Q a)

/-- Finite-ray profiles form the local subspace killed by the ray quotient. -/
def rayLocalSubmodule {Omega P : Type*} (ray : Omega -> P) :
    Submodule ℂ (Omega -> ℂ) where
  carrier := {a | RayLocal ray a}
  zero_mem' := by
    have hzero : rayActivity ray (0 : Omega -> ℂ) = ∅ := by
      ext p
      simp [rayActivity]
    change (rayActivity ray (0 : Omega -> ℂ)).Finite
    rw [hzero]
    exact Set.finite_empty
  add_mem' := by
    intro a b ha hb
    apply (ha.union hb).subset
    rintro p ⟨omega, homega, hab⟩
    by_cases haomega : a omega = 0
    · apply Set.mem_union_right
      refine ⟨omega, homega, ?_⟩
      intro hbomega
      apply hab
      simp [haomega, hbomega]
    · exact Set.mem_union_left _ ⟨omega, homega, haomega⟩
  smul_mem' := by
    intro c a ha
    apply ha.subset
    rintro p ⟨omega, homega, hca⟩
    refine ⟨omega, homega, ?_⟩
    exact fun haomega => hca (by simp [haomega])

@[simp]
theorem mem_rayLocalSubmodule_iff
    {Omega P : Type*} (ray : Omega -> P) (a : Omega -> ℂ) :
    a ∈ rayLocalSubmodule ray ↔ RayLocal ray a :=
  Iff.rfl

/-- **Quotient torsion-freeness, representative form.**  A nonzero polynomial clock sends a
profile to zero modulo local rays exactly when the original profile was already zero modulo local
rays. -/
theorem rayQuotient_polynomialClock_eq_zero_iff
    {Omega P : Type*} (ray : Omega -> P) (weight : Omega -> ℂ)
    (hweight : Function.Injective weight) (Q : ℂ[X]) (hQ : Q ≠ 0)
    (a : Omega -> ℂ) :
    (rayLocalSubmodule ray).mkQ (polynomialClockApply weight Q a) = 0 ↔
      (rayLocalSubmodule ray).mkQ a = 0 := by
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_rayLocalSubmodule_iff]
  exact rayLocal_polynomialClockApply_iff ray weight hweight Q hQ a

/-- One positive prime-power coordinate.  The natural component records exponent minus one. -/
abbrev PrimePowerClockIndex := Nat.Primes × Nat

/-- Prime ray underlying a prime-power coordinate. -/
def primePowerClockRay (x : PrimePowerClockIndex) : Nat.Primes := x.1

/-- The unrotated prime-power logarithmic clock `(p,e) |-> (e+1) log p`. -/
def primePowerClockWeight (x : PrimePowerClockIndex) : ℂ :=
  (Real.log ((Nat.Primes.prodNatEquiv x : Nat) : ℝ) : ℂ)

/-- Unique factorization makes the complete prime-power logarithmic spectrum simple. -/
theorem primePowerClockWeight_injective : Function.Injective primePowerClockWeight := by
  intro x y hclock
  have hlog : Real.log ((Nat.Primes.prodNatEquiv x : Nat) : ℝ) =
      Real.log ((Nat.Primes.prodNatEquiv y : Nat) : ℝ) :=
    Complex.ofReal_injective hclock
  have hpowReal : ((Nat.Primes.prodNatEquiv x : Nat) : ℝ) =
      ((Nat.Primes.prodNatEquiv y : Nat) : ℝ) :=
    Real.strictMonoOn_log.injOn
      (Set.mem_Ioi.mpr (Nat.cast_pos.mpr (Nat.Primes.prodNatEquiv x).2.pos))
      (Set.mem_Ioi.mpr (Nat.cast_pos.mpr (Nat.Primes.prodNatEquiv y).2.pos)) hlog
  have hpow : (Nat.Primes.prodNatEquiv x : Nat) =
      (Nat.Primes.prodNatEquiv y : Nat) :=
    Nat.cast_injective hpowReal
  apply Nat.Primes.prodNatEquiv.injective
  exact Subtype.ext hpow

/-- The rotated clock used by the formal differential realization. -/
def rotatedPrimePowerClockWeight (x : PrimePowerClockIndex) : ℂ :=
  Complex.I * primePowerClockWeight x

/-- Rotation by `I` preserves the simple prime-power spectrum. -/
theorem rotatedPrimePowerClockWeight_injective :
    Function.Injective rotatedPrimePowerClockWeight := by
  intro x y hxy
  apply primePowerClockWeight_injective
  exact mul_left_cancel₀ Complex.I_ne_zero hxy

/-- Finite-prime locality for a prime-power profile. -/
def PrimePowerClockLocal (a : PrimePowerClockIndex -> ℂ) : Prop :=
  RayLocal primePowerClockRay a

/-- Polynomial action of the prime-power logarithmic clock. -/
def primePowerClockPolynomialApply
    (P : ℂ[X]) (a : PrimePowerClockIndex -> ℂ) : PrimePowerClockIndex -> ℂ :=
  polynomialClockApply primePowerClockWeight P a

/-- **Prime-clock saturation.**  A nonzero polynomial in the complete prime-power clock preserves
finite-prime locality exactly.  This is the representative-level form of torsion-freeness of the
prime-clock quotient by finite-prime profiles. -/
theorem primePowerClockPolynomialApply_local_iff
    (P : ℂ[X]) (hP : P ≠ 0) (a : PrimePowerClockIndex -> ℂ) :
    PrimePowerClockLocal (primePowerClockPolynomialApply P a) ↔
      PrimePowerClockLocal a := by
  exact rayLocal_polynomialClockApply_iff primePowerClockRay
    primePowerClockWeight primePowerClockWeight_injective P hP a

/-- Quotient form of prime-clock torsion-freeness. -/
theorem primePowerClockQuotient_polynomialClock_eq_zero_iff
    (P : ℂ[X]) (hP : P ≠ 0) (a : PrimePowerClockIndex -> ℂ) :
    (rayLocalSubmodule primePowerClockRay).mkQ
        (primePowerClockPolynomialApply P a) = 0 ↔
      (rayLocalSubmodule primePowerClockRay).mkQ a = 0 := by
  exact rayQuotient_polynomialClock_eq_zero_iff primePowerClockRay
    primePowerClockWeight primePowerClockWeight_injective P hP a

/-- Polynomial action of the rotated prime-power clock. -/
def rotatedPrimePowerClockPolynomialApply
    (P : ℂ[X]) (a : PrimePowerClockIndex -> ℂ) : PrimePowerClockIndex -> ℂ :=
  polynomialClockApply rotatedPrimePowerClockWeight P a

/-- Rotated prime-clock saturation, in the exact normalization used by logarithmic
differentiation. -/
theorem rotatedPrimePowerClockPolynomialApply_local_iff
    (P : ℂ[X]) (hP : P ≠ 0) (a : PrimePowerClockIndex -> ℂ) :
    PrimePowerClockLocal (rotatedPrimePowerClockPolynomialApply P a) ↔
      PrimePowerClockLocal a := by
  exact rayLocal_polynomialClockApply_iff primePowerClockRay
    rotatedPrimePowerClockWeight rotatedPrimePowerClockWeight_injective P hP a

/-- Quotient torsion-freeness for the rotated differential clock. -/
theorem rotatedPrimePowerClockQuotient_polynomialClock_eq_zero_iff
    (P : ℂ[X]) (hP : P ≠ 0) (a : PrimePowerClockIndex -> ℂ) :
    (rayLocalSubmodule primePowerClockRay).mkQ
        (rotatedPrimePowerClockPolynomialApply P a) = 0 ↔
      (rayLocalSubmodule primePowerClockRay).mkQ a = 0 := by
  exact rayQuotient_polynomialClock_eq_zero_iff primePowerClockRay
    rotatedPrimePowerClockWeight rotatedPrimePowerClockWeight_injective P hP a

/-- Positive nonlocality form: every nonzero polynomial clock orbit of a nonlocal profile remains
nonlocal. -/
theorem not_primePowerClockLocal_polynomialClockApply_iff
    (P : ℂ[X]) (hP : P ≠ 0) (a : PrimePowerClockIndex -> ℂ) :
    ¬ PrimePowerClockLocal (primePowerClockPolynomialApply P a) ↔
      ¬ PrimePowerClockLocal a := by
  rw [primePowerClockPolynomialApply_local_iff P hP a]

end

end GaloisForLFunctions.HTGeometry
