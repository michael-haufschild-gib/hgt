import GaloisForLFunctions.RHTower.Deninger.DeningerLogStructure
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The divisorial log structure of a discrete valuation ring

The nonzero elements of a discrete valuation ring form the divisorial log structure of its closed
point: the map to the ring is injective, its image contains the units, and the valuation is a
characteristic map — it vanishes exactly on the units, it is onto the natural numbers because a
uniformizer has valuation one, and two elements of equal valuation are associated.  So the
characteristic monoid of the divisorial log structure is the natural numbers.

* `deningerDVRLog` : the divisorial log structure.
* `deningerDVRLog_isLog` : it is a log structure.
* `deningerDVRChar` : the valuation is a characteristic map with values in `ℕ`.
-/

namespace RHTower

open IsDiscreteValuationRing

open scoped nonZeroDivisors

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The valuation of a nonzero element, as a natural number. -/
noncomputable def deningerDVROrd (x : R⁰) : ℕ :=
  (addVal R (x : R)).untop (fun h =>
    nonZeroDivisors.coe_ne_zero x (addVal_eq_top_iff.1 h))

@[simp]
theorem deningerDVROrd_coe (x : R⁰) : ((deningerDVROrd R x : ℕ) : ℕ∞) = addVal R (x : R) :=
  WithTop.coe_untop _ _

theorem deningerDVROrd_eq_iff {x : R⁰} {n : ℕ} :
    deningerDVROrd R x = n ↔ addVal R (x : R) = (n : ℕ∞) := by
  constructor
  · intro h
    rw [← deningerDVROrd_coe R x, h]
  · intro h
    have h' : ((deningerDVROrd R x : ℕ) : ℕ∞) = (n : ℕ∞) := by rw [deningerDVROrd_coe, h]
    exact_mod_cast h'

theorem deningerDVROrd_one : deningerDVROrd R 1 = 0 := by
  rw [deningerDVROrd_eq_iff]
  simp

theorem deningerDVROrd_mul (x y : R⁰) :
    deningerDVROrd R (x * y) = deningerDVROrd R x + deningerDVROrd R y := by
  rw [deningerDVROrd_eq_iff]
  push_cast
  rw [deningerDVROrd_coe, deningerDVROrd_coe]
  exact addVal_mul

theorem deningerDVROrd_eq_zero_iff (x : R⁰) :
    deningerDVROrd R x = 0 ↔ IsUnit (x : R) := by
  rw [deningerDVROrd_eq_iff, Nat.cast_zero]
  exact addVal_eq_zero_iff

/-- **The divisorial log structure of a discrete valuation ring**: its nonzero elements, with the
inclusion into the ring. -/
def deningerDVRLog : DeningerPreLog R where
  M := R⁰
  hom := (nonZeroDivisors R).subtype

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[simp]
theorem deningerDVRLog_hom (x : R⁰) : (deningerDVRLog R).hom x = (x : R) := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **The divisorial log structure is a log structure**: the inclusion is injective and every unit
of the ring is a nonzero divisor. -/
theorem deningerDVRLog_isLog : DeningerIsLog (deningerDVRLog R) where
  injOn := by
    intro m n _ _ h
    refine Subtype.ext ?_
    exact h
  surjOn := by
    intro r hr
    exact ⟨(⟨r, hr.mem_nonZeroDivisors⟩ : R⁰), rfl⟩

/-- The valuation, as a monoid map to the natural numbers written multiplicatively. -/
noncomputable def deningerDVROrdHom : R⁰ →* Multiplicative ℕ where
  toFun x := Multiplicative.ofAdd (deningerDVROrd R x)
  map_one' := congrArg Multiplicative.ofAdd (deningerDVROrd_one R)
  map_mul' x y := congrArg Multiplicative.ofAdd (deningerDVROrd_mul R x y)

@[simp]
theorem deningerDVROrdHom_apply (x : R⁰) :
    deningerDVROrdHom R x = Multiplicative.ofAdd (deningerDVROrd R x) := rfl

/-- The valuation is onto: a uniformizer has valuation one. -/
theorem deningerDVROrdHom_surjective : Function.Surjective (deningerDVROrdHom R) := by
  intro n
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  have hmem : ϖ ^ (Multiplicative.toAdd n) ∈ R⁰ :=
    pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) _
  refine ⟨(⟨ϖ ^ (Multiplicative.toAdd n), hmem⟩ : R⁰), ?_⟩
  have h : deningerDVROrd R ⟨ϖ ^ (Multiplicative.toAdd n), hmem⟩ = Multiplicative.toAdd n := by
    rw [deningerDVROrd_eq_iff]
    exact hϖ.addVal_pow _
  rw [deningerDVROrdHom_apply, h]
  rfl

/-- The valuation vanishes exactly on the units. -/
theorem deningerDVROrdHom_eq_one_iff (x : R⁰) :
    deningerDVROrdHom R x = 1 ↔ IsUnit (x : R) := by
  rw [deningerDVROrdHom_apply, ← deningerDVROrd_eq_zero_iff R x]
  constructor
  · intro h
    simpa using congrArg Multiplicative.toAdd h
  · intro h
    rw [h]
    rfl

/-- Two nonzero elements of the same valuation differ by a unit. -/
theorem deningerDVROrdHom_orbit (x y : R⁰) (h : deningerDVROrdHom R x = deningerDVROrdHom R y) :
    ∃ w : R⁰, IsUnit (w : R) ∧ x = y * w := by
  have hord : deningerDVROrd R x = deningerDVROrd R y := by
    simpa [deningerDVROrdHom_apply] using congrArg Multiplicative.toAdd h
  have hval : addVal R (x : R) = addVal R (y : R) := by
    rw [← deningerDVROrd_coe R x, ← deningerDVROrd_coe R y, hord]
  obtain ⟨u, hu⟩ := (addVal_eq_iff_associated (x : R) (y : R)).1 hval
  refine ⟨(⟨((u⁻¹ : Rˣ) : R), (Units.isUnit u⁻¹).mem_nonZeroDivisors⟩ : R⁰),
    Units.isUnit u⁻¹, ?_⟩
  refine Subtype.ext ?_
  show (x : R) = (y : R) * ((u⁻¹ : Rˣ) : R)
  rw [← hu, mul_assoc]
  simp

/-- **The valuation is a characteristic map** for the divisorial log structure, so the
characteristic monoid of a discrete valuation ring is `ℕ`. -/
noncomputable def deningerDVRChar :
    DeningerLogChar (deningerDVRLog R) (Multiplicative ℕ) where
  ord := deningerDVROrdHom R
  surj := deningerDVROrdHom_surjective R
  ker := fun m => deningerDVROrdHom_eq_one_iff R m
  orbit := fun m n h => deningerDVROrdHom_orbit R m n h

end RHTower
