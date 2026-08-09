import GaloisForLFunctions.HTGeometry.NomogenicFixedPointCalibration
import Mathlib.Data.PNat.Basic

/-!
# Natural power interventions and inverse-depth normalization

A monoid-homomorphic intervention on finite multisets which is natural under every relabelling is
necessarily uniform multiplicity scaling.  On the ramification-depth category, every rational
comparison from raw weight-one transport to trivial normalized transport is a scalar multiple of
inverse depth.  The canonical inverse-depth comparison preserves every radial parameter, so power
naturality alone cannot select the radial origin.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A monoid endomorphism of finite multisets, natural in every relabelling of the carrier. -/
structure NaturalMultisetEndomorphism where
  app : {X : Type} → Multiset X →+ Multiset X
  natural : ∀ {X Y : Type} (f : X → Y) (s : Multiset X),
    Multiset.map f (app s) = app (Multiset.map f s)

/-- Uniform multiplicity scaling is a natural multiset intervention. -/
def multisetPowerIntervention (r : ℕ) : NaturalMultisetEndomorphism where
  app :=
    { toFun := fun s => r • s
      map_zero' := nsmul_zero r
      map_add' := by intro x y; exact nsmul_add x y r }
  natural := by
    intro X Y f s
    exact Multiset.map_nsmul f r s

/-- Multiplicity of the image of the unique singleton generator. -/
def NaturalMultisetEndomorphism.degree (Φ : NaturalMultisetEndomorphism) : ℕ :=
  (Φ.app ({PUnit.unit} : Multiset PUnit)).card

/-- Every finite multiset on a singleton carrier is a replicate of its unique point. -/
theorem punit_multiset_eq_replicate (s : Multiset PUnit) :
    s = Multiset.replicate s.card PUnit.unit := by
  exact Multiset.eq_replicate_card.2 (fun b _ => Subsingleton.elim b PUnit.unit)

/-- Naturality determines the image of every singleton from the universal singleton carrier. -/
theorem NaturalMultisetEndomorphism.app_singleton
    (Φ : NaturalMultisetEndomorphism) {X : Type} (x : X) :
    Φ.app ({x} : Multiset X) = Φ.degree • ({x} : Multiset X) := by
  let f : PUnit → X := fun _ => x
  have hnat := Φ.natural f ({PUnit.unit} : Multiset PUnit)
  have hrep : Φ.app ({PUnit.unit} : Multiset PUnit) =
      Multiset.replicate Φ.degree PUnit.unit := by
    simpa [NaturalMultisetEndomorphism.degree] using
      punit_multiset_eq_replicate (Φ.app ({PUnit.unit} : Multiset PUnit))
  rw [Multiset.map_singleton, hrep, Multiset.map_replicate] at hnat
  simpa [Multiset.nsmul_singleton] using hnat.symm

/-- A natural multiset endomorphism is uniform multiplicity scaling on every carrier. -/
theorem NaturalMultisetEndomorphism.app_eq_nsmul
    (Φ : NaturalMultisetEndomorphism) {X : Type} (s : Multiset X) :
    Φ.app s = Φ.degree • s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
      rw [← Multiset.singleton_add, map_add, Φ.app_singleton, ih, nsmul_add]

/-- **Natural intervention classification.** Every natural endomorphism of the free commutative
monoid functor is a unique uniform power intervention. -/
theorem naturalMultisetEndomorphism_classification :
    ∀ Φ : NaturalMultisetEndomorphism, ∃! r : ℕ,
      ∀ {X : Type} (s : Multiset X), Φ.app s = r • s := by
  intro Φ
  refine ⟨Φ.degree, fun s => Φ.app_eq_nsmul s, ?_⟩
  intro r hr
  have h := hr ({PUnit.unit} : Multiset PUnit)
  have hc := congrArg Multiset.card h
  simpa [NaturalMultisetEndomorphism.degree] using hc.symm

@[simp] theorem multisetPowerIntervention_app (r : ℕ) {X : Type} (s : Multiset X) :
    (multisetPowerIntervention r).app s = r • s := rfl

/-- Naturality condition for a rational coefficient on ramification depths. -/
def IsRamificationNatural (a : ℕ+ → ℚ) : Prop :=
  ∀ m r : ℕ+, a (m * r) * (r : ℚ) = a m

/-- Scalar multiple of inverse ramification depth. -/
def inverseDepthCoefficient (c : ℚ) (m : ℕ+) : ℚ := c / (m : ℚ)

/-- **Inverse-depth classification.** Every comparison from raw weight-one ramification transport
to trivial normalized transport is a scalar multiple of inverse depth. -/
theorem ramificationNatural_iff (a : ℕ+ → ℚ) :
    IsRamificationNatural a ↔ ∀ m : ℕ+, a m = a 1 / (m : ℚ) := by
  constructor
  · intro ha m
    have hm : (m : ℚ) ≠ 0 := by positivity
    apply (eq_div_iff hm).2
    simpa using ha 1 m
  · intro ha m r
    rw [ha (m * r), ha m]
    have hm : (m : ℚ) ≠ 0 := by positivity
    have hr : (r : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp

/-- Every scalar multiple of inverse depth is ramification-natural. -/
theorem inverseDepthCoefficient_natural (c : ℚ) :
    IsRamificationNatural (inverseDepthCoefficient c) := by
  exact (ramificationNatural_iff _).2 (fun _ => by simp [inverseDepthCoefficient])

/-- Raw radial defect grows linearly with ramification depth. -/
def rawRadialDefect (a : ℚ) (m : ℕ+) : ℚ := (m : ℚ) * a

theorem rawRadialDefect_power (a : ℚ) (m r : ℕ+) :
    rawRadialDefect a (m * r) = (r : ℚ) * rawRadialDefect a m := by
  simp [rawRadialDefect, mul_assoc, mul_comm]

/-- Canonical inverse-depth normalization preserves every radial parameter exactly. -/
theorem inverseDepth_preserves_radial (a : ℚ) (m : ℕ+) :
    inverseDepthCoefficient 1 m * rawRadialDefect a m = a := by
  simp [inverseDepthCoefficient, rawRadialDefect]

/-- A depth-independent ramification comparison is natural exactly when it is zero. -/
theorem constant_ramificationNatural_iff_zero (c : ℚ) :
    IsRamificationNatural (fun _ => c) ↔ c = 0 := by
  constructor
  · intro h
    have h2 : c * (2 : ℚ) = c := by simpa using h 1 2
    linarith
  · rintro rfl
    simp [IsRamificationNatural]

/-- **Natural-power/inverse-depth no-selection law.** Natural free-commutative-monoid
interventions are exactly uniform powers; natural depth comparisons are exactly inverse-depth
scalings; a constant frame must vanish; nevertheless canonical normalization preserves every
radial parameter. -/
theorem naturalPowerIntervention_inverseDepthNormalization_noSelection :
    (∀ Φ : NaturalMultisetEndomorphism, ∃! r : ℕ,
      ∀ {X : Type} (s : Multiset X), Φ.app s = r • s) ∧
    (∀ a : ℕ+ → ℚ,
      IsRamificationNatural a ↔ ∀ m : ℕ+, a m = a 1 / (m : ℚ)) ∧
    (∀ c : ℚ, IsRamificationNatural (inverseDepthCoefficient c)) ∧
    (∀ c : ℚ, IsRamificationNatural (fun _ => c) ↔ c = 0) ∧
    (∀ a : ℚ, ∀ m : ℕ+,
      inverseDepthCoefficient 1 m * rawRadialDefect a m = a) := by
  exact ⟨naturalMultisetEndomorphism_classification,
    ramificationNatural_iff,
    inverseDepthCoefficient_natural,
    constant_ramificationNatural_iff_zero,
    inverseDepth_preserves_radial⟩

end GaloisForLFunctions.HTGeometry
