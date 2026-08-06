import GaloisForLFunctions.HTGeometry.TameEisensteinDifferentExponent

/-!
# The local ramification order law

For a ring homomorphism between discrete valuation rings, the valuation of a pullback is the
ramification index times the valuation downstairs.  Combined with the exact tame ramification
exponent this assembles the full local order law of a rational eigenvolume,

`ord (pullback of the form) = e * ord (form) + (e - 1)`,

equivalently `c + 1 = e * (c' + 1)` after the Jacobian shift.

mathlib defines the ramification index combinatorially and has no theorem computing the effect of
a finite extension on adic valuations; the scaling identity is proved here from the discrete
valuation structure alone, with no finiteness, separability or Dedekind hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

/-- A unit has valuation zero. -/
theorem addVal_of_isUnit {x : B} (hx : IsUnit x) : addVal B x = 0 := by
  have hdvd : x ∣ 1 := hx.dvd
  have hle : addVal B x ≤ addVal B 1 := addVal_le_iff_dvd.mpr hdvd
  rw [AddValuation.map_one] at hle
  exact le_antisymm hle zero_le

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Powers of a uniformizer image scale by the ramification index. -/
theorem addVal_map_pow_of_addVal_eq (φ : A →+* B) {π : A}
    (e : ℕ) (he : addVal B (φ π) = (e : ℕ∞)) :
    ∀ n : ℕ, addVal B (φ π ^ n) = (e : ℕ∞) * (n : ℕ∞) := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, AddValuation.map_mul, ih, he]
    push_cast
    ring

/-- **The ramification index scales the valuation.**  If a ring homomorphism of discrete
valuation rings sends some uniformizer to an element of valuation `e`, then it multiplies every
valuation by `e`. -/
theorem addVal_map_eq_mul_ramification (φ : A →+* B) {π : A} (hπ : Irreducible π)
    (e : ℕ) (he : addVal B (φ π) = (e : ℕ∞)) (a : A) (ha : a ≠ 0) :
    addVal B (φ a) = (e : ℕ∞) * addVal A a := by
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
  have hdown : addVal A ((u : A) * π ^ n) = (n : ℕ∞) := by
    rw [AddValuation.map_mul, addVal_of_isUnit u.isUnit, zero_add,
      addVal_pow_uniformizer hπ]
  have hup : addVal B (φ ((u : A) * π ^ n)) = (e : ℕ∞) * (n : ℕ∞) := by
    rw [map_mul, map_pow, AddValuation.map_mul,
      addVal_of_isUnit (u.isUnit.map φ), zero_add]
    exact addVal_map_pow_of_addVal_eq φ e he n
  rw [hup, hdown]

/-- **The local order law of a rational eigenvolume.**  The valuation of the pullback of a form
with coefficient `ω`, twisted by a Jacobian factor of valuation `e - 1`, is
`e * ord ω + (e - 1)`. -/
theorem addVal_pullback_form (φ : A →+* B) {π : A} (hπ : Irreducible π)
    (e : ℕ) (he : addVal B (φ π) = (e : ℕ∞)) (ω : A) (hω : ω ≠ 0)
    (jac : B) (hjac : addVal B jac = ((e - 1 : ℕ) : ℕ∞)) :
    addVal B (φ ω * jac) = (e : ℕ∞) * addVal A ω + ((e - 1 : ℕ) : ℕ∞) := by
  rw [AddValuation.map_mul, addVal_map_eq_mul_ramification φ hπ e he ω hω, hjac]

/-- The Jacobian shift: the unshifted order law and the shifted order law are equivalent. -/
theorem orderLaw_iff_shiftLaw {cF cE : ℤ} {e : ℕ} :
    cE = (e : ℤ) * cF + ((e : ℤ) - 1) ↔ cE + 1 = (e : ℤ) * (cF + 1) := by
  constructor
  · intro h
    rw [h]; ring
  · intro h
    have : cE + 1 = (e : ℤ) * cF + (e : ℤ) := by rw [h]; ring
    omega

/-! ## Rational forms: orders with poles -/

/-- Natural-number order of a ring element at the place. -/
noncomputable def natOrd (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (a : A) : ℕ :=
  (addVal A a).toNat

theorem natOrd_spec {a : A} (ha : a ≠ 0) : addVal A a = (natOrd A a : ℕ∞) :=
  (ENat.coe_toNat (by rwa [Ne, addVal_eq_top_iff])).symm

theorem natOrd_mul {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    natOrd A (a * b) = natOrd A a + natOrd A b := by
  refine ENat.coe_inj.mp ?_
  rw [← natOrd_spec (mul_ne_zero ha hb), AddValuation.map_mul, natOrd_spec ha,
    natOrd_spec hb]
  push_cast
  ring

/-- The ramification index scales the natural-number order. -/
theorem natOrd_map_eq_mul_ramification (φ : A →+* B) (hinj : Function.Injective φ)
    {π : A} (hπ : Irreducible π) (e : ℕ) (he : addVal B (φ π) = (e : ℕ∞))
    (a : A) (ha : a ≠ 0) :
    natOrd B (φ a) = e * natOrd A a := by
  have hφa : φ a ≠ 0 := fun h => ha (hinj (by rw [h, map_zero]))
  refine ENat.coe_inj.mp ?_
  rw [← natOrd_spec hφa, addVal_map_eq_mul_ramification φ hπ e he a ha, natOrd_spec ha]
  push_cast
  ring

/-- **The order law for a rational form.**  Writing a rational form as a quotient `a / b`, its
order is `natOrd a - natOrd b`, which may be negative; the ramification index scales it. -/
theorem ramificationOrder_frac (φ : A →+* B) (hinj : Function.Injective φ)
    {π : A} (hπ : Irreducible π) (e : ℕ) (he : addVal B (φ π) = (e : ℕ∞))
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((natOrd B (φ a) : ℤ) - (natOrd B (φ b) : ℤ)) =
      (e : ℤ) * ((natOrd A a : ℤ) - (natOrd A b : ℤ)) := by
  rw [natOrd_map_eq_mul_ramification φ hinj hπ e he a ha,
    natOrd_map_eq_mul_ramification φ hinj hπ e he b hb]
  push_cast
  ring

/-- **The local order law of a rational eigenvolume, with poles allowed.**  This is equation (8)
for a form of arbitrary integer order: the pullback order is `e` times the order downstairs plus
the Jacobian contribution `e - 1`. -/
theorem ramificationOrderLaw_frac (φ : A →+* B) (hinj : Function.Injective φ)
    {π : A} (hπ : Irreducible π) (e : ℕ) (hepos : 0 < e)
    (he : addVal B (φ π) = (e : ℕ∞))
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0)
    (jac : B) (hjac0 : jac ≠ 0) (hjac : natOrd B jac = e - 1) :
    ((natOrd B (φ a * jac) : ℤ) - (natOrd B (φ b) : ℤ)) =
      (e : ℤ) * ((natOrd A a : ℤ) - (natOrd A b : ℤ)) + ((e : ℤ) - 1) := by
  have hφa : φ a ≠ 0 := fun h => ha (hinj (by rw [h, map_zero]))
  rw [natOrd_mul hφa hjac0, hjac]
  have hcast : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by
    have : 1 ≤ e := hepos
    push_cast [Nat.cast_sub this]
    ring
  push_cast [hcast]
  rw [natOrd_map_eq_mul_ramification φ hinj hπ e he a ha,
    natOrd_map_eq_mul_ramification φ hinj hπ e he b hb]
  push_cast
  ring

/-- The shifted form (9) of the rational order law. -/
theorem ramificationShiftLaw_frac (φ : A →+* B) (hinj : Function.Injective φ)
    {π : A} (hπ : Irreducible π) (e : ℕ) (hepos : 0 < e)
    (he : addVal B (φ π) = (e : ℕ∞))
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0)
    (jac : B) (hjac0 : jac ≠ 0) (hjac : natOrd B jac = e - 1) :
    ((natOrd B (φ a * jac) : ℤ) - (natOrd B (φ b) : ℤ)) + 1 =
      (e : ℤ) * (((natOrd A a : ℤ) - (natOrd A b : ℤ)) + 1) :=
  orderLaw_iff_shiftLaw.mp
    (ramificationOrderLaw_frac φ hinj hπ e hepos he a b ha hb jac hjac0 hjac)

end GaloisForLFunctions.HTGeometry
