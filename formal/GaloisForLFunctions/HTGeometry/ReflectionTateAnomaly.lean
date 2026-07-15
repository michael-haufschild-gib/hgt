import GaloisForLFunctions.HTGeometry.ReflectedOrbitCharge

/-!
# Reflection-gauged orbit charge and its Tate anomaly

The Gamma charge-conjugation involution is `C(q) = -r(q)`.  A degree-one cocycle for the reflection
group `C₂` therefore satisfies `q + C(q) = 0`, equivalently `r(q) = q`, and a coboundary has the
form `q = g - C(g) = g + r(g)`.

This file computes that cohomology without constructing an abstract quotient.  A finite cocycle is
a coboundary exactly when its coefficient at every fixed label is even.  Hence the complete
degree-one anomaly is one `Z/2` parity for every fixed orbit label.  Free reflection two-cycles are
cohomologically trivial, while a fixed-label unit is nontrivial and its double is a boundary.

For the reflected Gamma shift cylinder there are two fixed orbit labels, so the paper theorem
obtains two independent binary mirror anomalies.  The Lean result below is the coefficient-generic
classification used by that application.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A reflection Tate coboundary for the signed action `C(q)=-r(q)`: `(1-C)g=g+r(g)`. -/
def reflectionTateBoundary {ι : Type*} (r : ι ≃ ι) (g : ι →₀ ℤ) : ι →₀ ℤ :=
  g + reflectedCharge r g

/-- A degree-one cocycle for the signed reflection action. -/
def ReflectionTateCocycle {ι : Type*} (r : ι ≃ ι) (q : ι →₀ ℤ) : Prop :=
  reflectedCharge r q = q

/-- Two reflection cocycles represent the same anomaly class when their difference is a Tate
coboundary. -/
def ReflectionTateCohomologous {ι : Type*} (r : ι ≃ ι)
    (p q : ι →₀ ℤ) : Prop :=
  ∃ g, p - q = reflectionTateBoundary r g

theorem reflectedCharge_add {ι A : Type*} [AddCommGroup A]
    (r : ι ≃ ι) (p q : ι →₀ A) :
    reflectedCharge r (p + q) = reflectedCharge r p + reflectedCharge r q := by
  ext i
  simp [reflectedCharge, Finsupp.equivMapDomain_apply]

/-- Every Tate boundary is a cocycle. -/
theorem reflectionTateBoundary_cocycle {ι : Type*} (r : ι ≃ ι)
    (hr : Function.Involutive r) (g : ι →₀ ℤ) :
    ReflectionTateCocycle r (reflectionTateBoundary r g) := by
  rw [ReflectionTateCocycle, reflectionTateBoundary, reflectedCharge_add,
    reflectedCharge_involutive r hr]
  abel

/-- Pointwise cocycle condition: a signed-reflection one-cocycle is constant on reflection
orbits. -/
theorem reflectionTateCocycle_iff {ι : Type*} (r : ι ≃ ι)
    (hr : Function.Involutive r) (q : ι →₀ ℤ) :
    ReflectionTateCocycle r q ↔ ∀ i, q (r i) = q i := by
  constructor
  · intro h i
    have hi := DFunLike.congr_fun h i
    simpa [ReflectionTateCocycle, reflectedCharge, Finsupp.equivMapDomain_apply,
      involutiveEquiv_symm_apply r hr] using hi
  · intro h
    ext i
    simpa [ReflectionTateCocycle, reflectedCharge, Finsupp.equivMapDomain_apply,
      involutiveEquiv_symm_apply r hr] using h i

/-- At a fixed mirror label, every boundary coefficient is even. -/
theorem reflectionTateBoundary_apply_fixed {ι : Type*} (r : ι ≃ ι)
    (g : ι →₀ ℤ) {i : ι} (hi : r i = i) :
    reflectionTateBoundary r g i = 2 * g i := by
  have hsymm : r.symm i = i := by
    apply r.injective
    simp [hi]
  simp [reflectionTateBoundary, reflectedCharge, Finsupp.equivMapDomain_apply,
    hsymm, two_mul]

/-- Explicit finite primitive: take half the coefficient on fixed labels, the whole coefficient on
the chosen smaller member of a free two-cycle, and zero on the larger member. -/
def reflectionTatePrimitive {ι : Type*} [LinearOrder ι]
    (r : ι ≃ ι) (q : ι →₀ ℤ) : ι →₀ ℤ :=
  Finsupp.onFinset q.support
    (fun i => if r i = i then q i / 2 else if i < r i then q i else 0)
    (by
      intro i h
      by_contra hi
      have hzero : q i = 0 := by simpa using hi
      simp [hzero] at h)

@[simp]
theorem reflectionTatePrimitive_apply {ι : Type*} [LinearOrder ι]
    (r : ι ≃ ι) (q : ι →₀ ℤ) (i : ι) :
    reflectionTatePrimitive r q i =
      if r i = i then q i / 2 else if i < r i then q i else 0 := by
  rfl

/-- The primitive contracts every cocycle whose fixed-label coefficients are even. -/
theorem reflectionTateBoundary_primitive {ι : Type*} [LinearOrder ι]
    (r : ι ≃ ι) (hr : Function.Involutive r) (q : ι →₀ ℤ)
    (hq : ReflectionTateCocycle r q)
    (heven : ∀ i, r i = i → Even (q i)) :
    reflectionTateBoundary r (reflectionTatePrimitive r q) = q := by
  have hpoint := (reflectionTateCocycle_iff r hr q).mp hq
  ext i
  have hsymm := involutiveEquiv_symm_apply r hr i
  rw [reflectionTateBoundary]
  simp only [Finsupp.add_apply, reflectedCharge, Finsupp.equivMapDomain_apply, hsymm,
    reflectionTatePrimitive_apply]
  by_cases hfix : r i = i
  · have hhalf := Int.two_mul_ediv_two_of_even (heven i hfix)
    simp [hfix]
    omega
  · by_cases hlt : i < r i
    · have hnback : ¬ r i < i := not_lt_of_ge (le_of_lt hlt)
      simp [hfix, hlt, hr i, Ne.symm hfix, hnback]
    · have hback : r i < i := lt_of_le_of_ne (le_of_not_gt hlt) hfix
      simp [hfix, hlt, hr i, Ne.symm hfix, hback, hpoint i]

/-- **Complete reflection-anomaly criterion.** A finite cocycle is a coboundary exactly when every
fixed-label coefficient is even. -/
theorem reflectionTateCocycle_is_boundary_iff_fixed_even
    {ι : Type*} [LinearOrder ι] (r : ι ≃ ι) (hr : Function.Involutive r)
    (q : ι →₀ ℤ) (hq : ReflectionTateCocycle r q) :
    (∃ g, q = reflectionTateBoundary r g) ↔
      ∀ i, r i = i → Even (q i) := by
  constructor
  · rintro ⟨g, rfl⟩ i hi
    refine ⟨g i, ?_⟩
    rw [reflectionTateBoundary_apply_fixed r g hi]
    omega
  · intro heven
    exact ⟨reflectionTatePrimitive r q,
      (reflectionTateBoundary_primitive r hr q hq heven).symm⟩

/-- **Parity classifies reflection cohomology.** Two finite cocycles are cohomologous exactly when
their coefficients have equal parity at every fixed label. -/
theorem reflectionTateCohomologous_iff_fixed_even
    {ι : Type*} [LinearOrder ι] (r : ι ≃ ι) (hr : Function.Involutive r)
    (p q : ι →₀ ℤ) (hp : ReflectionTateCocycle r p)
    (hq : ReflectionTateCocycle r q) :
    ReflectionTateCohomologous r p q ↔
      ∀ i, r i = i → Even (p i - q i) := by
  have hsub : ReflectionTateCocycle r (p - q) := by
    rw [ReflectionTateCocycle, reflectedCharge_sub, hp, hq]
  exact reflectionTateCocycle_is_boundary_iff_fixed_even r hr (p - q) hsub

/-- A unit charge at a fixed mirror label is a Tate cocycle. -/
theorem fixedMirrorCharge_cocycle {ι : Type*} [LinearOrder ι]
    (r : ι ≃ ι) {i : ι} (hi : r i = i) (m : ℤ) :
    ReflectionTateCocycle r (Finsupp.single i m) := by
  rw [ReflectionTateCocycle, reflectedCharge_single, hi]

/-- A fixed-mirror unit represents a nonzero order-two anomaly class. -/
theorem fixedMirrorUnit_not_boundary {ι : Type*} [LinearOrder ι]
    (r : ι ≃ ι) (hr : Function.Involutive r) {i : ι} (hi : r i = i) :
    ¬ ∃ g, Finsupp.single i (1 : ℤ) = reflectionTateBoundary r g := by
  intro h
  have hc := (reflectionTateCocycle_is_boundary_iff_fixed_even r hr
    (Finsupp.single i (1 : ℤ)) (fixedMirrorCharge_cocycle r hi 1)).mp h i hi
  norm_num at hc

/-- Twice any fixed-mirror charge is a boundary. -/
theorem fixedMirrorDouble_is_boundary {ι : Type*} [LinearOrder ι]
    (r : ι ≃ ι) {i : ι} (hi : r i = i) (m : ℤ) :
    Finsupp.single i (2 * m) = reflectionTateBoundary r (Finsupp.single i m) := by
  ext j
  simp [reflectionTateBoundary, reflectedCharge, Finsupp.single_apply, hi, two_mul]

/-- Every equal-charge free mirror pair is already a boundary and carries no Tate anomaly. -/
theorem freeMirrorPair_is_boundary {ι : Type*} [LinearOrder ι]
    (r : ι ≃ ι) (i : ι) (m : ℤ) :
    Finsupp.single i m + Finsupp.single (r i) m =
      reflectionTateBoundary r (Finsupp.single i m) := by
  simp [reflectionTateBoundary]

end

end GaloisForLFunctions
