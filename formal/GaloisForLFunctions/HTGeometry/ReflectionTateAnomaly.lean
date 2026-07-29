import GaloisForLFunctions.HTGeometry.ReflectedOrbitCharge
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Reflection-gauged orbit charge and its Tate anomaly

The Gamma charge-conjugation involution is `C(q) = -r(q)`.  A degree-one cocycle for the reflection
group `C₂` therefore satisfies `q + C(q) = 0`, equivalently `r(q) = q`, and a coboundary has the
form `q = g - C(g) = g + r(g)`.

This file computes the cohomology both constructively and as an actual quotient.  A finite cocycle
is a coboundary exactly when its coefficient at every fixed label is even.  Hence the complete
degree-one anomaly is one `Z/2` parity for every fixed orbit label.  The quotient of cocycles by
coboundaries is additively equivalent to the finitely supported `Z/2`-valued functions on the fixed
locus.  Free reflection two-cycles are cohomologically trivial, while a fixed-label unit is
nontrivial and its double is a boundary.

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

/-- The fixed locus of an orbit-label reflection. -/
def ReflectionFixedPoint {ι : Type*} (r : ι ≃ ι) := {i : ι // r i = i}

/-- The additive group of signed-reflection one-cocycles. -/
def reflectionTateCocycles {ι : Type*} (r : ι ≃ ι) : AddSubgroup (ι →₀ ℤ) where
  carrier := {q | ReflectionTateCocycle r q}
  zero_mem' := by simp [ReflectionTateCocycle, reflectedCharge]
  add_mem' := by
    intro p q hp hq
    change ReflectionTateCocycle r p at hp
    change ReflectionTateCocycle r q at hq
    change ReflectionTateCocycle r (p + q)
    unfold ReflectionTateCocycle at *
    rw [reflectedCharge_add, hp, hq]
  neg_mem' := by
    intro q hq
    change ReflectionTateCocycle r q at hq
    change ReflectionTateCocycle r (-q)
    unfold ReflectionTateCocycle at *
    have hz : reflectedCharge r (0 : ι →₀ ℤ) = 0 := by
      ext i
      simp [reflectedCharge]
    have hsub := reflectedCharge_sub r 0 q
    simpa [hz, hq] using hsub

/-- Boundaries as an additive map into the cocycle group. -/
def reflectionTateBoundaryHom {ι : Type*} (r : ι ≃ ι)
    (hr : Function.Involutive r) :
    (ι →₀ ℤ) →+ reflectionTateCocycles r where
  toFun g := ⟨reflectionTateBoundary r g, reflectionTateBoundary_cocycle r hr g⟩
  map_zero' := by
    apply Subtype.ext
    simp [reflectionTateBoundary, reflectedCharge]
  map_add' p q := by
    apply Subtype.ext
    simp [reflectionTateBoundary, reflectedCharge_add]
    abel

/-- The subgroup of signed-reflection coboundaries. -/
def reflectionTateBoundaries {ι : Type*} (r : ι ≃ ι)
    (hr : Function.Involutive r) : AddSubgroup (reflectionTateCocycles r) :=
  (reflectionTateBoundaryHom r hr).range

/-- Restriction of a cocycle to the fixed locus, reduced modulo two. -/
def reflectionTateFixedParity {ι : Type*} (r : ι ≃ ι) :
    reflectionTateCocycles r →+ (ReflectionFixedPoint r →₀ ZMod 2) :=
  (Finsupp.comapDomain.addMonoidHom (f := Subtype.val) Subtype.val_injective).comp
    ((Finsupp.mapRange.addMonoidHom (Int.castAddHom (ZMod 2))).comp
      (reflectionTateCocycles r).subtype)

@[simp]
theorem reflectionTateFixedParity_apply {ι : Type*} (r : ι ≃ ι)
    (q : reflectionTateCocycles r) (i : ReflectionFixedPoint r) :
    reflectionTateFixedParity r q i = (q.1 i.1 : ZMod 2) := by
  rfl

/-- Every finitely supported parity pattern on the fixed locus is realized by a cocycle. -/
theorem reflectionTateFixedParity_surjective {ι : Type*} (r : ι ≃ ι) :
    Function.Surjective (reflectionTateFixedParity r) := by
  intro a
  obtain ⟨b, hb⟩ := Finsupp.mapRange_surjective
    (α := ReflectionFixedPoint r) ((↑) : ℤ → ZMod 2) (by simp)
      ZMod.intCast_surjective a
  let q : ι →₀ ℤ := Finsupp.mapDomain Subtype.val b
  have hq : ReflectionTateCocycle r q := by
    rw [ReflectionTateCocycle, reflectedCharge, Finsupp.equivMapDomain_eq_mapDomain,
      ← Finsupp.mapDomain_comp]
    congr 1
    funext i
    exact i.property
  refine ⟨⟨q, hq⟩, ?_⟩
  ext i
  have hbi := DFunLike.congr_fun hb i
  rw [reflectionTateFixedParity_apply]
  change ((Finsupp.mapDomain Subtype.val b i.1 : ℤ) : ZMod 2) = a i
  rw [Finsupp.mapDomain_apply Subtype.val_injective]
  exact hbi

/-- The actual boundary subgroup is exactly the kernel of fixed-point parity. -/
theorem reflectionTateBoundaries_eq_fixedParity_ker
    {ι : Type*} (r : ι ≃ ι) (hr : Function.Involutive r) :
    reflectionTateBoundaries r hr = (reflectionTateFixedParity r).ker := by
  letI : LinearOrder ι := (exists_wellFoundedLT ι).choose
  ext q
  constructor
  · rintro ⟨g, rfl⟩
    rw [AddMonoidHom.mem_ker]
    ext i
    rw [reflectionTateFixedParity_apply]
    change ((reflectionTateBoundary r g i.1 : ℤ) : ZMod 2) = 0
    rw [reflectionTateBoundary_apply_fixed r g i.property]
    have htwo : ((2 : ℤ) : ZMod 2) = 0 := by decide
    rw [Int.cast_mul, htwo, zero_mul]
  · intro hq
    rw [AddMonoidHom.mem_ker] at hq
    have heven : ∀ i, r i = i → Even (q.1 i) := by
      intro i hi
      have hzero := DFunLike.congr_fun hq (⟨i, hi⟩ : ReflectionFixedPoint r)
      have hcast : ((q.1 i : ℤ) : ZMod 2) = 0 := by
        simpa only [reflectionTateFixedParity_apply, Finsupp.zero_apply] using! hzero
      exact even_iff_two_dvd.mpr
        ((ZMod.intCast_zmod_eq_zero_iff_dvd (q.1 i) 2).mp hcast)
    obtain ⟨g, hg⟩ :=
      (reflectionTateCocycle_is_boundary_iff_fixed_even r hr q.1 q.2).mpr heven
    exact ⟨g, Subtype.ext hg.symm⟩

/-- First signed-reflection cohomology: cocycles modulo actual coboundaries. -/
abbrev ReflectionTateCohomology {ι : Type*} (r : ι ≃ ι)
    (hr : Function.Involutive r) :=
  (reflectionTateCocycles r) ⧸ reflectionTateBoundaries r hr

/-- Signed-reflection cohomology is the finitely supported mod-two homology of the fixed locus. -/
noncomputable def reflectionTateCohomologyEquivFixedParity
    {ι : Type*} (r : ι ≃ ι) (hr : Function.Involutive r) :
    ReflectionTateCohomology r hr ≃+ (ReflectionFixedPoint r →₀ ZMod 2) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (reflectionTateBoundaries_eq_fixedParity_ker r hr)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (reflectionTateFixedParity r) (reflectionTateFixedParity_surjective r))

/-- If the reflection has exactly two fixed labels, its anomaly group is `(Z/2)^2`. -/
noncomputable def reflectionTateCohomologyEquivZModTwoSquared
    {ι : Type*} (r : ι ≃ ι) (hr : Function.Involutive r)
    (hfixed : ReflectionFixedPoint r ≃ Fin 2) :
    ReflectionTateCohomology r hr ≃+ (ZMod 2 × ZMod 2) :=
  (reflectionTateCohomologyEquivFixedParity r hr).trans <|
    (Finsupp.domCongr hfixed).trans <|
      Finsupp.addEquivFunOnFinite.trans (RingEquiv.piFinTwo fun _ => ZMod 2).toAddEquiv

/-- Reflection of the unit real shift circle. -/
def unitAddCircleReflection : AddCircle (1 : ℝ) ≃ AddCircle (1 : ℝ) where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x

/-- The two standard points of order dividing two on the unit shift circle. -/
def unitAddCircleTwoTorsion (i : Fin 2) : AddCircle (1 : ℝ) :=
  (((i : ℕ) : ℝ) / 2 : ℝ)

theorem unitAddCircleTwoTorsion_fixed (i : Fin 2) :
    unitAddCircleReflection (unitAddCircleTwoTorsion i) = unitAddCircleTwoTorsion i := by
  fin_cases i
  · simp [unitAddCircleReflection, unitAddCircleTwoTorsion]
  · simp only [unitAddCircleReflection, unitAddCircleTwoTorsion, Equiv.coe_fn_mk]
    norm_num only [Nat.cast_one]
    change -(((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)) =
      (((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ))
    rw [← AddCircle.coe_neg]
    have h : -((1 : ℝ) / 2) = (1 : ℝ) / 2 - 1 := by ring
    rw [h, AddCircle.coe_sub, AddCircle.coe_period, sub_zero]

/-- The unit shift-circle reflection has exactly the integer and half-integer fixed labels. -/
noncomputable def unitAddCircleReflectionFixedEquivFinTwo :
    ReflectionFixedPoint unitAddCircleReflection ≃ Fin 2 := by
  let f : Fin 2 → ReflectionFixedPoint unitAddCircleReflection :=
    fun i => ⟨unitAddCircleTwoTorsion i, unitAddCircleTwoTorsion_fixed i⟩
  have hinj : Function.Injective f := by
    have hhalf : (((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
      change ¬ ((((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)) = 0)
      rw [AddCircle.coe_eq_zero_iff (p := (1 : ℝ))]
      rintro ⟨n, hn⟩
      simp only [zsmul_eq_mul, mul_one] at hn
      have hn' : (2 : ℝ) * (n : ℝ) = 1 := by rw [hn]; ring
      have hn'' : (2 : ℤ) * n = 1 := by exact_mod_cast hn'
      omega
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have hval := congrArg Subtype.val hij
      have h01 : (0 : AddCircle (1 : ℝ)) =
          (((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)) := by
        simpa only [f, unitAddCircleTwoTorsion, Nat.cast_zero, Nat.cast_one, zero_div,
          QuotientAddGroup.mk_zero] using hval
      exfalso
      exact hhalf h01.symm
    · have hval := congrArg Subtype.val hij
      have h10 : (((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        simpa only [f, unitAddCircleTwoTorsion, Nat.cast_zero, Nat.cast_one, zero_div,
          QuotientAddGroup.mk_zero] using hval
      exfalso
      exact hhalf h10
    · rfl
  have hsurj : Function.Surjective f := by
    intro x
    have htwo : 2 • x.1 = 0 := by
      have hfix := x.2
      change -x.1 = x.1 at hfix
      rw [two_nsmul]
      exact neg_eq_iff_add_eq_zero.mp hfix
    obtain ⟨m, hm, hx⟩ :=
      (AddCircle.nsmul_eq_zero_iff (p := (1 : ℝ)) (n := 2) (by omega)).mp htwo
    interval_cases m
    · refine ⟨0, Subtype.ext ?_⟩
      simpa [f, unitAddCircleTwoTorsion] using hx
    · refine ⟨1, Subtype.ext ?_⟩
      simpa [f, unitAddCircleTwoTorsion] using hx
  exact (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm

/-- The standard reflected Gamma shift circle has anomaly group exactly `(Z/2)^2`. -/
noncomputable def unitAddCircleReflectionTateCohomologyEquivZModTwoSquared :
    ReflectionTateCohomology unitAddCircleReflection (fun x => neg_neg x) ≃+
      (ZMod 2 × ZMod 2) :=
  reflectionTateCohomologyEquivZModTwoSquared unitAddCircleReflection
    (fun x => neg_neg x) unitAddCircleReflectionFixedEquivFinTwo

/-! ### Characteristic-zero averaging and restricted gauges -/

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V]

/-- Displacement of a vector under a linear reflection. -/
def relativeReflectionBoundary (C : V →ₗ[K] V) (g : V) : V :=
  C g - g

/-- The signed reflection condition satisfied by a reflection displacement. -/
def LinearReflectionAntiInvariant (C : V →ₗ[K] V) (v : V) : Prop :=
  C v = -v

/-- The canonical primitive of an anti-invariant displacement supplied by
characteristic-zero averaging. -/
def canonicalReflectionPrimitive (v : V) : V :=
  (-((2 : K)⁻¹)) • v

/-- The canonical primitive really has the prescribed reflection displacement. -/
theorem relativeReflectionBoundary_canonical
    (C : V →ₗ[K] V) {v : V} (hv : LinearReflectionAntiInvariant C v) :
    relativeReflectionBoundary C (canonicalReflectionPrimitive (K := K) v) = v := by
  rw [relativeReflectionBoundary, canonicalReflectionPrimitive, map_smul, hv]
  have htwo : (2 : K) ≠ 0 := by norm_num
  module

/-- **Primitive-torsor theorem.** The full fibre of the reflection-boundary map above an
anti-invariant displacement `v` is the affine translate of the fixed subspace by the canonical
primitive `-v/2`.  Hence failure of a restricted realization is an incidence failure of this
affine torsor, while nonuniqueness is exactly its surviving fixed direction. -/
theorem relativeReflectionBoundary_eq_iff_sub_canonical_fixed
    (C : V →ₗ[K] V) {v g : V} (hv : LinearReflectionAntiInvariant C v) :
    relativeReflectionBoundary C g = v ↔
      C (g - canonicalReflectionPrimitive (K := K) v) =
        g - canonicalReflectionPrimitive (K := K) v := by
  have hcanonical := relativeReflectionBoundary_canonical (K := K) C hv
  constructor
  · intro hg
    rw [map_sub]
    rw [relativeReflectionBoundary] at hg hcanonical
    have heq : C g - g =
        C (canonicalReflectionPrimitive (K := K) v) -
          canonicalReflectionPrimitive (K := K) v :=
      hg.trans hcanonical.symm
    calc
      C g - C (canonicalReflectionPrimitive (K := K) v) =
          (C g - g) +
            (g - C (canonicalReflectionPrimitive (K := K) v)) := by abel
      _ = (C (canonicalReflectionPrimitive (K := K) v) -
            canonicalReflectionPrimitive (K := K) v) +
            (g - C (canonicalReflectionPrimitive (K := K) v)) := by rw [heq]
      _ = g - canonicalReflectionPrimitive (K := K) v := by abel
  · intro hfixed
    rw [map_sub] at hfixed
    rw [relativeReflectionBoundary] at hcanonical ⊢
    calc
      C g - g =
          (C g - C (canonicalReflectionPrimitive (K := K) v)) +
            (C (canonicalReflectionPrimitive (K := K) v) - g) := by abel
      _ = (g - canonicalReflectionPrimitive (K := K) v) +
            (C (canonicalReflectionPrimitive (K := K) v) - g) := by rw [hfixed]
      _ = C (canonicalReflectionPrimitive (K := K) v) -
            canonicalReflectionPrimitive (K := K) v := by abel
      _ = v := hcanonical

omit [CharZero K] in
/-- Any two primitives of the same reflection displacement differ by a fixed vector. -/
theorem relativeReflectionBoundary_sub_fixed
    (C : V →ₗ[K] V) {v g h : V}
    (hg : relativeReflectionBoundary C g = v)
    (hh : relativeReflectionBoundary C h = v) :
    C (g - h) = g - h := by
  rw [map_sub]
  rw [relativeReflectionBoundary] at hg hh
  have heq : C g - g = C h - h := hg.trans hh.symm
  calc
    C g - C h = (C g - g) + (g - C h) := by abel
    _ = (C h - h) + (g - C h) := by rw [heq]
    _ = g - h := by abel

/-- **Characteristic-zero averaging firewall.** Every anti-invariant vector for a linear
reflection is an unrestricted reflection boundary.  Thus complex-linear reflection cohomology
cannot retain such a defect once arbitrary gauges are allowed. -/
theorem linearReflectionAntiInvariant_is_boundary
    (C : V →ₗ[K] V) {v : V} (hv : LinearReflectionAntiInvariant C v) :
    ∃ g : V, relativeReflectionBoundary C g = v := by
  exact ⟨canonicalReflectionPrimitive (K := K) v,
    relativeReflectionBoundary_canonical (K := K) C hv⟩

/-- **Restricted-gauge positive replacement.** Let `D` be a reflection-stable subspace of
admissible gauges.  An anti-invariant displacement has a primitive in `D` exactly when the
displacement itself belongs to `D`.  In particular, restricting gauges can retain precisely the
defects erased by unrestricted characteristic-zero averaging. -/
theorem linearReflectionAntiInvariant_relativeBoundary_iff_mem
    (C : V →ₗ[K] V) (D : Submodule K V)
    (hstable : ∀ g ∈ D, C g ∈ D)
    {v : V} (hv : LinearReflectionAntiInvariant C v) :
    (∃ g : V, g ∈ D ∧ relativeReflectionBoundary C g = v) ↔ v ∈ D := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact D.sub_mem (hstable g hg) hg
  · intro hvD
    refine ⟨(-((2 : K)⁻¹)) • v, D.smul_mem _ hvD, ?_⟩
    rw [relativeReflectionBoundary, map_smul, hv]
    have htwo : (2 : K) ≠ 0 := by norm_num
    module

/-- **Linear-incidence collapse.** For any family of reflection-stable linear admissibility
conditions, individual membership of an anti-invariant displacement supplies one primitive that
satisfies every condition simultaneously: the canonical primitive `-v/2`.  Thus such linear
incidence systems have no higher compatibility obstruction. -/
theorem linearReflectionAntiInvariant_simultaneousRelativeBoundary_iff
    {I : Type*} (C : V →ₗ[K] V) (D : I → Submodule K V)
    (hstable : ∀ i g, g ∈ D i → C g ∈ D i)
    {v : V} (hv : LinearReflectionAntiInvariant C v) :
    (∃ g : V, (∀ i, g ∈ D i) ∧ relativeReflectionBoundary C g = v) ↔
      ∀ i, v ∈ D i := by
  constructor
  · rintro ⟨g, hg, rfl⟩ i
    exact (D i).sub_mem (hstable i g (hg i)) (hg i)
  · intro hvD
    refine ⟨canonicalReflectionPrimitive (K := K) v, ?_,
      relativeReflectionBoundary_canonical (K := K) C hv⟩
    intro i
    exact (D i).smul_mem _ (hvD i)

/-- For reflection-stable linear gauges, separate solvability in every admissible class is
equivalent to solvability by one common primitive.  This is the precise Helly-number-one form of
the linear-incidence collapse. -/
theorem linearReflectionAntiInvariant_simultaneous_iff_individual
    {I : Type*} (C : V →ₗ[K] V) (D : I → Submodule K V)
    (hstable : ∀ i g, g ∈ D i → C g ∈ D i)
    {v : V} (hv : LinearReflectionAntiInvariant C v) :
    (∃ g : V, (∀ i, g ∈ D i) ∧ relativeReflectionBoundary C g = v) ↔
      ∀ i, ∃ g : V, g ∈ D i ∧ relativeReflectionBoundary C g = v := by
  rw [linearReflectionAntiInvariant_simultaneousRelativeBoundary_iff C D hstable hv]
  constructor
  · intro hvD i
    exact (linearReflectionAntiInvariant_relativeBoundary_iff_mem
      C (D i) (hstable i) hv).2 (hvD i)
  · intro h i
    exact (linearReflectionAntiInvariant_relativeBoundary_iff_mem
      C (D i) (hstable i) hv).1 (h i)

end

end GaloisForLFunctions
