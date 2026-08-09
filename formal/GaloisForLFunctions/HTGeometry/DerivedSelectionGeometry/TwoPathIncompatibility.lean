import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.IdentityWall

/-!
# The two-path defect and the Cartier incompatibility module

Over a commutative ring `R` with a distinguished element `q` and a landing scalar `c`, put
`U = R²` and

* the source reflection `τ(x,y) = (y,x)`;
* the physical paracyclic rotation `T_q(x,y) = (y, q x)`;
* the coefficient-faithful landing `L = c · id`.

The *two-path defect* is `Δ_q = T_q L - L τ` and the *minimal `T_q`-stable boundary* is
`B_min = im Δ_q + im (T_q Δ_q)`.  The *incompatibility module* is `Q = U / B_min`.

The main results, for `c` a unit:

* `twoPathDefect_apply` / `rotDefect_apply` — the closed forms `Δ_q(x,y) = (0, c(q-1)x)` and
  `T_qΔ_q(x,y) = (c(q-1)x, 0)`;
* `minStableBoundary_eq` — `B_min = I R²` with `I = (q-1)`;
* `incompatEquiv` — `Q ≅ (R/I)²`;
* `annihilator_incompatModule` — `Ann_R Q = I`;
* `range_wallSmul` — the presentation `R² --(q-1)·id--> R² → Q → 0`.

The final section specialises everything to the universal monodromy ring `R = k[q,q⁻¹]` and the
identity wall `I = (q-1)`.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

universe u

section General

variable {R : Type u} [CommRing R]

/-- The source reflection `τ(x,y) = (y,x)`. -/
def srcRefl : (R × R) →ₗ[R] (R × R) where
  toFun p := (p.2, p.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem srcRefl_apply (p : R × R) : srcRefl p = (p.2, p.1) := rfl

/-- The physical paracyclic rotation `T_q(x,y) = (y, q x)`. -/
def paracyclicRot (q : R) : (R × R) →ₗ[R] (R × R) where
  toFun p := (p.2, q * p.1)
  map_add' a b := Prod.ext rfl (by simp [mul_add])
  map_smul' c a := Prod.ext rfl (by simp [mul_left_comm])

@[simp] theorem paracyclicRot_apply (q : R) (p : R × R) :
    paracyclicRot q p = (p.2, q * p.1) := rfl

/-- The coefficient-faithful landing `L = c · id`. -/
def landing (c : R) : (R × R) →ₗ[R] (R × R) := c • LinearMap.id

@[simp] theorem landing_apply (c : R) (p : R × R) : landing c p = (c * p.1, c * p.2) := by
  simp [landing, Prod.smul_def, smul_eq_mul]

/-- The two-path defect `Δ_q = T_q L - L τ`. -/
def twoPathDefect (q c : R) : (R × R) →ₗ[R] (R × R) :=
  paracyclicRot q ∘ₗ landing c - landing c ∘ₗ srcRefl

/-- The rotated defect `T_q Δ_q`. -/
def rotDefect (q c : R) : (R × R) →ₗ[R] (R × R) :=
  paracyclicRot q ∘ₗ twoPathDefect q c

@[simp] theorem twoPathDefect_apply (q c : R) (p : R × R) :
    twoPathDefect q c p = (0, c * (q - 1) * p.1) := by
  simp [twoPathDefect, Prod.ext_iff]
  ring

@[simp] theorem rotDefect_apply (q c : R) (p : R × R) :
    rotDefect q c p = (c * (q - 1) * p.1, 0) := by
  simp [rotDefect]

/-- The wall submodule `I R² ⊆ R²` for the principal wall ideal `I = (q-1)`. -/
def wallSquare (q : R) : Submodule R (R × R) :=
  Submodule.prod (Ideal.span {q - 1} : Ideal R) (Ideal.span {q - 1} : Ideal R)

theorem mem_wallSquare {q : R} {p : R × R} :
    p ∈ wallSquare q ↔ (∃ x, p.1 = (q - 1) * x) ∧ ∃ y, p.2 = (q - 1) * y := by
  simp only [wallSquare, Submodule.mem_prod, Ideal.mem_span_singleton, dvd_def]

/-- The minimal `T_q`-stable boundary `B_min = im Δ_q + im (T_q Δ_q)`. -/
def minStableBoundary (q c : R) : Submodule R (R × R) :=
  LinearMap.range (twoPathDefect q c) ⊔ LinearMap.range (rotDefect q c)

/-- The incompatibility module `Q = U / B_min`. -/
abbrev incompatModule (q c : R) : Type u := (R × R) ⧸ minStableBoundary q c

variable (q c : R)

theorem range_twoPathDefect :
    LinearMap.range (twoPathDefect q c) =
      Submodule.prod (⊥ : Submodule R R) (Ideal.span {c * (q - 1)} : Ideal R) := by
  ext p
  simp only [LinearMap.mem_range, Submodule.mem_prod, Submodule.mem_bot,
    Ideal.mem_span_singleton, twoPathDefect_apply, Prod.ext_iff, dvd_def]
  constructor
  · rintro ⟨w, h1, h2⟩
    exact ⟨h1.symm, ⟨w.1, h2.symm⟩⟩
  · rintro ⟨h1, d, h2⟩
    exact ⟨(d, 0), h1.symm, h2.symm⟩

theorem range_rotDefect :
    LinearMap.range (rotDefect q c) =
      Submodule.prod (Ideal.span {c * (q - 1)} : Ideal R) (⊥ : Submodule R R) := by
  ext p
  simp only [LinearMap.mem_range, Submodule.mem_prod, Submodule.mem_bot,
    Ideal.mem_span_singleton, rotDefect_apply, Prod.ext_iff, dvd_def]
  constructor
  · rintro ⟨w, h1, h2⟩
    exact ⟨⟨w.1, h1.symm⟩, h2.symm⟩
  · rintro ⟨⟨d, h1⟩, h2⟩
    exact ⟨(d, 0), h1.symm, h2.symm⟩

/-- **The minimal stable boundary is the full wall ideal in both legs.**  With `c` a unit,
`B_min = I R²` where `I = (q-1)`. -/
theorem minStableBoundary_eq (hc : IsUnit c) :
    minStableBoundary q c = wallSquare q := by
  have hspan : (Ideal.span {c * (q - 1)} : Ideal R) = Ideal.span {q - 1} := by
    rw [mul_comm]
    exact Ideal.span_singleton_mul_right_unit hc _
  rw [minStableBoundary, range_twoPathDefect, range_rotDefect, hspan, wallSquare,
    Submodule.prod_sup_prod, bot_sup_eq, sup_bot_eq]

/-- Multiplication by the wall equation on `U = R²`, the presentation map `(q-1)·id₂`. -/
def wallSmul : (R × R) →ₗ[R] (R × R) := (q - 1) • LinearMap.id

@[simp] theorem wallSmul_apply (p : R × R) :
    wallSmul q p = ((q - 1) * p.1, (q - 1) * p.2) := by
  simp [wallSmul, Prod.smul_def, smul_eq_mul]

/-- **The presentation `R² --(q-1)·id--> R² → Q → 0`.**  The range of the presentation map is the
wall submodule, hence (for `c` a unit) the minimal stable boundary. -/
theorem range_wallSmul : LinearMap.range (wallSmul q) = wallSquare q := by
  ext p
  simp only [LinearMap.mem_range, mem_wallSquare, wallSmul_apply, Prod.ext_iff]
  constructor
  · rintro ⟨w, h1, h2⟩
    exact ⟨⟨w.1, h1.symm⟩, ⟨w.2, h2.symm⟩⟩
  · rintro ⟨⟨x, h1⟩, ⟨y, h2⟩⟩
    exact ⟨(x, y), h1.symm, h2.symm⟩

theorem range_wallSmul_eq_minStableBoundary (hc : IsUnit c) :
    LinearMap.range (wallSmul q) = minStableBoundary q c := by
  rw [range_wallSmul, minStableBoundary_eq q c hc]

/-- The coordinatewise reduction `R² → (R/I)²`. -/
def coordReduce : (R × R) →ₗ[R] (R ⧸ Ideal.span {q - 1}) × (R ⧸ Ideal.span {q - 1}) :=
  LinearMap.prodMap (Ideal.span {q - 1} : Ideal R).mkQ (Ideal.span {q - 1} : Ideal R).mkQ

theorem coordReduce_surjective : Function.Surjective (coordReduce q) := by
  rintro ⟨a, b⟩
  obtain ⟨x, rfl⟩ := (Ideal.span {q - 1} : Ideal R).mkQ_surjective a
  obtain ⟨y, rfl⟩ := (Ideal.span {q - 1} : Ideal R).mkQ_surjective b
  exact ⟨(x, y), rfl⟩

theorem ker_coordReduce : LinearMap.ker (coordReduce q) = wallSquare q := by
  rw [coordReduce, LinearMap.ker_prodMap, Submodule.ker_mkQ, wallSquare]

/-- **The Cartier incompatibility theorem.**  With `c` a unit, quotienting `U = R²` by the minimal
stable boundary gives `Q ≅ (R/I)²`, rank-two torsion on the wall `I = (q-1)`. -/
noncomputable def incompatEquiv (hc : IsUnit c) :
    incompatModule q c ≃ₗ[R]
      (R ⧸ Ideal.span {q - 1} : Type u) × (R ⧸ Ideal.span {q - 1} : Type u) :=
  (Submodule.quotEquivOfEq _ _
      (by rw [minStableBoundary_eq q c hc, ← ker_coordReduce q])).trans
    (LinearMap.quotKerEquivOfSurjective _ (coordReduce_surjective q))

/-- **The annihilator of the incompatibility module is the wall ideal.** -/
theorem annihilator_incompatModule (hc : IsUnit c) :
    Module.annihilator R (incompatModule q c) = Ideal.span {q - 1} := by
  rw [(incompatEquiv q c hc).annihilator_eq, Module.annihilator_prod,
    Ideal.annihilator_quotient, inf_idem]

end General

section Monodromy

open LaurentPolynomial

variable {k : Type u} [Field k] (c : MonodromyRing k)

theorem wallSquare_monodromy :
    wallSquare (monodromyParam k) =
      Submodule.prod (identityIdeal k) (identityIdeal k) := by
  rw [wallSquare, identityIdeal, wallEquation]

/-- **Theorem 3.1, boundary half, on the universal monodromy line.**  `B_min = I R²`. -/
theorem monodromy_minStableBoundary_eq (hc : IsUnit c) :
    minStableBoundary (monodromyParam k) c =
      Submodule.prod (identityIdeal k) (identityIdeal k) := by
  rw [minStableBoundary_eq (monodromyParam k) c hc, wallSquare_monodromy]

/-- **Theorem 3.1, quotient half, on the universal monodromy line.**  `Q ≅ (R/I)²`. -/
noncomputable def monodromyIncompatEquiv (hc : IsUnit c) :
    incompatModule (monodromyParam k) c ≃ₗ[MonodromyRing k]
      (MonodromyRing k ⧸ identityIdeal k) × (MonodromyRing k ⧸ identityIdeal k) :=
  incompatEquiv (monodromyParam k) c hc

/-- **Theorem 3.2, annihilator half.**  `Ann_R Q = I`. -/
theorem monodromy_annihilator_incompatModule (hc : IsUnit c) :
    Module.annihilator (MonodromyRing k) (incompatModule (monodromyParam k) c) =
      identityIdeal k :=
  annihilator_incompatModule (monodromyParam k) c hc

end Monodromy

end GaloisForLFunctions.HTGeometry.DerivedSelection
