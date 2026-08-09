import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Stable-primitive exactness

Fix one degree of a cochain complex of modules: a differential `d : A →ₗ B` whose image lands
inside a submodule `Z ≤ B` of cocycles.  An *observer* declares a submodule `S ≤ A` of admissible
primitives, and the resulting degree-`n` stable-primitive group is

`Hₛ = Z / d S`.

Taking `S = ⊤` recovers ordinary cohomology `H = Z / d A`, so the comparison map is the special
case `S ≤ ⊤` of the general monotone comparison.

This file proves the algebraic core:

* the canonical short exact sequence
  `0 → A / (S ⊔ ker d) → Z / d S → Z / d A → 0`;
* the three-gate solvability criterion: a chain has a primitive inside `S` exactly when it is a
  cocycle, is an ordinary coboundary, and one (hence any) ordinary primitive lies in `S ⊔ ker d`;
* the comparison sequence `0 → d T / d S → Z / d S → Z / d T → 0` for `S ≤ T`, its compatibility
  with the ordinary projection, and the resulting immortality of classes with nonzero ordinary
  image.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

universe u v w

variable {R : Type u} [Ring R]
variable {A : Type v} [AddCommGroup A] [Module R A]
variable {B : Type w} [AddCommGroup B] [Module R B]

/-- One degree of a cochain complex: a differential together with the submodule of cocycles of the
target degree, which must contain the image of the differential. -/
structure CochainSlice (R : Type u) (A : Type v) (B : Type w) [Ring R] [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] where
  /-- The coboundary operator `C^{n-1} → C^n`. -/
  d : A →ₗ[R] B
  /-- The cocycles `Z^n ≤ C^n`. -/
  cocycles : Submodule R B
  /-- Coboundaries are cocycles. -/
  range_le : LinearMap.range d ≤ cocycles

namespace CochainSlice

variable (X : CochainSlice R A B)

/-- The differential corestricted to the cocycles. -/
def dRes : A →ₗ[R] X.cocycles :=
  X.d.codRestrict X.cocycles fun a => X.range_le ⟨a, rfl⟩

@[simp] theorem coe_dRes (a : A) : ((X.dRes a : X.cocycles) : B) = X.d a := rfl

@[simp] theorem ker_dRes : LinearMap.ker X.dRes = LinearMap.ker X.d :=
  LinearMap.ker_codRestrict _ _ _

/-- The stable coboundaries `d S`, viewed inside the cocycles. -/
def stableBoundary (S : Submodule R A) : Submodule R X.cocycles :=
  Submodule.map X.dRes S

theorem mem_stableBoundary_iff {S : Submodule R A} {z : X.cocycles} :
    z ∈ X.stableBoundary S ↔ ∃ a ∈ S, X.d a = (z : B) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, Subtype.ext h⟩

theorem stableBoundary_mono {S T : Submodule R A} (h : S ≤ T) :
    X.stableBoundary S ≤ X.stableBoundary T :=
  Submodule.map_mono h

@[simp] theorem stableBoundary_top : X.stableBoundary ⊤ = LinearMap.range X.dRes :=
  Submodule.map_top _

/-- The image of the stable coboundaries in the ambient degree, i.e. `d S ≤ C^n`. -/
theorem coe_stableBoundary (S : Submodule R A) :
    Submodule.map X.cocycles.subtype (X.stableBoundary S) = Submodule.map X.d S := by
  ext b
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, ha, hb⟩ := X.mem_stableBoundary_iff.1 hz
    exact ⟨a, ha, hb⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨X.dRes a, ⟨a, ha, rfl⟩, rfl⟩

/-- The degree-`n` stable-primitive group `Z^n / d S`.  With `S = ⊤` this is ordinary
cohomology. -/
abbrev StableH (S : Submodule R A) := X.cocycles ⧸ X.stableBoundary S

/-- Ordinary cohomology `H^n = Z^n / d C^{n-1}`, the stable group of the totally unconstrained
observer. -/
abbrev OrdinaryH := X.StableH (⊤ : Submodule R A)

/-! ## The comparison map along observer strengthening -/

/-- Quotienting by a larger space of stable coboundaries. -/
def compare {S T : Submodule R A} (h : S ≤ T) : X.StableH S →ₗ[R] X.StableH T :=
  Submodule.mapQ _ _ LinearMap.id (by
    simpa using X.stableBoundary_mono h)

@[simp] theorem compare_mk {S T : Submodule R A} (h : S ≤ T) (z : X.cocycles) :
    X.compare h (Submodule.Quotient.mk z) = Submodule.Quotient.mk z := rfl

theorem compare_surjective {S T : Submodule R A} (h : S ≤ T) :
    Function.Surjective (X.compare h) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk z, rfl⟩

/-- The projection to ordinary cohomology. -/
def toOrdinary (S : Submodule R A) : X.StableH S →ₗ[R] X.OrdinaryH := X.compare (le_top (a := S))

@[simp] theorem toOrdinary_mk (S : Submodule R A) (z : X.cocycles) :
    X.toOrdinary S (Submodule.Quotient.mk z) = Submodule.Quotient.mk z := rfl

theorem toOrdinary_surjective (S : Submodule R A) : Function.Surjective (X.toOrdinary S) :=
  X.compare_surjective _

/-- Comparison maps compose: strengthening the observer in two steps agrees with doing it at
once. -/
theorem compare_comp_compare {S T U : Submodule R A} (h₁ : S ≤ T) (h₂ : T ≤ U) :
    (X.compare h₂).comp (X.compare h₁) = X.compare (h₁.trans h₂) := by
  ext z
  rfl

/-- Comparison is compatible with the ordinary projection: `p_{o'} ∘ q_{oo'} = p_o`. -/
theorem toOrdinary_comp_compare {S T : Submodule R A} (h : S ≤ T) :
    (X.toOrdinary T).comp (X.compare h) = X.toOrdinary S :=
  X.compare_comp_compare h le_top

/-! ## The obstruction group and the short exact sequence -/

/-- The primitive-obstruction group `C^{n-1} / (S + Z^{n-1})`. -/
abbrev PrimitiveObstruction (S : Submodule R A) := A ⧸ (S ⊔ LinearMap.ker X.d)

theorem ker_mkQ_comp_dRes (S : Submodule R A) :
    LinearMap.ker ((X.stableBoundary S).mkQ.comp X.dRes) = S ⊔ LinearMap.ker X.d := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  simpa [stableBoundary] using Submodule.comap_map_eq X.dRes S

/-- The connecting map `[a] ↦ [d a]` of the stable-primitive sequence. -/
def dbar (S : Submodule R A) : X.PrimitiveObstruction S →ₗ[R] X.StableH S :=
  Submodule.liftQ _ ((X.stableBoundary S).mkQ.comp X.dRes)
    (le_of_eq (X.ker_mkQ_comp_dRes S).symm)

@[simp] theorem dbar_mk (S : Submodule R A) (a : A) :
    X.dbar S (Submodule.Quotient.mk a) = Submodule.Quotient.mk (X.dRes a) := rfl

/-- **Injectivity of the connecting map.**  If `d a` is a stable coboundary then `a` differs from a
stable primitive by a cocycle. -/
theorem dbar_injective (S : Submodule R A) : Function.Injective (X.dbar S) := by
  rw [← LinearMap.ker_eq_bot]
  rw [dbar, Submodule.ker_liftQ]
  rw [X.ker_mkQ_comp_dRes S]
  refine (Submodule.eq_bot_iff _).2 ?_
  rintro x ⟨a, ha, rfl⟩
  exact (Submodule.Quotient.mk_eq_zero _).2 ha

/-- **Exactness in the middle.**  A stable class dies ordinarily exactly when it comes from a
primitive obstruction. -/
theorem range_dbar (S : Submodule R A) :
    LinearMap.range (X.dbar S) = LinearMap.ker (X.toOrdinary S) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [LinearMap.mem_ker, X.dbar_mk S a, X.toOrdinary_mk S]
    rw [Submodule.Quotient.mk_eq_zero]
    exact X.stableBoundary_top ▸ LinearMap.mem_range_self _ a
  · intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, X.toOrdinary_mk S, Submodule.Quotient.mk_eq_zero,
      X.stableBoundary_top] at hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨Submodule.Quotient.mk a, by rw [X.dbar_mk S a, ha]⟩

/-- **The stable-primitive short exact sequence.**
`0 → C^{n-1}/(S + Z^{n-1}) → Z^n/dS → H^n → 0`. -/
theorem stable_shortExact (S : Submodule R A) :
    Function.Injective (X.dbar S) ∧
      LinearMap.range (X.dbar S) = LinearMap.ker (X.toOrdinary S) ∧
        Function.Surjective (X.toOrdinary S) :=
  ⟨X.dbar_injective S, X.range_dbar S, X.toOrdinary_surjective S⟩

/-! ## The three-gate solvability criterion -/

/-- Any two ordinary primitives of the same chain give the same obstruction class: they differ by a
cocycle. -/
theorem mem_sup_ker_congr {S : Submodule R A} {a a' : A} (h : X.d a = X.d a') :
    a ∈ S ⊔ LinearMap.ker X.d ↔ a' ∈ S ⊔ LinearMap.ker X.d := by
  have hmem : a - a' ∈ S ⊔ LinearMap.ker X.d := by
    refine Submodule.mem_sup_right ?_
    simp [LinearMap.mem_ker, map_sub, h]
  constructor
  · intro ha
    simpa using Submodule.sub_mem _ ha hmem
  · intro ha'
    simpa using Submodule.add_mem _ ha' hmem

/-- **Three-gate criterion.**  A chain `c` has a primitive inside the stable subspace `S` exactly
when: it is a cocycle, its ordinary class vanishes, and its obstruction class vanishes.  The last
gate does not depend on the chosen ordinary primitive. -/
theorem mem_map_d_iff (S : Submodule R A) (c : B) :
    c ∈ Submodule.map X.d S ↔
      c ∈ X.cocycles ∧ c ∈ LinearMap.range X.d ∧
        ∀ a : A, X.d a = c → a ∈ S ⊔ LinearMap.ker X.d := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨X.range_le ⟨s, rfl⟩, ⟨s, rfl⟩, ?_⟩
    intro a ha
    exact (X.mem_sup_ker_congr (S := S) ha).2 (Submodule.mem_sup_left hs)
  · rintro ⟨-, ⟨a, rfl⟩, hgate⟩
    obtain ⟨s, hs, z, hz, hsz⟩ := Submodule.mem_sup.1 (hgate a rfl)
    refine ⟨s, hs, ?_⟩
    have : X.d s + X.d z = X.d a := by rw [← map_add, hsz]
    rw [LinearMap.mem_ker] at hz
    simpa [hz] using this

/-! ## The comparison short exact sequence -/

/-- **Kernel of the comparison map.**  Strengthening from `S` to `T` kills exactly the classes
represented by `d T`. -/
theorem ker_compare {S T : Submodule R A} (h : S ≤ T) :
    LinearMap.ker (X.compare h) = Submodule.map (X.stableBoundary S).mkQ (X.stableBoundary T) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, X.compare_mk h z, Submodule.Quotient.mk_eq_zero] at hx
    exact ⟨z, hx, rfl⟩
  · rintro x ⟨z, hz, rfl⟩
    rw [LinearMap.mem_ker]
    show X.compare h (Submodule.Quotient.mk z) = 0
    rw [X.compare_mk h z, Submodule.Quotient.mk_eq_zero]
    exact hz

/-- The kernel of the comparison map is canonically `d T / d S`. -/
noncomputable def compareKernelEquiv {S T : Submodule R A} (h : S ≤ T) :
    (X.stableBoundary T ⧸
        Submodule.comap (X.stableBoundary T).subtype (X.stableBoundary S)) ≃ₗ[R]
      LinearMap.ker (X.compare h) := by
  classical
  refine (Submodule.quotEquivOfEq _ _ ?_).trans
    (((X.stableBoundary S).mkQ.comp (X.stableBoundary T).subtype).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ ?_))
  · rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  · rw [LinearMap.range_comp, Submodule.range_subtype, X.ker_compare h]

/-- **The comparison short exact sequence.**
`0 → dT/dS → Z^n/dS → Z^n/dT → 0`. -/
theorem compare_shortExact {S T : Submodule R A} (h : S ≤ T) :
    LinearMap.ker (X.compare h) = Submodule.map (X.stableBoundary S).mkQ (X.stableBoundary T) ∧
      Function.Surjective (X.compare h) :=
  ⟨X.ker_compare h, X.compare_surjective h⟩

/-- **Immortality.**  A stable class whose ordinary image is nonzero survives every observer
strengthening. -/
theorem compare_ne_zero_of_toOrdinary_ne_zero {S T : Submodule R A} (h : S ≤ T)
    {x : X.StableH S} (hx : X.toOrdinary S x ≠ 0) : X.compare h x ≠ 0 := by
  intro hzero
  apply hx
  rw [← X.toOrdinary_comp_compare h]
  simp [hzero]

/-- Ordinary classes are observer-immortal: the ordinary image is unchanged along the whole
observer poset. -/
theorem toOrdinary_compare {S T : Submodule R A} (h : S ≤ T) (x : X.StableH S) :
    X.toOrdinary T (X.compare h x) = X.toOrdinary S x :=
  congrArg (fun f => f x) (X.toOrdinary_comp_compare h)

end CochainSlice

end GaloisForLFunctions.HTGeometry.Interfinity
