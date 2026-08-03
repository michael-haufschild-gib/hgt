import Mathlib.Tactic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Exact.Basic

/-!
# Algebraic core of Shilov boundary migration

This module formalizes the exact quotient calculus underlying escape and deficit defects for
operator-system complete quotient maps.  Analytically, the submodules below are the underlying
complex-linear spaces of Shilov ideals and the linear maps are induced by universal-cover
`*`-homomorphisms.  No operator-system or positivity axiom is introduced here.

The main results are:

* `escapeDefect_subsingleton_iff` and `deficitDefect_subsingleton_iff`: exact zero-defect criteria;
* `exists_entrywise_matrix_lift`: deficit-free maps lift every finite matrix entrywise;
* `escapeDetectionEquiv`: a representation whose kernel is the target Shilov ideal detects the
  escape defect faithfully;
* `deficitComposition_exact`: the canonical right-exact composition law for deficits;
* `exists_coherent_representatives`: recursive correction of compatible quotient classes in a
  countable inverse system.

These statements are the algebraic, non-topological proof obligations in Theorems A, B, and D of
`docs/drafts/pipeline/2-fully-proven/spectral-boundary-migration-shilov-exactness.md`.
-/

open Function

namespace GaloisForLFunctions.HTGeometry
namespace BoundaryMigration

universe u v

variable {𝕜 : Type u} [Field 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V]

/-- Quotient `M / (L ∩ M)`, expressed intrinsically inside `M`. -/
abbrev RelativeQuotient (L M : Submodule 𝕜 V) : Type v :=
  M ⧸ L.comap M.subtype

/-- Inclusion-induced map `M / (L ∩ M) → N / (L ∩ N)`. -/
def relativeInclusion {L M N : Submodule 𝕜 V} (hMN : M ≤ N) :
    RelativeQuotient L M →ₗ[𝕜] RelativeQuotient L N :=
  (L.comap M.subtype).mapQ (L.comap N.subtype)
    (Submodule.inclusion hMN) (by
      intro x hx
      rw [Submodule.mem_comap] at hx ⊢
      exact hx)

/-- Canonical projection `N / (L ∩ N) → N / (M ∩ N)` when `L ≤ M`. -/
def relativeProjection {L M N : Submodule 𝕜 V} (hLM : L ≤ M) :
    RelativeQuotient L N →ₗ[𝕜] RelativeQuotient M N :=
  (L.comap N.subtype).mapQ (M.comap N.subtype) LinearMap.id (by
    intro x hx
    rw [Submodule.mem_comap] at hx ⊢
    exact hLM hx)

theorem relativeInclusion_apply_mk {L M N : Submodule 𝕜 V} (hMN : M ≤ N) (x : M) :
    relativeInclusion (L := L) hMN
        ((Submodule.Quotient.mk x) : RelativeQuotient L M) =
      ((Submodule.Quotient.mk (⟨x, hMN x.2⟩ : N)) : RelativeQuotient L N) := by
  rfl

theorem relativeProjection_apply_mk {L M N : Submodule 𝕜 V} (hLM : L ≤ M) (x : N) :
    relativeProjection (N := N) hLM
        ((Submodule.Quotient.mk x) : RelativeQuotient L N) =
      ((Submodule.Quotient.mk x) : RelativeQuotient M N) := by
  rfl

/-- For `L ≤ M ≤ N`, the canonical sequence `M/L → N/L → N/M` is exact. -/
theorem relative_exact {L M N : Submodule 𝕜 V} (hLM : L ≤ M) (hMN : M ≤ N) :
    Function.Exact (relativeInclusion (L := L) hMN)
      (relativeProjection (N := N) hLM) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    constructor
    · intro hy
      rw [relativeProjection_apply_mk, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap] at hy
      refine ⟨((Submodule.Quotient.mk (⟨y, hy⟩ : M)) : RelativeQuotient L M), ?_⟩
      rw [relativeInclusion_apply_mk (L := L) (M := M) (N := N)]
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [relativeInclusion_apply_mk (L := L) (M := M) (N := N)] at hx
        rw [← hx, relativeProjection_apply_mk (L := L) (M := M) (N := N),
          Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
        exact x.2

section Defects

variable {W : Type v} [AddCommGroup W] [Module 𝕜 W]

/-- Source boundary mass that survives outside the target boundary ideal. -/
abbrev EscapeDefect (f : V →ₗ[𝕜] W) (Jsource : Submodule 𝕜 V)
    (Jtarget : Submodule 𝕜 W) : Type v :=
  RelativeQuotient Jtarget (Jsource.map f)

/-- Target boundary mass not reached by source boundary lifts. -/
abbrev DeficitDefect (f : V →ₗ[𝕜] W) (Jsource : Submodule 𝕜 V)
    (Jtarget : Submodule 𝕜 W) : Type v :=
  RelativeQuotient (Jsource.map f) Jtarget

/-- Source boundary ideal maps into the target boundary ideal. -/
def EscapeFree (f : V →ₗ[𝕜] W) (Jsource : Submodule 𝕜 V)
    (Jtarget : Submodule 𝕜 W) : Prop :=
  Jsource.map f ≤ Jtarget

/-- Every target boundary direction has a source boundary lift. -/
def DeficitFree (f : V →ₗ[𝕜] W) (Jsource : Submodule 𝕜 V)
    (Jtarget : Submodule 𝕜 W) : Prop :=
  Jtarget ≤ Jsource.map f

theorem escapeDefect_subsingleton_iff (f : V →ₗ[𝕜] W)
    (Jsource : Submodule 𝕜 V) (Jtarget : Submodule 𝕜 W) :
    Subsingleton (EscapeDefect f Jsource Jtarget) ↔
      EscapeFree f Jsource Jtarget := by
  rw [Submodule.Quotient.subsingleton_iff]
  constructor
  · intro h x hx
    have hx' : (⟨x, hx⟩ : Jsource.map f) ∈
        Jtarget.comap (Jsource.map f).subtype := by
      rw [h]
      exact Submodule.mem_top
    exact Submodule.mem_comap.mp hx'
  · intro h
    apply top_unique
    intro x _
    exact Submodule.mem_comap.mpr (h x.2)

theorem deficitDefect_subsingleton_iff (f : V →ₗ[𝕜] W)
    (Jsource : Submodule 𝕜 V) (Jtarget : Submodule 𝕜 W) :
    Subsingleton (DeficitDefect f Jsource Jtarget) ↔
      DeficitFree f Jsource Jtarget := by
  rw [Submodule.Quotient.subsingleton_iff]
  constructor
  · intro h x hx
    have hx' : (⟨x, hx⟩ : Jtarget) ∈
        (Jsource.map f).comap Jtarget.subtype := by
      rw [h]
      exact Submodule.mem_top
    exact Submodule.mem_comap.mp hx'
  · intro h
    apply top_unique
    intro x _
    exact Submodule.mem_comap.mpr (h x.2)

theorem escapeFree_and_deficitFree_iff (f : V →ₗ[𝕜] W)
    (Jsource : Submodule 𝕜 V) (Jtarget : Submodule 𝕜 W) :
    EscapeFree f Jsource Jtarget ∧ DeficitFree f Jsource Jtarget ↔
      Jsource.map f = Jtarget := by
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

theorem deficitFree_iff_exact_lifts (f : V →ₗ[𝕜] W)
    (Jsource : Submodule 𝕜 V) (Jtarget : Submodule 𝕜 W) :
    DeficitFree f Jsource Jtarget ↔
      ∀ y, y ∈ Jtarget → ∃ x, x ∈ Jsource ∧ f x = y := by
  constructor
  · intro h y hy
    exact Submodule.mem_map.mp (h hy)
  · intro h y hy
    exact Submodule.mem_map.mpr (h y hy)

/-- Exact boundary lifts persist entrywise at every matrix size. -/
theorem exists_entrywise_matrix_lift {n : Type*}
    (f : V →ₗ[𝕜] W) (Jsource : Submodule 𝕜 V)
    (Jtarget : Submodule 𝕜 W)
    (h : DeficitFree f Jsource Jtarget)
    (b : Matrix n n W) (hb : ∀ i j, b i j ∈ Jtarget) :
    ∃ a : Matrix n n V,
      (∀ i j, a i j ∈ Jsource) ∧
      ∀ i j, f (a i j) = b i j := by
  classical
  have hlift : ∀ i j, ∃ x, x ∈ Jsource ∧ f x = b i j :=
    fun i j => (deficitFree_iff_exact_lifts f Jsource Jtarget).mp h _ (hb i j)
  let a : Matrix n n V := fun i j => Classical.choose (hlift i j)
  exact ⟨a,
    fun i j => (Classical.choose_spec (hlift i j)).1,
    fun i j => (Classical.choose_spec (hlift i j)).2⟩

variable {Z : Type v} [AddCommGroup Z] [Module 𝕜 Z]

/-- First-isomorphism detection of escape by a representation with target boundary kernel. -/
noncomputable def escapeDetectionEquiv (f : V →ₗ[𝕜] W)
    (Jsource : Submodule 𝕜 V) (Jtarget : Submodule 𝕜 W)
    (ρ : W →ₗ[𝕜] Z) (hker : LinearMap.ker ρ = Jtarget) :
    EscapeDefect f Jsource Jtarget ≃ₗ[𝕜]
      LinearMap.range (ρ.domRestrict (Jsource.map f)) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    simp only [Submodule.mem_comap, LinearMap.mem_ker]
    change (x : W) ∈ Jtarget ↔ ρ x = 0
    rw [← hker, LinearMap.mem_ker])).trans
    (ρ.domRestrict (Jsource.map f)).quotKerEquivRange

end Defects

section Composition

variable {W X : Type v}
variable [AddCommGroup W] [Module 𝕜 W]
variable [AddCommGroup X] [Module 𝕜 X]

theorem compositeImage_le (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] X)
    (Jsource : Submodule 𝕜 V) (Jmiddle : Submodule 𝕜 W)
    (h : EscapeFree f Jsource Jmiddle) :
    Jsource.map (g.comp f) ≤ Jmiddle.map g := by
  rw [Submodule.map_comp]
  exact Submodule.map_mono h

/-- Map from a first-link deficit to the composite deficit. -/
def deficitPushforward (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] X)
    (Jsource : Submodule 𝕜 V) (Jmiddle : Submodule 𝕜 W)
    (Jtarget : Submodule 𝕜 X)
    (hr : EscapeFree g Jmiddle Jtarget) :
    DeficitDefect f Jsource Jmiddle →ₗ[𝕜]
      DeficitDefect (g.comp f) Jsource Jtarget :=
  let gJ : Jmiddle →ₗ[𝕜] Jtarget :=
    (g.comp Jmiddle.subtype).codRestrict Jtarget
      (fun x => hr (Submodule.mem_map_of_mem x.2))
  ((Jsource.map f).comap Jmiddle.subtype).mapQ
    ((Jsource.map (g.comp f)).comap Jtarget.subtype) gJ (by
      intro x hx
      rw [Submodule.mem_comap] at hx ⊢
      change g x.1 ∈ Jsource.map (g.comp f)
      rcases Submodule.mem_map.mp hx with ⟨a, ha, hfa⟩
      exact Submodule.mem_map.mpr ⟨a, ha, by simp [hfa]⟩)

theorem deficitPushforward_apply_mk (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] X)
    (Jsource : Submodule 𝕜 V) (Jmiddle : Submodule 𝕜 W)
    (Jtarget : Submodule 𝕜 X)
    (hr : EscapeFree g Jmiddle Jtarget) (x : Jmiddle) :
    deficitPushforward f g Jsource Jmiddle Jtarget hr
        ((Submodule.Quotient.mk x) : DeficitDefect f Jsource Jmiddle) =
      ((Submodule.Quotient.mk
        (⟨g x, hr (Submodule.mem_map_of_mem x.2)⟩ : Jtarget)) :
        DeficitDefect (g.comp f) Jsource Jtarget) := by
  rfl

/-- Projection from the composite deficit onto the second-link deficit. -/
def deficitCompositionProjection (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] X)
    (Jsource : Submodule 𝕜 V) (Jmiddle : Submodule 𝕜 W)
    (Jtarget : Submodule 𝕜 X)
    (hq : EscapeFree f Jsource Jmiddle) :
    DeficitDefect (g.comp f) Jsource Jtarget →ₗ[𝕜]
      DeficitDefect g Jmiddle Jtarget :=
  relativeProjection (N := Jtarget)
    (compositeImage_le f g Jsource Jmiddle hq)

theorem deficitCompositionProjection_apply_mk
    (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] X)
    (Jsource : Submodule 𝕜 V) (Jmiddle : Submodule 𝕜 W)
    (Jtarget : Submodule 𝕜 X)
    (hq : EscapeFree f Jsource Jmiddle) (x : Jtarget) :
    deficitCompositionProjection f g Jsource Jmiddle Jtarget hq
        ((Submodule.Quotient.mk x) :
          DeficitDefect (g.comp f) Jsource Jtarget) =
      ((Submodule.Quotient.mk x) : DeficitDefect g Jmiddle Jtarget) := by
  rfl

/-- Right-exact deficit law for two composable escape-free boundary maps. -/
theorem deficitComposition_exact
    (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] X)
    (Jsource : Submodule 𝕜 V) (Jmiddle : Submodule 𝕜 W)
    (Jtarget : Submodule 𝕜 X)
    (hq : EscapeFree f Jsource Jmiddle)
    (hr : EscapeFree g Jmiddle Jtarget) :
    Function.Exact
      (deficitPushforward f g Jsource Jmiddle Jtarget hr)
      (deficitCompositionProjection f g Jsource Jmiddle Jtarget hq) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    constructor
    · intro hy
      rw [deficitCompositionProjection_apply_mk,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hy
      rcases Submodule.mem_map.mp hy with ⟨x, hx, hgx⟩
      let xJ : Jmiddle := ⟨x, hx⟩
      refine ⟨((Submodule.Quotient.mk xJ) :
        DeficitDefect f Jsource Jmiddle), ?_⟩
      rw [deficitPushforward_apply_mk]
      apply congrArg Submodule.Quotient.mk
      exact Subtype.ext hgx
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [deficitPushforward_apply_mk] at hx
        rw [← hx, deficitCompositionProjection_apply_mk,
          Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
        exact Submodule.mem_map_of_mem x.2

theorem deficitCompositionProjection_surjective
    (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] X)
    (Jsource : Submodule 𝕜 V) (Jmiddle : Submodule 𝕜 W)
    (Jtarget : Submodule 𝕜 X)
    (hq : EscapeFree f Jsource Jmiddle) :
    Function.Surjective
      (deficitCompositionProjection f g Jsource Jmiddle Jtarget hq) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- A first-link deficit class is erased precisely when its image already comes from source
boundary mass.  This is the elementwise form of the kernel formula in the paper. -/
theorem deficitPushforward_mk_eq_zero_iff
    (f : V →ₗ[𝕜] W) (g : W →ₗ[𝕜] X)
    (Jsource : Submodule 𝕜 V) (Jmiddle : Submodule 𝕜 W)
    (Jtarget : Submodule 𝕜 X)
    (hr : EscapeFree g Jmiddle Jtarget) (x : Jmiddle) :
    deficitPushforward f g Jsource Jmiddle Jtarget hr
        ((Submodule.Quotient.mk x) : DeficitDefect f Jsource Jmiddle) = 0 ↔
      ∃ z, z ∈ Jsource.map f ∧ g z = g x := by
  rw [deficitPushforward_apply_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.map_comp, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx⟩

end Composition

section CoherentLifting

variable (A : ℕ → Type v)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module 𝕜 (A n)]

/-- Linkwise surjectivity on boundary ideals corrects arbitrary compatible quotient classes to a
coherent sequence of representatives.  This is the constructive surjectivity step for the local
`C*`-envelope inverse-limit comparison; no uniform cross-stage norm bound is used. -/
theorem exists_coherent_representatives
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hlift : ∀ n (x : A n), x ∈ J n →
      ∃ y : A (n + 1), y ∈ J (n + 1) ∧ bond n y = x)
    (b : ∀ n, A n)
    (hmod : ∀ n, bond n (b (n + 1)) - b n ∈ J n) :
    ∃ a : ∀ n, A n,
      (∀ n, a n - b n ∈ J n) ∧
      ∀ n, bond n (a (n + 1)) = a n := by
  classical
  let C : ℕ → Type v := fun n => {x : A n // x - b n ∈ J n}
  let c0 : C 0 := ⟨b 0, by simp⟩
  let step : ∀ n, C n → C (n + 1) := fun n x => by
    have htarget : bond n (b (n + 1)) - x.1 ∈ J n := by
      have hx : x.1 - b n ∈ J n := x.2
      have := (J n).sub_mem (hmod n) hx
      (convert this using 1; abel)
    let d : A (n + 1) := Classical.choose (hlift n _ htarget)
    have hd : d ∈ J (n + 1) := (Classical.choose_spec (hlift n _ htarget)).1
    exact ⟨b (n + 1) - d, by
      have hneg : -d ∈ J (n + 1) := (J (n + 1)).neg_mem hd
      (convert hneg using 1; abel)⟩
  let c : ∀ n, C n := fun n => Nat.rec c0 (fun k x => step k x) n
  refine ⟨fun n => (c n).1, fun n => (c n).2, ?_⟩
  intro n
  change bond n ((c (n + 1)).1) = (c n).1
  rw [show c (n + 1) = step n (c n) by rfl]
  simp only [step]
  let target : A n := bond n (b (n + 1)) - (c n).1
  have htarget : target ∈ J n := by
    have hc : (c n).1 - b n ∈ J n := (c n).2
    have := (J n).sub_mem (hmod n) hc
    (convert this using 1; simp only [target]; abel)
  let d : A (n + 1) := Classical.choose (hlift n target htarget)
  have hdmap : bond n d = target :=
    (Classical.choose_spec (hlift n target htarget)).2
  change bond n (b (n + 1) - d) = (c n).1
  rw [map_sub, hdmap]
  simp only [target]
  abel

end CoherentLifting

end BoundaryMigration
end GaloisForLFunctions.HTGeometry
