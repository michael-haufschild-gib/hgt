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
* `stageBoundaryDerivedSequence_shortExact`: the literal universal derived inverse-limit law
  `0 → (lim Aₙ)/(lim Jₙ) → lim(Aₙ/Jₙ) → lim¹ Jₙ → 0`;
* `localBoundaryComparison_surjective_iff`: exactness of local descent is equivalent to vanishing
  of the global `lim¹` boundary obstruction;
* `zero_scalar_bond_global_vanishing`: linkwise cokernel defects need not obstruct global descent.

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

/-- Roos difference `1 - shift` for a countable inverse sequence.  Its kernel is the
inverse limit and its cokernel is the algebraic first derived inverse limit. -/
def inverseDifference (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) :
    (∀ n, A n) →ₗ[𝕜] (∀ n, A n) where
  toFun x n := x n - bond n (x (n + 1))
  map_add' x y := by
    funext n
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' c x := by
    funext n
    simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]

/-- Algebraic `lim¹` of a countable inverse sequence, presented as the cokernel of the
Roos difference. -/
abbrev DerivedLimitOne (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) : Type v :=
  (∀ n, A n) ⧸ LinearMap.range (inverseDifference A bond)

/-- Restriction of a bonding map to a compatible inverse sequence of submodules. -/
def restrictedBond (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) :
    ∀ n, J (n + 1) →ₗ[𝕜] J n :=
  fun n => ((bond n).domRestrict (J (n + 1))).codRestrict (J n)
    (fun x => hstable n x x.2)

/-- Boundary mismatch attached to arbitrary representatives of compatible quotient classes. -/
def boundaryMismatch (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (b : ∀ n, A n)
    (hmod : ∀ n, bond n (b (n + 1)) - b n ∈ J n) :
    ∀ n, J n :=
  fun n => ⟨bond n (b (n + 1)) - b n, hmod n⟩

/-- Sequences that are coherent modulo the designated boundary submodules. -/
def compatibleModuloSubmodule (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) : Submodule 𝕜 (∀ n, A n) where
  carrier := {b | ∀ n, bond n (b (n + 1)) - b n ∈ J n}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy n
    have h := (J n).add_mem (hx n) (hy n)
    convert h using 1
    simp only [Pi.add_apply, map_add]
    abel
  smul_mem' := by
    intro c x hx n
    have h := (J n).smul_mem c (hx n)
    convert h using 1
    simp only [Pi.smul_apply, map_smul, smul_sub]

/-- Coordinatewise product of boundary submodules. -/
abbrev productSubmodule (J : ∀ n, Submodule 𝕜 (A n)) :
    Submodule 𝕜 (∀ n, A n) :=
  Submodule.pi Set.univ J

/-- Boundary-valued representatives inside the space of sequences coherent modulo boundary. -/
def compatibleProductSubmodule (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    Submodule 𝕜 (compatibleModuloSubmodule A bond J) :=
  (productSubmodule A J).comap (compatibleModuloSubmodule A bond J).subtype

/-- Compatible quotient classes represented intrinsically as boundary-compatible sequences modulo
coordinatewise boundary perturbations. -/
abbrev CompatibleClassSpace (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) : Type v :=
  compatibleModuloSubmodule A bond J ⧸ compatibleProductSubmodule A bond J

/-- Bonding map induced on the stage boundary quotient. -/
def quotientBond (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) :
    ∀ n, (A (n + 1) ⧸ J (n + 1)) →ₗ[𝕜] (A n ⧸ J n) :=
  fun n => (J (n + 1)).mapQ (J n) (bond n) (by
    intro x hx
    exact hstable n x hx)

/-- Literal inverse limit of the stage boundary quotients. -/
abbrev StageQuotientInverseLimit
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) : Type v :=
  LinearMap.ker
    (inverseDifference (fun n => A n ⧸ J n) (quotientBond A bond J hstable))

/-- The intrinsic compatible-class model maps canonically to the literal inverse limit of stage
quotients. -/
def compatibleClassToStageLimit
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) :
    CompatibleClassSpace A bond J →ₗ[𝕜]
      StageQuotientInverseLimit A bond J hstable :=
  (compatibleProductSubmodule A bond J).liftQ
    ({
      toFun := fun b => ⟨fun n => Submodule.Quotient.mk (b.1 n), by
        funext n
        change ((Submodule.Quotient.mk (b.1 n)) : A n ⧸ J n) -
          ((Submodule.Quotient.mk (bond n (b.1 (n + 1)))) : A n ⧸ J n) = 0
        apply sub_eq_zero.mpr
        rw [Submodule.Quotient.eq]
        have hb := b.property
        change ∀ n, bond n (b.1 (n + 1)) - b.1 n ∈ J n at hb
        simpa only [neg_sub] using (J n).neg_mem (hb n)⟩
      map_add' := fun x y => by rfl
      map_smul' := fun c x => by rfl
    } : compatibleModuloSubmodule A bond J →ₗ[𝕜]
      StageQuotientInverseLimit A bond J hstable) (by
        intro x hx
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        funext n
        change Submodule.Quotient.mk (x.1 n) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        change x.1 ∈ productSubmodule A J at hx
        rw [Submodule.mem_pi] at hx
        exact hx n (Set.mem_univ n))

theorem compatibleClassToStageLimit_injective
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) :
    Function.Injective (compatibleClassToStageLimit A bond J hstable) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_bot]
    induction y using Submodule.Quotient.induction_on with
    | _ b =>
      change (⟨fun n => Submodule.Quotient.mk (b.1 n), _⟩ :
        StageQuotientInverseLimit A bond J hstable) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero]
      change b.1 ∈ productSubmodule A J
      rw [Submodule.mem_pi]
      intro n _
      have hn := congrArg Subtype.val hy
      have hn' := congrFun hn n
      change Submodule.Quotient.mk (b.1 n) = 0 at hn'
      rwa [Submodule.Quotient.mk_eq_zero] at hn'
  · exact bot_le

theorem compatibleClassToStageLimit_surjective
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) :
    Function.Surjective (compatibleClassToStageLimit A bond J hstable) := by
  classical
  intro z
  choose b hb using fun n => Submodule.Quotient.mk_surjective (J n) (z.1 n)
  have hmod : ∀ n, bond n (b (n + 1)) - b n ∈ J n := by
    intro n
    rw [← Submodule.Quotient.eq]
    have hn := congrFun z.property n
    change z.1 n - quotientBond A bond J hstable n (z.1 (n + 1)) = 0 at hn
    have hn' := sub_eq_zero.mp hn
    calc
      Submodule.Quotient.mk (bond n (b (n + 1))) =
          quotientBond A bond J hstable n (Submodule.Quotient.mk (b (n + 1))) := rfl
      _ = quotientBond A bond J hstable n (z.1 (n + 1)) := by rw [hb]
      _ = z.1 n := hn'.symm
      _ = Submodule.Quotient.mk (b n) := (hb n).symm
  let br : compatibleModuloSubmodule A bond J := ⟨b, hmod⟩
  refine ⟨Submodule.Quotient.mk br, ?_⟩
  apply Subtype.ext
  funext n
  exact hb n

/-- Canonical identification of the intrinsic representative model with
`lim (Aₙ / Jₙ)`. -/
noncomputable def compatibleClassEquivStageLimit
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) :
    CompatibleClassSpace A bond J ≃ₗ[𝕜]
      StageQuotientInverseLimit A bond J hstable :=
  LinearEquiv.ofBijective (compatibleClassToStageLimit A bond J hstable)
    ⟨compatibleClassToStageLimit_injective A bond J hstable,
      compatibleClassToStageLimit_surjective A bond J hstable⟩

/-- Linear boundary mismatch on the representative space. -/
def representativeBoundary (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    compatibleModuloSubmodule A bond J →ₗ[𝕜] (∀ n, J n) where
  toFun b n := ⟨bond n (b.1 (n + 1)) - b.1 n, by
    have hb := b.property
    change ∀ n, bond n (b.1 (n + 1)) - b.1 n ∈ J n at hb
    exact hb n⟩
  map_add' x y := by
    funext n
    apply Subtype.ext
    change bond n (x.1 (n + 1) + y.1 (n + 1)) - (x.1 n + y.1 n) =
      (bond n (x.1 (n + 1)) - x.1 n) + (bond n (y.1 (n + 1)) - y.1 n)
    rw [map_add]
    abel
  map_smul' c x := by
    funext n
    apply Subtype.ext
    change bond n (c • x.1 (n + 1)) - c • x.1 n =
      c • (bond n (x.1 (n + 1)) - x.1 n)
    simp only [map_smul, smul_sub]

/-- Connecting map from compatible quotient classes to the derived boundary obstruction. -/
def boundaryConnectingMap (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) :
    CompatibleClassSpace A bond J →ₗ[𝕜]
      DerivedLimitOne (fun n => J n) (restrictedBond A bond J hstable) :=
  (compatibleProductSubmodule A bond J).mapQ
    (LinearMap.range
      (inverseDifference (fun n => J n) (restrictedBond A bond J hstable)))
    (representativeBoundary A bond J) (by
      intro x hx
      change x.1 ∈ productSubmodule A J at hx
      rw [Submodule.mem_pi] at hx
      change representativeBoundary A bond J x ∈
        LinearMap.range
          (inverseDifference (fun n => J n) (restrictedBond A bond J hstable))
      let j : ∀ n, J n := fun n =>
        ⟨-x.1 n, (J n).neg_mem (hx n (Set.mem_univ n))⟩
      refine ⟨j, ?_⟩
      funext n
      apply Subtype.ext
      change (-x.1 n) - bond n (-x.1 (n + 1)) =
        bond n (x.1 (n + 1)) - x.1 n
      rw [map_neg]
      abel)

/-- Linear inverse limit, realized as the kernel of the Roos difference. -/
abbrev InverseLimit (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) : Type v :=
  LinearMap.ker (inverseDifference A bond)

/-- A coherent sequence is, in particular, coherent modulo every stable boundary system. -/
def coherentRepresentative (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    InverseLimit A bond →ₗ[𝕜] compatibleModuloSubmodule A bond J where
  toFun a := ⟨a.1, by
    intro n
    have hn := congrFun a.property n
    change a.1 n - bond n (a.1 (n + 1)) = 0 at hn
    have hzero : bond n (a.1 (n + 1)) - a.1 n = 0 := by
      rw [sub_eq_zero]
      exact (sub_eq_zero.mp hn).symm
    rw [hzero]
    exact (J n).zero_mem⟩
  map_add' x y := by rfl
  map_smul' c x := by rfl

/-- Natural map from coherent sequences to compatible boundary-quotient classes. -/
def coherentClassMap (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    InverseLimit A bond →ₗ[𝕜] CompatibleClassSpace A bond J :=
  (compatibleProductSubmodule A bond J).mkQ.comp
    (coherentRepresentative A bond J)

/-- Coherent boundary sequences, i.e. the inverse limit of the boundary submodules. -/
def inverseLimitBoundarySubmodule (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) : Submodule 𝕜 (InverseLimit A bond) :=
  (productSubmodule A J).comap (LinearMap.ker (inverseDifference A bond)).subtype

/-- Algebraic local boundary quotient `(lim Aₙ)/(lim Jₙ)`. -/
abbrev LocalBoundaryQuotient (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) : Type v :=
  InverseLimit A bond ⧸ inverseLimitBoundarySubmodule A bond J

/-- Canonical comparison from the local boundary quotient to compatible stage-quotient classes. -/
def localBoundaryComparison (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    LocalBoundaryQuotient A bond J →ₗ[𝕜] CompatibleClassSpace A bond J :=
  (inverseLimitBoundarySubmodule A bond J).liftQ
    (coherentClassMap A bond J) (by
      intro x hx
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk (coherentRepresentative A bond J x) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      change x.1 ∈ productSubmodule A J at hx
      change (coherentRepresentative A bond J x).1 ∈ productSubmodule A J
      exact hx)

/-- Canonical local boundary comparison with literal target `lim (Aₙ/Jₙ)`. -/
noncomputable def stageLocalBoundaryComparison
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) :
    LocalBoundaryQuotient A bond J →ₗ[𝕜]
      StageQuotientInverseLimit A bond J hstable :=
  (compatibleClassEquivStageLimit A bond J hstable).toLinearMap.comp
    (localBoundaryComparison A bond J)

/-- Derived boundary connecting map on the literal stage-quotient inverse limit. -/
noncomputable def stageBoundaryConnectingMap
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) :
    StageQuotientInverseLimit A bond J hstable →ₗ[𝕜]
      DerivedLimitOne (fun n => J n) (restrictedBond A bond J hstable) :=
  (boundaryConnectingMap A bond J hstable).comp
    (compatibleClassEquivStageLimit A bond J hstable).symm.toLinearMap

/-- The canonical comparison is always injective. -/
theorem localBoundaryComparison_injective
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    Function.Injective (localBoundaryComparison A bond J) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_bot]
    induction y using Submodule.Quotient.induction_on with
    | _ x =>
      change coherentClassMap A bond J x = 0 at hy
      change Submodule.Quotient.mk (coherentRepresentative A bond J x) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      rw [Submodule.Quotient.mk_eq_zero]
      change x.1 ∈ productSubmodule A J
      change (coherentRepresentative A bond J x).1 ∈ productSubmodule A J at hy
      exact hy
  · exact bot_le

/-- Representatives can be corrected to a coherent sequence exactly when their boundary
mismatch is a Roos coboundary.  This is the elementwise derived-limit obstruction law. -/
theorem exists_coherent_representatives_iff_mismatch_mem_range
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n)
    (b : ∀ n, A n)
    (hmod : ∀ n, bond n (b (n + 1)) - b n ∈ J n) :
    (∃ a : ∀ n, A n,
      (∀ n, a n - b n ∈ J n) ∧
      ∀ n, bond n (a (n + 1)) = a n) ↔
      boundaryMismatch A bond J b hmod ∈
        LinearMap.range
          (inverseDifference (fun n => J n)
            (restrictedBond A bond J hstable)) := by
  constructor
  · rintro ⟨a, haJ, hcoh⟩
    let j : ∀ n, J n := fun n => ⟨a n - b n, haJ n⟩
    refine ⟨j, ?_⟩
    funext n
    apply Subtype.ext
    change (a n - b n) - bond n (a (n + 1) - b (n + 1)) =
      bond n (b (n + 1)) - b n
    rw [map_sub, hcoh]
    abel
  · rintro ⟨j, hj⟩
    let a : ∀ n, A n := fun n => b n + j n
    refine ⟨a, ?_, ?_⟩
    · intro n
      have hjmem : (j n : A n) ∈ J n := (j n).2
      simpa only [a, add_sub_cancel_left] using hjmem
    · intro n
      have hn := congrFun hj n
      have hn' := congrArg Subtype.val hn
      change (j n : A n) - bond n (j (n + 1)) =
        bond n (b (n + 1)) - b n at hn'
      change bond n (b (n + 1) + j (n + 1)) = b n + j n
      rw [map_add]
      calc
        bond n (b (n + 1)) + bond n (j (n + 1)) =
            (bond n (b (n + 1)) - b n) + b n + bond n (j (n + 1)) := by
              abel
        _ = ((j n : A n) - bond n (j (n + 1))) + b n +
            bond n (j (n + 1)) := by rw [hn']
        _ = b n + j n := by abel

/-- Universal derived-limit law at the middle term: a compatible boundary-quotient class has
zero connecting class exactly when it comes from a coherent sequence. -/
theorem boundarySequence_exact
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) :
    Function.Exact (coherentClassMap A bond J)
      (boundaryConnectingMap A bond J hstable) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ b =>
    constructor
    · intro hy
      change Submodule.Quotient.mk (representativeBoundary A bond J b) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      have hmod : ∀ n, bond n (b.1 (n + 1)) - b.1 n ∈ J n := by
        have hb := b.property
        change ∀ n, bond n (b.1 (n + 1)) - b.1 n ∈ J n at hb
        exact hb
      have hmismatch : boundaryMismatch A bond J b.1 hmod ∈
          LinearMap.range
            (inverseDifference (fun n => J n)
              (restrictedBond A bond J hstable)) := by
        have heq : boundaryMismatch A bond J b.1 hmod =
            representativeBoundary A bond J b := by
          funext n
          apply Subtype.ext
          rfl
        rw [heq]
        exact hy
      rcases (exists_coherent_representatives_iff_mismatch_mem_range
        A bond J hstable b.1 hmod).mpr hmismatch with ⟨a, haJ, hcoh⟩
      have hker : inverseDifference A bond a = 0 := by
        funext n
        change a n - bond n (a (n + 1)) = 0
        rw [hcoh]
        exact sub_self _
      let aLim : InverseLimit A bond := ⟨a, hker⟩
      refine ⟨aLim, ?_⟩
      change Submodule.Quotient.mk (coherentRepresentative A bond J aLim) =
        Submodule.Quotient.mk b
      rw [Submodule.Quotient.eq]
      change (fun n => a n - b.1 n) ∈ productSubmodule A J
      rw [Submodule.mem_pi]
      intro n _
      exact haJ n
    · rintro ⟨a, ha⟩
      rw [← ha]
      change Submodule.Quotient.mk
        (representativeBoundary A bond J (coherentRepresentative A bond J a)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      have hzero : representativeBoundary A bond J
          (coherentRepresentative A bond J a) = 0 := by
        funext n
        apply Subtype.ext
        have hn := congrFun a.property n
        change a.1 n - bond n (a.1 (n + 1)) = 0 at hn
        change bond n (a.1 (n + 1)) - a.1 n = 0
        rw [sub_eq_zero]
        exact (sub_eq_zero.mp hn).symm
      rw [hzero]
      exact (LinearMap.range
        (inverseDifference (fun n => J n)
          (restrictedBond A bond J hstable))).zero_mem

/-- Exact derived Shilov-limit sequence
`0 → (lim Aₙ)/(lim Jₙ) → lim(Aₙ/Jₙ) → lim¹ Jₙ` in its intrinsic representative model. -/
theorem localBoundaryDerivedSequence_exact
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n) :
    Function.Exact (localBoundaryComparison A bond J)
      (boundaryConnectingMap A bond J hstable) := by
  intro y
  constructor
  · intro hy
    rcases (boundarySequence_exact A bond J hstable y).mp hy with ⟨a, ha⟩
    exact ⟨Submodule.Quotient.mk a, ha⟩
  · rintro ⟨z, hz⟩
    induction z using Submodule.Quotient.induction_on with
    | _ a =>
      apply (boundarySequence_exact A bond J hstable y).mpr
      exact ⟨a, hz⟩

/-- The canonical derived Shilov class of a compatible family of quotient representatives. -/
def boundaryObstruction (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n)
    (b : ∀ n, A n)
    (hmod : ∀ n, bond n (b (n + 1)) - b n ∈ J n) :
    DerivedLimitOne (fun n => J n) (restrictedBond A bond J hstable) :=
  Submodule.Quotient.mk (boundaryMismatch A bond J b hmod)

theorem boundaryObstruction_eq_zero_iff
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n)
    (b : ∀ n, A n)
    (hmod : ∀ n, bond n (b (n + 1)) - b n ∈ J n) :
    boundaryObstruction A bond J hstable b hmod = 0 ↔
      ∃ a : ∀ n, A n,
        (∀ n, a n - b n ∈ J n) ∧
        ∀ n, bond n (a (n + 1)) = a n := by
  rw [boundaryObstruction, Submodule.Quotient.mk_eq_zero]
  exact (exists_coherent_representatives_iff_mismatch_mem_range
    A bond J hstable b hmod).symm

/-- Surjective bonding maps make the Roos difference surjective by recursive correction. -/
theorem inverseDifference_surjective
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (hsurj : ∀ n, Function.Surjective (bond n)) :
    Function.Surjective (inverseDifference A bond) := by
  classical
  intro y
  let step : ∀ n, A n → A (n + 1) :=
    fun n x => Classical.choose (hsurj n (x - y n))
  let x : ∀ n, A n := fun n => Nat.rec 0 (fun k xk => step k xk) n
  refine ⟨x, ?_⟩
  funext n
  change x n - bond n (x (n + 1)) = y n
  rw [show x (n + 1) = step n (x n) by rfl]
  have hstep : bond n (step n (x n)) = x n - y n :=
    Classical.choose_spec (hsurj n (x n - y n))
  rw [hstep]
  abel

/-- Surjective cover bonding maps make the derived boundary connecting map onto.  Together with
`boundarySequence_exact`, this is the universal right-hand exact sequence for local boundary
migration. -/
theorem boundaryConnectingMap_surjective
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n)
    (hsurj : ∀ n, Function.Surjective (bond n)) :
    Function.Surjective (boundaryConnectingMap A bond J hstable) := by
  classical
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ c =>
    let step : ∀ n, A n → A (n + 1) :=
      fun n x => Classical.choose (hsurj n (x + (c n : A n)))
    let b : ∀ n, A n := fun n => Nat.rec 0 (fun k xk => step k xk) n
    have hstep (n : ℕ) : bond n (step n (b n)) = b n + (c n : A n) :=
      Classical.choose_spec (hsurj n (b n + (c n : A n)))
    have hmod : ∀ n, bond n (b (n + 1)) - b n ∈ J n := by
      intro n
      rw [show b (n + 1) = step n (b n) by rfl, hstep]
      simpa only [add_sub_cancel_left] using (c n).2
    let br : compatibleModuloSubmodule A bond J := ⟨b, hmod⟩
    refine ⟨Submodule.Quotient.mk br, ?_⟩
    change Submodule.Quotient.mk (representativeBoundary A bond J br) =
      Submodule.Quotient.mk c
    apply congrArg Submodule.Quotient.mk
    funext n
    apply Subtype.ext
    change bond n (b (n + 1)) - b n = (c n : A n)
    rw [show b (n + 1) = step n (b n) by rfl, hstep]
    exact add_sub_cancel_left _ _

/-- Universal short exact derived Shilov-limit law for a countable tower with surjective cover
bonding maps. -/
theorem localBoundaryDerivedSequence_shortExact
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n)
    (hsurj : ∀ n, Function.Surjective (bond n)) :
    Function.Injective (localBoundaryComparison A bond J) ∧
      Function.Exact (localBoundaryComparison A bond J)
        (boundaryConnectingMap A bond J hstable) ∧
      Function.Surjective (boundaryConnectingMap A bond J hstable) :=
  ⟨localBoundaryComparison_injective A bond J,
    localBoundaryDerivedSequence_exact A bond J hstable,
    boundaryConnectingMap_surjective A bond J hstable hsurj⟩

/-- Literal universal exact law
`0 → (lim Aₙ)/(lim Jₙ) → lim(Aₙ/Jₙ) → lim¹ Jₙ → 0`. -/
theorem stageBoundaryDerivedSequence_shortExact
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n)
    (hsurj : ∀ n, Function.Surjective (bond n)) :
    Function.Injective (stageLocalBoundaryComparison A bond J hstable) ∧
      Function.Exact (stageLocalBoundaryComparison A bond J hstable)
        (stageBoundaryConnectingMap A bond J hstable) ∧
      Function.Surjective (stageBoundaryConnectingMap A bond J hstable) := by
  let e := compatibleClassEquivStageLimit A bond J hstable
  constructor
  · intro x y hxy
    apply localBoundaryComparison_injective A bond J
    apply e.injective
    exact hxy
  constructor
  · intro z
    constructor
    · intro hz
      have hz' : boundaryConnectingMap A bond J hstable (e.symm z) = 0 := hz
      rcases (localBoundaryDerivedSequence_exact A bond J hstable (e.symm z)).mp hz' with
        ⟨x, hx⟩
      refine ⟨x, ?_⟩
      change e (localBoundaryComparison A bond J x) = z
      rw [hx]
      exact e.apply_symm_apply z
    · rintro ⟨x, hx⟩
      have hx' : localBoundaryComparison A bond J x = e.symm z := by
        apply e.injective
        change e (localBoundaryComparison A bond J x) = e (e.symm z)
        rw [e.apply_symm_apply]
        exact hx
      exact (localBoundaryDerivedSequence_exact A bond J hstable (e.symm z)).mpr ⟨x, hx'⟩
  · intro z
    rcases boundaryConnectingMap_surjective A bond J hstable hsurj z with ⟨y, hy⟩
    refine ⟨e y, ?_⟩
    change boundaryConnectingMap A bond J hstable (e.symm (e y)) = z
    rw [e.symm_apply_apply]
    exact hy

/-- The local boundary comparison is onto exactly when the global derived boundary obstruction
vanishes. -/
theorem localBoundaryComparison_surjective_iff
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n)
    (hsurj : ∀ n, Function.Surjective (bond n)) :
    Function.Surjective (localBoundaryComparison A bond J) ↔
      Subsingleton
        (DerivedLimitOne (fun n => J n) (restrictedBond A bond J hstable)) := by
  constructor
  · intro hcomparison
    constructor
    intro x y
    apply sub_eq_zero.mp
    let z := x - y
    rcases boundaryConnectingMap_surjective A bond J hstable hsurj z with ⟨c, hc⟩
    rcases hcomparison c with ⟨a, ha⟩
    have hzero : boundaryConnectingMap A bond J hstable c = 0 :=
      (localBoundaryDerivedSequence_exact A bond J hstable c).mpr ⟨a, ha⟩
    change z = 0
    exact hc.symm.trans hzero
  · intro hderived c
    have hzero : boundaryConnectingMap A bond J hstable c = 0 :=
      Subsingleton.elim _ _
    exact (localBoundaryDerivedSequence_exact A bond J hstable c).mp hzero

/-- Mittag--Leffler vanishing in the strong linkwise-surjective case. -/
theorem derivedLimitOne_subsingleton_of_surjective
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (hsurj : ∀ n, Function.Surjective (bond n)) :
    Subsingleton (DerivedLimitOne A bond) := by
  change Subsingleton ((∀ n, A n) ⧸ LinearMap.range (inverseDifference A bond))
  rw [Submodule.Quotient.subsingleton_iff]
  exact LinearMap.range_eq_top.mpr (inverseDifference_surjective A bond hsurj)

/-- Vanishing can be genuinely global: a zero bonding sequence has vanishing `lim¹` although its
individual bonding maps need not be onto. -/
theorem derivedLimitOne_subsingleton_of_zero_bond
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (hzero : ∀ n, bond n = 0) :
    Subsingleton (DerivedLimitOne A bond) := by
  change Subsingleton ((∀ n, A n) ⧸ LinearMap.range (inverseDifference A bond))
  rw [Submodule.Quotient.subsingleton_iff]
  apply LinearMap.range_eq_top.mpr
  intro y
  refine ⟨y, ?_⟩
  funext n
  change y n - bond n (y (n + 1)) = y n
  rw [hzero]
  simp

/-- Concrete separation of linkwise and global exactness over every field: every scalar zero bond
is non-surjective, while the derived inverse limit of the tower is zero. -/
theorem zero_scalar_bond_global_vanishing :
    (∀ _n : ℕ, ¬Function.Surjective (0 : 𝕜 →ₗ[𝕜] 𝕜)) ∧
      Subsingleton
        (DerivedLimitOne (fun _ : ℕ => 𝕜) (fun _ => (0 : 𝕜 →ₗ[𝕜] 𝕜))) := by
  constructor
  · intro _n hsurj
    rcases hsurj 1 with ⟨x, hx⟩
    simp at hx
  · apply derivedLimitOne_subsingleton_of_zero_bond
    intro n
    rfl

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
