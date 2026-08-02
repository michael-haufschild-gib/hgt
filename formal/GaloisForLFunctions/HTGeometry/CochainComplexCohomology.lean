import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Directed

/-!
# Cohomology of a cochain complex of modules, and its filtered stages

A cochain complex of `k`-modules is a family of modules with degree-raising maps whose consecutive
composites vanish.  Its cohomology in degree `n` is the cocycles modulo the coboundaries.  Cochain
maps induce maps on cohomology, functorially, and a quasi-isomorphism is a cochain map inducing an
isomorphism in every degree.

A filtration of a complex by a directed family of subcomplexes exhausting it satisfies the two
halves of "cohomology commutes with the filtered union": every cocycle already lies at a stage, and
a cocycle that becomes a coboundary in the union already becomes one at a later stage.

* `DeningerCochainComplex`, `deningerCohomology` : the complex and its cohomology.
* `DeningerCochainMap`, `deningerCohomologyMap` : cochain maps and the induced maps.
* `DeningerQuasiIso` : the quasi-isomorphism predicate.
* `deningerFiltered_cocycle_stage`, `deningerFiltered_coboundary_stage` : the filtered-union
  comparison.
-/

namespace HTGeometry

section Complex

variable (k : Type*) [CommRing k] (M : ℕ → Type*)
variable [∀ n, AddCommGroup (M n)] [∀ n, Module k (M n)]

/-- A cochain complex of `k`-modules: degree-raising maps whose consecutive composites vanish. -/
structure DeningerCochainComplex where
  /-- The differential raising the degree by one. -/
  d : ∀ n, M n →ₗ[k] M (n + 1)
  /-- Consecutive differentials compose to zero. -/
  d_comp_d : ∀ n, (d (n + 1)).comp (d n) = 0

variable {k M}

namespace DeningerCochainComplex

variable (C : DeningerCochainComplex k M)

/-- The cocycles in degree `n`. -/
def cocycles (n : ℕ) : Submodule k (M n) :=
  LinearMap.ker (C.d n)

/-- The coboundaries in degree `n`; in degree zero there are none. -/
def coboundaries : ∀ n, Submodule k (M n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (C.d n)

@[simp]
theorem coboundaries_zero : C.coboundaries 0 = ⊥ := rfl

@[simp]
theorem coboundaries_succ (n : ℕ) : C.coboundaries (n + 1) = LinearMap.range (C.d n) := rfl

theorem mem_cocycles_iff {n : ℕ} {x : M n} : x ∈ C.cocycles n ↔ C.d n x = 0 :=
  Iff.rfl

/-- Every coboundary is a cocycle. -/
theorem coboundaries_le_cocycles (n : ℕ) : C.coboundaries n ≤ C.cocycles n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun (C.d_comp_d n) y

/-- The coboundaries, viewed inside the cocycles. -/
def coboundariesInCocycles (n : ℕ) : Submodule k (C.cocycles n) :=
  (C.coboundaries n).comap (C.cocycles n).subtype

/-- The cohomology of a cochain complex in degree `n`. -/
abbrev cohomology (n : ℕ) : Type _ :=
  C.cocycles n ⧸ C.coboundariesInCocycles n

/-- The cohomology class of a cocycle. -/
def cohomologyMk {n : ℕ} (x : C.cocycles n) : C.cohomology n :=
  Submodule.Quotient.mk x

theorem cohomologyMk_eq_zero_iff {n : ℕ} (x : C.cocycles n) :
    C.cohomologyMk x = 0 ↔ (x : M n) ∈ C.coboundaries n := by
  rw [cohomologyMk, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

theorem cohomologyMk_surjective (n : ℕ) : Function.Surjective (C.cohomologyMk (n := n)) :=
  Submodule.Quotient.mk_surjective _

end DeningerCochainComplex

end Complex

section Maps

variable {k : Type*} [CommRing k] {M N : ℕ → Type*}
variable [∀ n, AddCommGroup (M n)] [∀ n, Module k (M n)]
variable [∀ n, AddCommGroup (N n)] [∀ n, Module k (N n)]

/-- A map of cochain complexes: degreewise linear maps commuting with the differentials. -/
structure DeningerCochainMap (C : DeningerCochainComplex k M) (D : DeningerCochainComplex k N) where
  /-- The degreewise components. -/
  f : ∀ n, M n →ₗ[k] N n
  /-- The components commute with the differentials. -/
  comm : ∀ n, (f (n + 1)).comp (C.d n) = (D.d n).comp (f n)

namespace DeningerCochainMap

variable {C : DeningerCochainComplex k M} {D : DeningerCochainComplex k N}
variable (F : DeningerCochainMap C D)

/-- A cochain map sends cocycles to cocycles. -/
theorem mapsTo_cocycles {n : ℕ} {x : M n} (hx : x ∈ C.cocycles n) : F.f n x ∈ D.cocycles n := by
  have h := LinearMap.congr_fun (F.comm n) x
  simp only [LinearMap.comp_apply] at h
  have hx' : C.d n x = 0 := hx
  show D.d n (F.f n x) = 0
  rw [← h, hx', map_zero]

/-- A cochain map sends coboundaries to coboundaries. -/
theorem mapsTo_coboundaries {n : ℕ} {x : M n} (hx : x ∈ C.coboundaries n) :
    F.f n x ∈ D.coboundaries n := by
  cases n with
  | zero =>
    rw [C.coboundaries_zero, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  | succ n =>
    obtain ⟨y, rfl⟩ := hx
    refine ⟨F.f n y, ?_⟩
    have h := LinearMap.congr_fun (F.comm n) y
    simp only [LinearMap.comp_apply] at h
    exact h.symm

/-- The induced map on cocycles. -/
def cocyclesMap (n : ℕ) : C.cocycles n →ₗ[k] D.cocycles n where
  toFun x := ⟨F.f n x, F.mapsTo_cocycles x.2⟩
  map_add' x y := Subtype.ext (map_add (F.f n) x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul (F.f n) c x.1)

@[simp]
theorem cocyclesMap_coe (n : ℕ) (x : C.cocycles n) :
    ((F.cocyclesMap n x : D.cocycles n) : N n) = F.f n (x : M n) :=
  rfl

/-- **The induced map on cohomology.** -/
def cohomologyMap (n : ℕ) : C.cohomology n →ₗ[k] D.cohomology n :=
  Submodule.mapQ _ _ (F.cocyclesMap n) (fun _ hx => F.mapsTo_coboundaries hx)

@[simp]
theorem cohomologyMap_mk (n : ℕ) (x : C.cocycles n) :
    F.cohomologyMap n (C.cohomologyMk x) = D.cohomologyMk (F.cocyclesMap n x) :=
  rfl

end DeningerCochainMap

/-- The identity cochain map. -/
def deningerCochainMapId (C : DeningerCochainComplex k M) : DeningerCochainMap C C where
  f _ := LinearMap.id
  comm _ := rfl

@[simp]
theorem deningerCochainMapId_cohomologyMap (C : DeningerCochainComplex k M) (n : ℕ) :
    (deningerCochainMapId C).cohomologyMap n = LinearMap.id := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := C.cohomologyMk_surjective n q
  rfl

section Comp

variable {P : ℕ → Type*} [∀ n, AddCommGroup (P n)] [∀ n, Module k (P n)]

/-- The composite of two cochain maps. -/
def deningerCochainMapComp {C : DeningerCochainComplex k M} {D : DeningerCochainComplex k N}
    {E : DeningerCochainComplex k P}
    (G : DeningerCochainMap D E) (F : DeningerCochainMap C D) : DeningerCochainMap C E where
  f n := (G.f n).comp (F.f n)
  comm n := by
    refine LinearMap.ext fun x => ?_
    have h1 := LinearMap.congr_fun (F.comm n) x
    have h2 := LinearMap.congr_fun (G.comm n) (F.f n x)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h1, h2]

/-- Cohomology is functorial. -/
@[simp]
theorem deningerCochainMapComp_cohomologyMap {C : DeningerCochainComplex k M}
    {D : DeningerCochainComplex k N} {E : DeningerCochainComplex k P}
    (G : DeningerCochainMap D E) (F : DeningerCochainMap C D) (n : ℕ) :
    (deningerCochainMapComp G F).cohomologyMap n =
      (G.cohomologyMap n).comp (F.cohomologyMap n) := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := C.cohomologyMk_surjective n q
  rfl

end Comp

/-- **A quasi-isomorphism**: a cochain map inducing an isomorphism on cohomology in every degree. -/
def DeningerQuasiIso {C : DeningerCochainComplex k M} {D : DeningerCochainComplex k N}
    (F : DeningerCochainMap C D) : Prop :=
  ∀ n : ℕ, Function.Bijective (F.cohomologyMap n)

theorem deningerQuasiIso_id (C : DeningerCochainComplex k M) :
    DeningerQuasiIso (deningerCochainMapId C) := by
  intro n
  rw [deningerCochainMapId_cohomologyMap]
  exact Function.bijective_id

end Maps

section Filtration

variable {k : Type*} [CommRing k] {M : ℕ → Type*}
variable [∀ n, AddCommGroup (M n)] [∀ n, Module k (M n)]

/-- A subcomplex of a cochain complex: a degreewise submodule stable under the differential. -/
structure DeningerSubcomplex (C : DeningerCochainComplex k M) where
  /-- The degreewise submodule. -/
  sub : ∀ n, Submodule k (M n)
  /-- The submodule is stable under the differential. -/
  stable : ∀ n, ∀ x ∈ sub n, C.d n x ∈ sub (n + 1)

variable {C : DeningerCochainComplex k M}
variable {B : Type*} [Preorder B] [IsDirected B (· ≤ ·)]

/-- An exhausting monotone family of subcomplexes is a directed family of submodules. -/
theorem deningerFiltered_directed (F : B → DeningerSubcomplex C)
    (hmono : ∀ n, Monotone fun b => (F b).sub n) (n : ℕ) :
    Directed (· ≤ ·) fun b => (F b).sub n := by
  intro b b'
  obtain ⟨c, hbc, hbc'⟩ := directed_of (· ≤ ·) b b'
  exact ⟨c, hmono n hbc, hmono n hbc'⟩

/-- **Every element already lies at a stage.**  In particular every cocycle of the union is a
cocycle of some stage, so every cohomology class comes from a finite stage. -/
theorem deningerFiltered_cocycle_stage [Nonempty B] (F : B → DeningerSubcomplex C)
    (hmono : ∀ n, Monotone fun b => (F b).sub n)
    (hexh : ∀ n, ⨆ b, (F b).sub n = ⊤)
    (n : ℕ) (x : M n) : ∃ b, x ∈ (F b).sub n := by
  have hmem : x ∈ ⨆ b, (F b).sub n := by rw [hexh n]; exact Submodule.mem_top
  rwa [Submodule.mem_iSup_of_directed _ (deningerFiltered_directed F hmono n)] at hmem

/-- **A class that dies in the union already dies at a later stage.**  If a cocycle present at a
stage becomes a coboundary in the whole complex, it is already a coboundary of the subcomplex at
some later stage. -/
theorem deningerFiltered_coboundary_stage [Nonempty B] (F : B → DeningerSubcomplex C)
    (hmono : ∀ n, Monotone fun b => (F b).sub n)
    (hexh : ∀ n, ⨆ b, (F b).sub n = ⊤)
    {n : ℕ} {b : B} {x : M (n + 1)} (hx : x ∈ C.coboundaries (n + 1)) :
    ∃ b', b ≤ b' ∧ ∃ y ∈ (F b').sub n, C.d n y = x := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨c, hc⟩ := deningerFiltered_cocycle_stage F hmono hexh n y
  obtain ⟨b', hbb', hcb'⟩ := directed_of (· ≤ ·) b c
  exact ⟨b', hbb', y, hmono n hcb' hc, hy⟩

/-- **The filtered comparison.**  Cohomology of an exhausted filtration is computed at the stages:
every class is represented at a stage, and a class dying in the union dies at a stage. -/
theorem deningerFiltered_cohomology_comparison [Nonempty B] (F : B → DeningerSubcomplex C)
    (hmono : ∀ n, Monotone fun b => (F b).sub n)
    (hexh : ∀ n, ⨆ b, (F b).sub n = ⊤) (n : ℕ) :
    (∀ x : M n, ∃ b, x ∈ (F b).sub n) ∧
      ∀ (b : B) (x : M (n + 1)), x ∈ C.coboundaries (n + 1) →
        ∃ b', b ≤ b' ∧ ∃ y ∈ (F b').sub n, C.d n y = x :=
  ⟨deningerFiltered_cocycle_stage F hmono hexh n,
    fun _ _ hx => deningerFiltered_coboundary_stage F hmono hexh hx⟩

end Filtration

section ZeroDifferential

variable {k : Type*} [CommRing k] {M : ℕ → Type*}
variable [∀ n, AddCommGroup (M n)] [∀ n, Module k (M n)]

/-- The complex with vanishing differential. -/
def deningerZeroComplex : DeningerCochainComplex k M where
  d _ := 0
  d_comp_d _ := rfl

@[simp]
theorem deningerZeroComplex_cocycles (n : ℕ) :
    (deningerZeroComplex (k := k) (M := M)).cocycles n = ⊤ :=
  LinearMap.ker_zero

@[simp]
theorem deningerZeroComplex_coboundaries (n : ℕ) :
    (deningerZeroComplex (k := k) (M := M)).coboundaries n = ⊥ := by
  cases n with
  | zero => rfl
  | succ n => exact LinearMap.range_zero

/-- **Cohomology of a complex with zero differential is the complex itself.** -/
noncomputable def deningerZeroComplexCohomologyEquiv (n : ℕ) :
    (deningerZeroComplex (k := k) (M := M)).cohomology n ≃ₗ[k] M n :=
  (Submodule.quotEquivOfEqBot _ (by
    refine le_antisymm ?_ bot_le
    intro x hx
    have : (x : M n) ∈ (deningerZeroComplex (k := k) (M := M)).coboundaries n := hx
    rw [deningerZeroComplex_coboundaries, Submodule.mem_bot] at this
    exact Submodule.mem_bot _ |>.mpr (Subtype.ext this))).trans
    ((LinearEquiv.ofEq _ _ (deningerZeroComplex_cocycles n)).trans (Submodule.topEquiv))

end ZeroDifferential

end HTGeometry
