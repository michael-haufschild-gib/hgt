import Mathlib.Data.Complex.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The regular representation of a finite group over `ℂ` and its simple decomposition

Mathlib has Maschke's theorem but no character theory of finite groups.  This file starts that
development with the facts that Burnside's `p ^ a q ^ b` theorem needs.

The whole development is phrased in terms of `ℂ`-subspaces of the group algebra that are stable
under left translation (`IsGStable`), so that no `MonoidAlgebra`-submodule types leak into the
statements.

* `exists_simple_decomposition` — the group algebra `ℂ[G]` is an internal direct sum of finitely
  many `G`-stable `ℂ`-subspaces, each of which is minimal among the nonzero `G`-stable subspaces.
* `trace_regLeft` — the trace of left multiplication by `g` on `ℂ[G]` is `#G` if `g = 1` and `0`
  otherwise.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra

variable (G : Type u) [Group G] [Fintype G]

/-- Left multiplication by `g` on the group algebra, as a `ℂ`-linear endomorphism. -/
noncomputable def regLeft (g : G) : MonoidAlgebra ℂ G →ₗ[ℂ] MonoidAlgebra ℂ G :=
  LinearMap.mulLeft ℂ (MonoidAlgebra.single g 1)

omit [Fintype G] in
theorem regLeft_apply (g : G) (x : MonoidAlgebra ℂ G) :
    regLeft G g x = MonoidAlgebra.single g 1 * x := rfl

omit [Fintype G] in
theorem regLeft_apply_smul (g : G) (x : MonoidAlgebra ℂ G) :
    regLeft G g x = (MonoidAlgebra.single g 1 : MonoidAlgebra ℂ G) • x := rfl

/-- A `ℂ`-subspace of the group algebra stable under left translation by `G`. -/
def IsGStable (W : Submodule ℂ (MonoidAlgebra ℂ G)) : Prop :=
  ∀ g : G, Set.MapsTo (regLeft G g) (W : Set (MonoidAlgebra ℂ G)) (W : Set (MonoidAlgebra ℂ G))

variable {G}

omit [Fintype G] in
theorem isGStable_iff {W : Submodule ℂ (MonoidAlgebra ℂ G)} :
    IsGStable G W ↔ ∀ (g : G), ∀ x ∈ W, regLeft G g x ∈ W := Iff.rfl

/-- A `G`-stable `ℂ`-subspace of the group algebra is a `ℂ[G]`-submodule. -/
def toAlgSubmodule (W : Submodule ℂ (MonoidAlgebra ℂ G)) (hW : IsGStable G W) :
    Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) where
  carrier := W
  add_mem' := W.add_mem
  zero_mem' := W.zero_mem
  smul_mem' := by
    intro a w hw
    induction a using MonoidAlgebra.induction_on with
    | hM m => exact hW m hw
    | hadd x y hx hy => simpa [add_mul] using W.add_mem hx hy
    | hsmul r x hx => simpa [smul_mul_assoc] using W.smul_mem r hx

omit [Fintype G] in
@[simp] theorem restrictScalars_toAlgSubmodule (W : Submodule ℂ (MonoidAlgebra ℂ G))
    (hW : IsGStable G W) : (toAlgSubmodule W hW).restrictScalars ℂ = W := rfl

omit [Fintype G] in
theorem isGStable_restrictScalars (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    IsGStable G (S.restrictScalars ℂ) := by
  intro g x hx
  have hx' : x ∈ S := hx
  exact S.smul_mem _ hx'

variable (G)

/-- The group algebra of a finite group over `ℂ` is an internal direct sum of minimal nonzero
`G`-stable `ℂ`-subspaces. -/
theorem exists_simple_decomposition :
    ∃ (n : ℕ) (N : Fin n → Submodule ℂ (MonoidAlgebra ℂ G)),
      (∀ i, IsGStable G (N i)) ∧ (∀ i, N i ≠ ⊥) ∧
      (∀ i, ∀ W : Submodule ℂ (MonoidAlgebra ℂ G), IsGStable G W → W ≤ N i →
        W = ⊥ ∨ W = N i) ∧
      DirectSum.IsInternal N := by
  classical
  obtain ⟨s, hind, hsup, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G)
  have hind' : iSupIndep ((↑) : s → Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :=
    (sSupIndep_iff _).mp hind
  have hatom : ∀ S : s, IsAtom (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :=
    fun S => isSimpleModule_iff_isAtom.mp (hsimple S.1 S.2)
  have hfin : Finite s := WellFoundedGT.finite_of_iSupIndep hind' fun S => (hatom S).1
  haveI : Fintype s := Fintype.ofFinite _
  set e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm with he
  refine ⟨Fintype.card s,
    fun i => ((e i : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)).restrictScalars ℂ),
    fun i => isGStable_restrictScalars _, ?_, ?_, ?_⟩
  · intro i
    show (Submodule.restrictScalars ℂ (e i : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)))
      ≠ ⊥
    exact fun h => (hatom (e i)).1
      ((Submodule.restrictScalars_eq_bot_iff ℂ (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)).mp h)
  · intro i W hW hle
    have hle' : toAlgSubmodule W hW ≤ (e i : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :=
      fun x hx => hle hx
    rcases eq_or_lt_of_le hle' with h | h
    · right
      rw [← restrictScalars_toAlgSubmodule W hW, h]
    · left
      have := (hatom (e i)).2 _ h
      rw [← restrictScalars_toAlgSubmodule W hW, this]
      exact Submodule.restrictScalars_bot ℂ _ _
  · refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
    · have h2 : iSupIndep
          (fun i : Fin (Fintype.card s) =>
            ((e i : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)))) :=
        hind'.comp e.injective
      intro i
      have h := h2 i
      rw [← Submodule.disjoint_restrictScalars_iff (S := ℂ)] at h
      simpa using h
    · rw [← Submodule.restrictScalars_iSup]
      have hs : (⨆ i : Fin (Fintype.card s),
          ((e i : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)))) = ⊤ := by
        rw [e.surjective.iSup_comp
          (g := fun j : s => (j : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))),
          ← sSup_eq_iSup']
        exact hsup
      rw [hs]
      ext x
      simp

/-- The trace of left multiplication by `g` on the whole group algebra. -/
theorem trace_regLeft [DecidableEq G] (g : G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G) (regLeft G g)
      = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  let b : Module.Basis G ℂ (MonoidAlgebra ℂ G) := MonoidAlgebra.basis G ℂ
  have hb : ∀ h : G, b h = MonoidAlgebra.single h (1 : ℂ) := fun h => rfl
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  have hentry : ∀ h : G, (LinearMap.toMatrix b b) (regLeft G g) h h
      = if g = 1 then (1 : ℂ) else 0 := by
    intro h
    rw [LinearMap.toMatrix_apply, hb h, regLeft_apply]
    have hmul : MonoidAlgebra.single g (1 : ℂ) * MonoidAlgebra.single h 1
        = MonoidAlgebra.single (g * h) 1 := by
      rw [MonoidAlgebra.single_mul_single, one_mul]
    rw [hmul, ← hb (g * h), Module.Basis.repr_self]
    by_cases hg : g = 1
    · subst hg; simp
    · simp [hg]
  simp only [Matrix.diag_apply, hentry]
  by_cases hg : g = 1 <;> simp [hg, Finset.card_univ]

end GaloisForLFunctions.HTGeometry.GroupCharacter
