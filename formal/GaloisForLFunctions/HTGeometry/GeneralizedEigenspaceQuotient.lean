import GaloisForLFunctions.HTGeometry.GeneralizedEigenspaceIntertwining
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.End

/-!
# Exact generalized eigenspaces after quotienting an invariant subspace

If the shifted restriction to an invariant subspace is invertible, quotient
projection identifies every generalized root level, including the maximal
root space. For surjectivity, lift a quotient root vector and subtract the
unique invariant-subspace correction that cancels its shifted power.
Injectivity follows because the same shifted power is injective on the
invariant subspace. Consequently eigenvalues and algebraic multiplicities
are preserved exactly. No compactness or finite-dimensional hypothesis is
needed for this algebraic transport.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Module.End

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The quotient map intertwines the original operator and its induced operator. -/
theorem mkQ_intertwines_mapQ (f : Module.End R V) (S : Submodule R V)
    (hS : ∀ x ∈ S, f x ∈ S) (x : V) :
    S.mkQ (f x) = S.mapQ S f (fun {_} hx => hS _ hx) (S.mkQ x) :=
  (S.mapQ_apply S f x).symm

/-- Quotient projection on every generalized root level, including the maximal union. -/
def quotientGenEigenspaceMap (f : Module.End R V) (S : Submodule R V)
    (hS : ∀ x ∈ S, f x ∈ S) (mu : R) (k : ℕ∞) :
    f.genEigenspace mu k →ₗ[R] Module.End.genEigenspace (S.mapQ S f (fun {_} hx => hS _ hx)) mu k :=
  (S.mkQ.domRestrict _).codRestrict _ (fun x => by
    obtain ⟨n, hn, hx⟩ := Module.End.mem_genEigenspace.mp x.property
    refine Module.End.mem_genEigenspace.mpr ⟨n, hn, ?_⟩
    rw [LinearMap.mem_ker] at hx ⊢
    change ((S.mapQ S f (fun {_} hx => hS _ hx) - mu • 1) ^ n) (S.mkQ (x : V)) = 0
    rw [← map_pow_sub_smul_of_intertwining f (S.mapQ S f (fun {_} hx => hS _ hx)) S.mkQ
      (mkQ_intertwines_mapQ f S hS)]
    rw [hx, map_zero])

theorem quotientGenEigenspaceMap_apply (f : Module.End R V) (S : Submodule R V)
    (hS : ∀ x ∈ S, f x ∈ S) (mu : R) (k : ℕ∞) (x : f.genEigenspace mu k) :
    (quotientGenEigenspaceMap f S hS mu k x : V ⧸ S) = S.mkQ x := rfl

/-- An invertible shifted restriction contains no generalized root vector. -/
theorem eq_zero_of_mem_genEigenspace_of_mem_invariant
    (f : Module.End R V) (S : Submodule R V) (hS : ∀ x ∈ S, f x ∈ S)
    (mu : R) (hunit : IsUnit (f.restrict hS - mu • 1)) {k : ℕ∞} {x : V}
    (hx : x ∈ f.genEigenspace mu k) (hxS : x ∈ S) : x = 0 := by
  obtain ⟨n, -, hn⟩ := Module.End.mem_genEigenspace.mp hx
  let u : S := ⟨x, hxS⟩
  have hu : ((f.restrict hS - mu • 1) ^ n) u = 0 := by
    apply Subtype.ext
    change S.subtype (((f.restrict hS - mu • 1) ^ n) u) = 0
    rw [map_pow_sub_smul_of_intertwining (f.restrict hS) f S.subtype (fun _ => rfl)]
    exact hn
  have hinj := ((Module.End.isUnit_iff _).mp (hunit.pow n)).1
  have hzero : u = 0 := hinj (by simpa only [map_zero] using hu)
  exact congrArg (fun v : S => (v : V)) hzero

theorem quotientGenEigenspaceMap_injective
    (f : Module.End R V) (S : Submodule R V) (hS : ∀ x ∈ S, f x ∈ S)
    (mu : R) (hunit : IsUnit (f.restrict hS - mu • 1)) (k : ℕ∞) :
    Function.Injective (quotientGenEigenspaceMap f S hS mu k) := by
  intro x y hxy
  have hq : S.mkQ (x : V) = S.mkQ (y : V) := congrArg Subtype.val hxy
  have hzero : S.mkQ ((x : V) - (y : V)) = 0 := by rw [map_sub, hq, sub_self]
  have hmem : (x : V) - (y : V) ∈ S := (Submodule.Quotient.mk_eq_zero S).mp hzero
  apply Subtype.ext
  exact sub_eq_zero.mp (eq_zero_of_mem_genEigenspace_of_mem_invariant f S hS mu hunit
    ((f.genEigenspace mu k).sub_mem x.property y.property) hmem)

/-- Inverting the shifted power on the invariant subspace corrects any quotient root lift. -/
theorem quotientGenEigenspaceMap_surjective
    (f : Module.End R V) (S : Submodule R V) (hS : ∀ x ∈ S, f x ∈ S)
    (mu : R) (hunit : IsUnit (f.restrict hS - mu • 1)) (k : ℕ∞) :
    Function.Surjective (quotientGenEigenspaceMap f S hS mu k) := by
  intro y
  obtain ⟨x, hx⟩ := S.mkQ_surjective (y : V ⧸ S)
  obtain ⟨n, hn, hy⟩ := Module.End.mem_genEigenspace.mp y.property
  have hmem : ((f - mu • 1) ^ n) x ∈ S := by
    apply (Submodule.Quotient.mk_eq_zero S).mp
    change S.mkQ (((f - mu • 1) ^ n) x) = 0
    rw [map_pow_sub_smul_of_intertwining f (S.mapQ S f (fun {_} hx => hS _ hx)) S.mkQ
      (mkQ_intertwines_mapQ f S hS), hx]
    exact hy
  let r : S := ⟨((f - mu • 1) ^ n) x, hmem⟩
  obtain ⟨v, hv⟩ := ((Module.End.isUnit_iff _).mp (hunit.pow n)).2 r
  have hvcoe : ((f - mu • 1) ^ n) (v : V) = ((f - mu • 1) ^ n) x := by
    calc
      _ = S.subtype (((f.restrict hS - mu • 1) ^ n) v) :=
        (map_pow_sub_smul_of_intertwining (f.restrict hS) f S.subtype
          (fun _ => rfl) mu n v).symm
      _ = ((f - mu • 1) ^ n) x := congrArg (fun w : S => (w : V)) hv
  have hroot : (x - (v : V)) ∈ f.genEigenspace mu k := by
    refine Module.End.mem_genEigenspace.mpr ⟨n, hn, ?_⟩
    change ((f - mu • 1) ^ n) (x - (v : V)) = 0
    rw [map_sub, hvcoe, sub_self]
  refine ⟨⟨x - (v : V), hroot⟩, Subtype.ext ?_⟩
  change S.mkQ (x - (v : V)) = (y : V ⧸ S)
  have hvq : S.mkQ (v : V) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr v.property
  rw [map_sub, hvq, sub_zero, hx]

/-- Exact root-space equivalence induced by quotient projection. -/
def quotientGenEigenspaceEquiv
    (f : Module.End R V) (S : Submodule R V) (hS : ∀ x ∈ S, f x ∈ S)
    (mu : R) (hunit : IsUnit (f.restrict hS - mu • 1)) (k : ℕ∞) :
    f.genEigenspace mu k ≃ₗ[R] Module.End.genEigenspace (S.mapQ S f (fun {_} hx => hS _ hx)) mu k :=
  LinearEquiv.ofBijective (quotientGenEigenspaceMap f S hS mu k)
    ⟨quotientGenEigenspaceMap_injective f S hS mu hunit k,
      quotientGenEigenspaceMap_surjective f S hS mu hunit k⟩

theorem quotientGenEigenspaceEquiv_apply
    (f : Module.End R V) (S : Submodule R V) (hS : ∀ x ∈ S, f x ∈ S)
    (mu : R) (hunit : IsUnit (f.restrict hS - mu • 1)) (k : ℕ∞)
    (x : f.genEigenspace mu k) :
    (quotientGenEigenspaceEquiv f S hS mu hunit k x : V ⧸ S) = S.mkQ x := rfl

theorem finrank_genEigenspace_eq_quotient
    (f : Module.End R V) (S : Submodule R V) (hS : ∀ x ∈ S, f x ∈ S)
    (mu : R) (hunit : IsUnit (f.restrict hS - mu • 1)) (k : ℕ∞) :
    Module.finrank R (f.genEigenspace mu k) =
      Module.finrank R (Module.End.genEigenspace (S.mapQ S f (fun {_} hx => hS _ hx)) mu k) :=
  (quotientGenEigenspaceEquiv f S hS mu hunit k).finrank_eq

/-- The maximal root spaces have exactly the same algebraic multiplicity. -/
theorem finrank_maxGenEigenspace_eq_quotient
    (f : Module.End R V) (S : Submodule R V) (hS : ∀ x ∈ S, f x ∈ S)
    (mu : R) (hunit : IsUnit (f.restrict hS - mu • 1)) :
    Module.finrank R (f.maxGenEigenspace mu) =
      Module.finrank R (Module.End.maxGenEigenspace (S.mapQ S f (fun {_} hx => hS _ hx)) mu) :=
  finrank_genEigenspace_eq_quotient f S hS mu hunit ⊤

/-- The quotient creates and loses no eigenvalue when the shifted restriction is invertible. -/
theorem hasEigenvalue_mapQ_iff
    (f : Module.End R V) (S : Submodule R V) (hS : ∀ x ∈ S, f x ∈ S)
    (mu : R) (hunit : IsUnit (f.restrict hS - mu • 1)) :
    Module.End.HasEigenvalue (S.mapQ S f (fun {_} hx => hS _ hx)) mu ↔
      Module.End.HasEigenvalue f mu := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h.exists_hasEigenvector
    obtain ⟨x, hx⟩ := quotientGenEigenspaceMap_surjective f S hS mu hunit 1 ⟨y, hy.1⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨x.property, ?_⟩
    intro hxzero
    have hq : S.mkQ (x : V) = y := congrArg Subtype.val hx
    rw [hxzero, map_zero] at hq
    exact hy.2 hq.symm
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    have hq : S.mkQ x ≠ 0 := by
      intro hzero
      exact hx.2 (eq_zero_of_mem_genEigenspace_of_mem_invariant f S hS mu hunit hx.1
        ((Submodule.Quotient.mk_eq_zero S).mp hzero))
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨(quotientGenEigenspaceMap f S hS mu 1 ⟨x, hx.1⟩).property, hq⟩

end

end GaloisForLFunctions.HTGeometry
