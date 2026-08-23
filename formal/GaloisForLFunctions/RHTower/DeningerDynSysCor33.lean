import GaloisForLFunctions.RHTower.DeningerDynSysInvariantPoints
import Mathlib.RingTheory.Invariant.Basic

/-!
# Corollary 3.3: descent through an intermediate normal extension

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 3.3.

For a normal subgroup `N` of `G`, the invariants `B ^ G` sit inside `B ^ N`, and the quotient
`G ⧸ N` — Deninger's `G₁ = Aut_{K₀}(K₁)` — acts on `B ^ N`.  Restriction

`Hom (B ^ N , C) / (G ⧸ N) ⟶ Hom (B ^ G , C)`

is a bijection for every algebraically closed field `C`.

Surjectivity needs nothing beyond Theorem 1.4 for `G`: extend to `B` and restrict.  For the fibres
one extends both homomorphisms to `B` — this is Theorem 1.4 for the closed subgroup `N`, which is
again profinite — and applies Theorem 1.4 for `G` to the two extensions, which agree on `B ^ G`.
This is Deninger's own argument `Hom(B,C)/N = Hom(B^N,C)`, `Hom(B,C)/G = Hom(B^G,C)`.
-/

namespace RHTower

open MulAction

section Inclusion

variable {B : Type*} [CommRing B]
variable {G : Type*} [Group G] [MulSemiringAction G B]
variable (N : Subgroup G)

/-- The invariants of the whole group sit inside the invariants of a subgroup. -/
theorem deningerFixedSubring_le : FixedPoints.subring B G ≤ FixedPoints.subring B N :=
  fun _ hx n => hx (n : G)

/-- The inclusion of the invariants of the group into the invariants of a subgroup. -/
def deningerFixedSubringInclusion :
    FixedPoints.subring B G →+* FixedPoints.subring B N :=
  Subring.inclusion (deningerFixedSubring_le N)

theorem deningerFixedSubringInclusion_algebraMap :
    (algebraMap (FixedPoints.subring B N) B).comp (deningerFixedSubringInclusion (B := B) N)
      = algebraMap (FixedPoints.subring B G) B := rfl

variable [N.Normal]

/-- The quotient group acts on the invariants of a normal subgroup through the action of any
representative on the ambient ring. -/
theorem deningerFixedSubring_quotient_smul_val (g : G) (x : FixedPoints.subring B N) :
    (((QuotientGroup.mk g : G ⧸ N) • x : FixedPoints.subring B N) : B) = g • (x : B) := rfl

end Inclusion

section Points

variable {B : Type*} [CommRing B]
variable {G : Type*} [Group G] [MulSemiringAction G B]
variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
variable (N : Subgroup G) [N.Normal]
variable {C : Type*} [Field C] [IsAlgClosed C]

omit [N.Normal] in
/-- **Deninger, Corollary 3.3, surjectivity.**  Restriction from the invariants of a normal
subgroup to the invariants of the whole group is surjective on homomorphisms into an algebraically
closed field. -/
theorem deningerFixedSubring_restrict_surjective_of_normal :
    Function.Surjective (fun ψ : FixedPoints.subring B N →+* C =>
      ψ.comp (deningerFixedSubringInclusion (B := B) N)) := by
  intro φ
  obtain ⟨Ψ, hΨ⟩ := deningerFixedSubring_restrict_surjective (B := B) (G := G) (C := C) φ
  have hΨ' : Ψ.comp (algebraMap (FixedPoints.subring B G) B) = φ := hΨ
  refine ⟨Ψ.comp (algebraMap (FixedPoints.subring B N) B), ?_⟩
  show (Ψ.comp (algebraMap (FixedPoints.subring B N) B)).comp
    (deningerFixedSubringInclusion (B := B) N) = φ
  rw [← hΨ', RingHom.comp_assoc, deningerFixedSubringInclusion_algebraMap]

/-- **Deninger, Corollary 3.3, the fibres.**  Two homomorphisms of the invariants of a closed
normal subgroup agree on the invariants of the whole group exactly when they differ by an element
of the quotient group. -/
theorem deningerFixedSubring_restrict_eq_iff_of_normal (hcl : IsClosed (N : Set G))
    (ψ₁ ψ₂ : FixedPoints.subring B N →+* C) :
    ψ₁.comp (deningerFixedSubringInclusion (B := B) N)
        = ψ₂.comp (deningerFixedSubringInclusion (B := B) N)
      ↔ ∃ g : G ⧸ N, ∀ x : FixedPoints.subring B N, ψ₂ x = ψ₁ (g • x) := by
  haveI : CompactSpace N := isCompact_iff_compactSpace.mp hcl.isCompact
  constructor
  · intro h
    obtain ⟨Ψ₁, hΨ₁⟩ := deningerFixedSubring_restrict_surjective (B := B) (G := N) (C := C) ψ₁
    obtain ⟨Ψ₂, hΨ₂⟩ := deningerFixedSubring_restrict_surjective (B := B) (G := N) (C := C) ψ₂
    have hΨ₁' : Ψ₁.comp (algebraMap (FixedPoints.subring B N) B) = ψ₁ := hΨ₁
    have hΨ₂' : Ψ₂.comp (algebraMap (FixedPoints.subring B N) B) = ψ₂ := hΨ₂
    have hres : Ψ₁.comp (algebraMap (FixedPoints.subring B G) B)
        = Ψ₂.comp (algebraMap (FixedPoints.subring B G) B) := by
      rw [← deningerFixedSubringInclusion_algebraMap (B := B) N, ← RingHom.comp_assoc,
        ← RingHom.comp_assoc, hΨ₁', hΨ₂', h]
    obtain ⟨g, hg⟩ := (deningerFixedSubring_restrict_eq_iff (B := B) (G := G) Ψ₁ Ψ₂).1 hres
    refine ⟨QuotientGroup.mk g, fun x => ?_⟩
    have h2 : ψ₂ x = Ψ₂ (x : B) :=
      congrArg (fun r : FixedPoints.subring B N →+* C => r x) hΨ₂'.symm
    have h1 : ψ₁ ((QuotientGroup.mk g : G ⧸ N) • x)
        = Ψ₁ (((QuotientGroup.mk g : G ⧸ N) • x : FixedPoints.subring B N) : B) :=
      congrArg (fun r : FixedPoints.subring B N →+* C => r _) hΨ₁'.symm
    rw [h2, h1, deningerFixedSubring_quotient_smul_val, hg]
  · rintro ⟨g, hg⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    refine RingHom.ext fun a => ?_
    show ψ₁ (deningerFixedSubringInclusion N a) = ψ₂ (deningerFixedSubringInclusion N a)
    rw [hg]
    congr 1
    refine Subtype.ext ?_
    rw [deningerFixedSubring_quotient_smul_val]
    exact (a.2 g').symm

end Points

end RHTower
