import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysInvariantPoints
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Points of an invariant extension with values in a valuation ring

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 1.6(2) (`t212n`)
and Corollary 1.7(1) (`t213n`).

Let `𝔬` be an integrally closed subring of an algebraically closed field `C` with `C` as its
fraction field — for instance a rank-one valuation ring with algebraically closed quotient field,
which is the source's hypothesis.  For a ring `B` with a continuous action of a profinite group `G`
and invariant subring `A`, restriction induces a bijection

`Hom (B, 𝔬) / G ≅ Hom (A, 𝔬)`.

The key point (`deningerHom_mem_of_mem_of_isIntegral`) is the source's remark that *any* extension
`B → C` of a homomorphism `A → 𝔬` automatically takes values in `𝔬`: every `b ∈ B` is integral
over `A`, so its image is integral over `𝔬`, and `𝔬` is integrally closed in `C`.  Surjectivity
and injectivity then follow from the corresponding statements over `C`.
-/

namespace RHTower

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
variable {C : Type*} [Field C]

omit [TopologicalSpace B] [DiscreteTopology B] in
/-- An extension to `B` of a homomorphism `A → 𝔬` into an integrally closed subring of `C` again
takes values in `𝔬`, because `B` is integral over `A`. -/
theorem deningerHom_mem_of_mem_of_isIntegral [Algebra.IsIntegral A B]
    (O : Subring C) [IsIntegrallyClosed O] [Algebra O C] [IsFractionRing O C]
    (halg : ∀ x : O, (algebraMap O C) x = (x : C))
    (ψ : B →+* C) (hφ : ∀ a : A, ψ (algebraMap A B a) ∈ O) (b : B) : ψ b ∈ O := by
  classical
  obtain ⟨F, hFmonic, hF⟩ := Algebra.IsIntegral.isIntegral (R := A) (A := B) b
  set φ : A →+* O := (ψ.comp (algebraMap A B)).codRestrict O hφ with hφdef
  have hcomp : (algebraMap O C).comp φ = ψ.comp (algebraMap A B) := by
    ext a
    show (algebraMap O C) (φ a) = ψ (algebraMap A B a)
    rw [halg]
    rfl
  have hint : IsIntegral O (ψ b) := by
    refine ⟨F.map φ, hFmonic.map φ, ?_⟩
    show Polynomial.eval₂ (algebraMap O C) (ψ b) (F.map φ) = 0
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hF, map_zero]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := C)).mp hint
  rw [halg] at hy
  exact hy ▸ y.2

/-- **Deninger, Lemma 1.6(2) / Corollary 1.7(1) (`t212n`, `t213n`), surjectivity.**  Restriction
to the invariants is surjective on homomorphisms into an integrally closed subring of an
algebraically closed field with that field as fraction field. -/
theorem deningerHomValued_restrict_surjective [Algebra.IsInvariant A B G] [FaithfulSMul A B]
    [IsAlgClosed C] (O : Subring C) [IsIntegrallyClosed O] [Algebra O C] [IsFractionRing O C]
    (halg : ∀ x : O, (algebraMap O C) x = (x : C)) :
    Function.Surjective (fun ψ : B →+* O => ψ.comp (algebraMap A B)) := by
  intro φ
  haveI : Algebra.IsIntegral A B :=
    Algebra.IsInvariant.isIntegral_of_profinite (A := A) (B := B) (G := G)
  obtain ⟨ψ, hψ⟩ := deningerHom_exists_extension (A := A) (B := B) (G := G)
    ((O.subtype).comp φ)
  have hmem : ∀ b : B, ψ b ∈ O := by
    refine deningerHom_mem_of_mem_of_isIntegral (A := A) O halg ψ ?_
    intro a
    rw [hψ a]
    exact (φ a).2
  refine ⟨ψ.codRestrict O hmem, ?_⟩
  ext a
  show ψ (algebraMap A B a) = (φ a : C)
  rw [hψ a]
  rfl

/-- **Deninger, Lemma 1.6(2) / Corollary 1.7(1), injectivity modulo `G`.** -/
theorem deningerHomValued_restrict_eq_iff [Algebra.IsInvariant A B G] (O : Subring C)
    (ψ₁ ψ₂ : B →+* O) :
    ψ₁.comp (algebraMap A B) = ψ₂.comp (algebraMap A B)
      ↔ ∃ g : G, ∀ b : B, ψ₂ b = ψ₁ (g • b) := by
  constructor
  · intro h
    have h' : (O.subtype.comp ψ₁).comp (algebraMap A B)
        = (O.subtype.comp ψ₂).comp (algebraMap A B) := by
      rw [RingHom.comp_assoc, RingHom.comp_assoc, h]
    obtain ⟨g, hg⟩ := (deningerHom_restrict_eq_iff (A := A) (G := G) _ _).mp h'
    exact ⟨g, fun b => Subtype.ext (hg b)⟩
  · rintro ⟨g, hg⟩
    refine RingHom.ext fun a => ?_
    show ψ₁ (algebraMap A B a) = ψ₂ (algebraMap A B a)
    rw [hg (algebraMap A B a), smul_algebraMap]

end RHTower
