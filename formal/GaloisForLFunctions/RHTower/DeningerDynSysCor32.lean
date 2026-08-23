import GaloisForLFunctions.RHTower.DeningerDynSysCor31
import GaloisForLFunctions.RHTower.DeningerDynSysStabilizerResidueField
import GaloisForLFunctions.RHTower.DeningerDynSysResidueAlgClosure

/-!
# Corollary 3.2 for an invariant extension

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 3.2.

For a profinite group acting continuously on a ring `B` with invariant subring `A`, the map
sending a pair (prime `Q` of `B`, character of `κ (Q)ˣ`) to the pair (prime `P = Q ∩ A`,
homomorphism `W_rat (κ (P)) → C`) has as its fibres exactly the orbits of the group.

Three statements make this up.  Over a fixed prime the character part is Corollary 3.1: two
characters of `κ (Q)ˣ` induce the same homomorphism of `W_rat (κ (P))` exactly when they differ by
an automorphism of `κ (Q)` over `κ (P)`, and by the profinite form of Deninger's (23) each such
automorphism comes from the stabilizer of `Q`.  On points the projection is surjective (lying over
an integral extension) and its fibres are the orbits.

The residue-field hypotheses `IsAlgClosure K L` and `IsAlgClosed L` hold in Deninger's situation
by `deningerIntegralClosureResidue_isAlgClosure`.
-/

namespace RHTower

open MulAction
open scoped Pointwise

section Fibre

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
variable (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [Algebra (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]
  [IsFractionRing (A ⧸ P) K] [IsFractionRing (B ⧸ Q) L]
variable [instInv : Algebra.IsInvariant A B G]
variable (q : ℕ) [ExpChar K q]
variable [Algebra.IsAlgebraic K L] [IsAlgClosed L] [IsAlgClosure K L]
variable [DecidableEq Lˣ] [DecidableEq (Polynomial (perfectClosure K L))]
variable {C : Type*} [Field C] [IsAlgClosed C]

include instInv q in
/-- **Deninger, Corollary 3.2, the fibre statement.**  Two characters of the residue field at `Q`
induce the same homomorphism of `W_rat` of the residue field at `P` exactly when they differ by an
element of the stabilizer of `Q` in `G`. -/
theorem deningerCharToWittHom_eq_iff_stabilizer (f₁ f₂ : Lˣ →* Cˣ) :
    deningerCharToWittHom (F := K) (E := L) f₁ = deningerCharToWittHom (F := K) (E := L) f₂
      ↔ ∃ g : MulAction.stabilizer G Q, f₂ = f₁.comp (Units.map
          (((IsFractionRing.stabilizerHom G P Q K L g : L ≃ₐ[K] L) : L →+* L) : L →* L)) := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := (deningerCharToWittHom_eq_iff (F := K) (E := L) q f₁ f₂).1 h
    obtain ⟨g, hg⟩ := deningerStabilizerHom_surjective (G := G) P Q K L σ
    exact ⟨g, by rw [hσ, hg]⟩
  · rintro ⟨g, rfl⟩
    exact (deningerCharToWittHom_comp_map (F := K) (E := L) f₁
      (IsFractionRing.stabilizerHom G P Q K L g)).symm

end Fibre

section Primes

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
variable [instInv : Algebra.IsInvariant A B G]

include instInv in
/-- **Deninger, Corollary 3.2, surjectivity on points.**  Every prime of the invariant subring is
the contraction of a prime of the ambient ring. -/
theorem deningerPrime_exists_liesOver [FaithfulSMul A B] (P : Ideal A) [P.IsPrime] :
    ∃ Q : Ideal B, Q.IsPrime ∧ Q.LiesOver P := by
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  obtain ⟨Q, -, hQp, hQ⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := B) P ⊥
      (fun a ha => by
        have h0 : algebraMap A B a = 0 := by simpa using ha
        have ha0 : a = 0 :=
          FaithfulSMul.algebraMap_injective A B (by rw [h0, map_zero])
        rw [ha0]
        exact Ideal.zero_mem _)
  exact ⟨Q, hQp, ⟨hQ.symm⟩⟩

include instInv in
/-- **Deninger, Corollary 3.2, the fibres of the projection to `X₀`.**  The group permutes the
primes above a given prime of the invariant subring transitively. -/
theorem deningerPrime_exists_smul (Q₁ Q₂ : Ideal B) [Q₁.IsPrime] [Q₂.IsPrime]
    (h : Q₁.under A = Q₂.under A) : ∃ g : G, Q₂ = g • Q₁ :=
  Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := A) (G := G) Q₁ Q₂ h

end Primes

end RHTower
