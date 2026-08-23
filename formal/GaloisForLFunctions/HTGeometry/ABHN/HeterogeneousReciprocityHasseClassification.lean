import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryHeterogeneousReciprocity

/-!
# Hasse classification for heterogeneous reciprocity profiles

Arbitrary place-dependent `ℚ/ℤ` invariants, finite torsion specializations, and literal cyclic carry
`H²` profiles are classified modulo their zero-sum reciprocity kernels.  Representative existence
is stated over the subgroup actually realized by the local maps.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u v

/-- The heterogeneous quotient equivalence is induced by the invariant-sum map. -/
@[simp] theorem heterogeneousRatModIntProfileInvariantSumQuotientEquivRange_mk
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (f : Π₀ i, A i) :
    (heterogeneousRatModIntProfileInvariantSumQuotientEquivRange A inv
      (QuotientAddGroup.mk f)).1 =
        heterogeneousRatModIntProfileInvariantSumAddHom A inv f := rfl

/-- Heterogeneous profiles have equal global invariant sum exactly when their difference is
reciprocal. -/
theorem heterogeneousRatModIntProfile_congr_hasse_iff
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (f g : Π₀ i, A i) :
    f - g ∈ (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker ↔
      heterogeneousRatModIntProfileInvariantSumAddHom A inv f =
        heterogeneousRatModIntProfileInvariantSumAddHom A inv g := by
  change heterogeneousRatModIntProfileInvariantSumAddHom A inv (f - g) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every realized heterogeneous invariant has a profile representative, unique modulo reciprocal
profiles. -/
theorem heterogeneousRatModIntProfile_exists_unique_mod_reciprocity
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt)
    (z : (heterogeneousRatModIntProfileInvariantSumAddHom A inv).range) :
    ∃ f : Π₀ i, A i,
      heterogeneousRatModIntProfileInvariantSumAddHom A inv f = z.1 ∧
      ∀ g : Π₀ i, A i,
        heterogeneousRatModIntProfileInvariantSumAddHom A inv g = z.1 ↔
          g - f ∈ (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker := by
  obtain ⟨f, hf⟩ := z.2
  refine ⟨f, hf, fun g => ?_⟩
  rw [← hf]
  exact (heterogeneousRatModIntProfile_congr_hasse_iff A inv g f).symm

/-- Place-dependent finite-torsion profiles have equal invariant sum exactly modulo their
reciprocity kernel. -/
theorem heterogeneousTorsionProfile_congr_hasse_iff
    {ι : Type u} [DecidableEq ι] (A : ι → Type v)
    [(i : ι) → AddCommGroup (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i))
    (f g : Π₀ i, A i) :
    f - g ∈ (heterogeneousTorsionProfileInvariantSumAddHom A n e).ker ↔
      heterogeneousTorsionProfileInvariantSumAddHom A n e f =
        heterogeneousTorsionProfileInvariantSumAddHom A n e g :=
  heterogeneousRatModIntProfile_congr_hasse_iff A
    (heterogeneousTorsionLocalInvariantAddHom A n e) f g

/-- Every realized heterogeneous finite-torsion invariant has a profile representative unique
modulo reciprocity. -/
theorem heterogeneousTorsionProfile_exists_unique_mod_reciprocity
    {ι : Type u} [DecidableEq ι] (A : ι → Type v)
    [(i : ι) → AddCommGroup (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i))
    (z : (heterogeneousTorsionProfileInvariantSumAddHom A n e).range) :
    ∃ f : Π₀ i, A i,
      heterogeneousTorsionProfileInvariantSumAddHom A n e f = z.1 ∧
      ∀ g : Π₀ i, A i,
        heterogeneousTorsionProfileInvariantSumAddHom A n e g = z.1 ↔
          g - f ∈ (heterogeneousTorsionProfileInvariantSumAddHom A n e).ker :=
  heterogeneousRatModIntProfile_exists_unique_mod_reciprocity A
    (heterogeneousTorsionLocalInvariantAddHom A n e) z

universe w


variable {ι : Type w} [DecidableEq ι]
  (K L : ι → Type)
  [(i : ι) → Field (K i)] [(i : ι) → Field (L i)]
  [(i : ι) → Algebra (K i) (L i)]
  [(i : ι) → FiniteDimensional (K i) (L i)]
  [(i : ι) → IsGalois (K i) (L i)]
  [(i : ι) → IsCyclic Gal(L i / K i)]
  (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
  (qEquiv : ∀ i,
    Additive (K i)ˣ ⧸ cyclicGaloisH2BaseNormImage (K i) (L i) ≃+ ZMod (n i))

local instance heterogeneousReciprocityHasseDecidableEq (i : ι) :
    DecidableEq (cyclicGaloisH2 (K i) (L i)) := Classical.decEq _

/-- Literal cyclic carry profiles have equal all-place invariant sum exactly modulo heterogeneous
reciprocity. -/
theorem cyclicGaloisCarryH2Heterogeneous_congr_hasse_iff
    (f g : Π₀ i, cyclicGaloisH2 (K i) (L i)) :
    f - g ∈
        (cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv).ker ↔
      cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv f =
        cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv g :=
  heterogeneousTorsionProfile_congr_hasse_iff
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv) f g

/-- Every invariant sum realized by heterogeneous cyclic carry classes has a profile representative
unique modulo reciprocity. -/
theorem cyclicGaloisCarryH2Heterogeneous_exists_unique_mod_reciprocity
    (z : (cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv).range) :
    ∃ f : Π₀ i, cyclicGaloisH2 (K i) (L i),
      cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv f = z.1 ∧
      ∀ g : Π₀ i, cyclicGaloisH2 (K i) (L i),
        cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv g = z.1 ↔
          g - f ∈
            (cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv).ker :=
  heterogeneousTorsionProfile_exists_unique_mod_reciprocity
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv) z

end
end GaloisForLFunctions.HTGeometry.ABHN
