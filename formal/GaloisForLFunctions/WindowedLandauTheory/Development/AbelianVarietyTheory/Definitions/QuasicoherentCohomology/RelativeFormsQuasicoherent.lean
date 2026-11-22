import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.QuasicoherenceOnAffines

/-! The sheaves of relative forms are quasi-coherent. -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (s : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)

/-- Sections of relative forms on a basic open are obtained by clearing
denominators, and the kernel of restriction is the denominator torsion. -/
theorem relativeForms_localization {U V : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) (e : V = X.basicOpen g) (i : V ⟶ U) :
    (∀ y : Γ(relativeForms s n, V), ∃ (m : ℕ) (x : Γ(relativeForms s n, U)),
      (relativeForms s n).presheaf.map i.op x = (X.presheaf.map i.op g) ^ m • y) ∧
    ∀ x : Γ(relativeForms s n, U), (relativeForms s n).presheaf.map i.op x = 0 →
      ∃ m : ℕ, g ^ m • x = 0 := by
  subst V
  have hi : i = homOfLE (X.basicOpen_le g) := Subsingleton.elim _ _
  subst i
  let A := affineFormsSections s n hU
  let B := affineFormsSections s n (hU.basicOpen g)
  have H := formsOn_basicOpen (s := s) hU (show SectionRing s U from g) n
  let r := sectionRes s (homOfLE (X.basicOpen_le g))
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨ω, rfl⟩ := B.surjective y
    obtain ⟨m, ξ, hξ⟩ := H.1 ω
    refine ⟨m, A ξ, ?_⟩
    change (relativeForms s n).presheaf.map (homOfLE (X.basicOpen_le g)).op
      (formsOnToSections s n U ξ) = (r g) ^ m • B ω
    rw [formsOnToSections_res, ← hξ]
    exact B.map_smul _ _
  · intro x hx
    obtain ⟨ω, rfl⟩ := A.surjective x
    have e' := (formsOnToSections_res s n (homOfLE (X.basicOpen_le g)) ω).symm.trans hx
    have hzero : ExteriorDifferentials.map r n ω = 0 :=
      B.injective (e'.trans (B.map_zero).symm)
    obtain ⟨m, hm⟩ := H.2 ω hzero
    exact ⟨m, (A.map_smul (g ^ m) ω).symm.trans ((congrArg A hm).trans A.map_zero)⟩

/-- Restriction of relative forms on affine opens satisfies the basic-open
localization criterion. -/
theorem relativeForms_isQuasicoherent : (relativeForms s n).IsQuasicoherent := by
  let U : {V : X.Opens // IsAffineOpen V} → X.Opens := Subtype.val
  have hcov : IsOpenCover U := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hx⟩
  refine isQuasicoherent_of_affineCover_localization (relativeForms s n) U hcov
    (fun i => i.property) (fun i f => ?_)
  obtain ⟨hs, hk⟩ := relativeForms_localization s n i.property f rfl
    (homOfLE (X.basicOpen_le f))
  exact ⟨fun y => by obtain ⟨m, x, hx⟩ := hs y; exact ⟨m, x, hx.symm⟩, hk⟩

end GlobalTheory.SchemeCohomology
