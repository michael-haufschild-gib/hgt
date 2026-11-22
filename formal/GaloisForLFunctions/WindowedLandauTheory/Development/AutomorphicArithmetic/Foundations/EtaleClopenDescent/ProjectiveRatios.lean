import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveCoordinateScalars

/-! A ratio of forms of the same degree is a regular section on the
denominator chart. Its invertibility locus is the common chart. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology

universe u

section Graded

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ}

/-- The section (v/u) over the chart where (u) is invertible. -/
def homogeneousRatio {u v : A} (hu : u ∈ 𝒜 d) (hv : v ∈ 𝒜 d) :
    Γ(Proj 𝒜, Proj.basicOpen 𝒜 u) :=
  (Proj.awayToSection 𝒜 u).hom
    (HomogeneousLocalization.mk ⟨d, ⟨v, hv⟩, ⟨u, hu⟩, ⟨1, pow_one u⟩⟩)

theorem homogeneousRatio_val {u v : A} (hu : u ∈ 𝒜 d) (hv : v ∈ 𝒜 d)
    (x : Proj.basicOpen 𝒜 u) :
    ((homogeneousRatio hu hv).1 x).val = Localization.mk v ⟨u, x.2⟩ := by
  change (HomogeneousLocalization.mk ⟨d, ⟨v, hv⟩, ⟨u, hu⟩, x.2⟩).val = _
  rw [HomogeneousLocalization.val_mk]

/-- A point in the denominator chart lies in the basic open of the ratio
precisely when the numerator is invertible there. -/
theorem basicOpen_homogeneousRatio {u v : A} (hu : u ∈ 𝒜 d) (hv : v ∈ 𝒜 d) :
    (Proj 𝒜).basicOpen (homogeneousRatio hu hv) = Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v := by
  ext x
  change x ∈ (Proj 𝒜).basicOpen (homogeneousRatio hu hv) ↔
    x ∈ Proj.basicOpen 𝒜 u ∧ x ∈ Proj.basicOpen 𝒜 v
  rw [Scheme.mem_basicOpen'']
  have hunit (hx : x ∈ Proj.basicOpen 𝒜 u) :
      IsUnit ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ _ x hx
        (homogeneousRatio hu hv)) ↔ x ∈ Proj.basicOpen 𝒜 v := by
    let e := Proj.stalkIso' 𝒜 x
    have h : IsUnit (e ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ _ x hx
        (homogeneousRatio hu hv))) ↔ x ∈ Proj.basicOpen 𝒜 v := by
      dsimp only [e]
      erw [Proj.stalkIso'_germ]
      rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
      erw [homogeneousRatio_val]
      rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
      rfl
    exact ⟨fun h' => h.mp (h'.map e), fun h' => by
      simpa only [RingEquiv.symm_apply_apply] using (h.mpr h').map e.symm⟩
  exact ⟨fun ⟨hx, h⟩ => ⟨hx, (hunit hx).mp h⟩, fun ⟨hx, h⟩ => ⟨hx, (hunit hx).mpr h⟩⟩

theorem homogeneousRatio_self {u : A} (hu : u ∈ 𝒜 d) : homogeneousRatio hu hu = 1 := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  erw [homogeneousRatio_val, Proj.one_apply, HomogeneousLocalization.val_one]
  exact Localization.mk_self ⟨u, x.2⟩

theorem homogeneousRatio_add {u v w : A} (hu : u ∈ 𝒜 d) (hv : v ∈ 𝒜 d) (hw : w ∈ 𝒜 d) :
    homogeneousRatio hu (add_mem hv hw) = homogeneousRatio hu hv + homogeneousRatio hu hw := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change ((homogeneousRatio hu (add_mem hv hw)).1 x).val =
    ((homogeneousRatio hu hv).1 x + (homogeneousRatio hu hw).1 x).val
  rw [HomogeneousLocalization.val_add]
  erw [homogeneousRatio_val, homogeneousRatio_val, homogeneousRatio_val]
  exact (Localization.add_mk_self _ _ _).symm

end Graded

open UpperTheory.Cb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [CommRing K] {N d : ℕ}

private abbrev Grade (K : Type u) [CommRing K] (N : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

/-- On the chart of a homogeneous denominator of positive degree, dividing
by the denominator is linear in the numerator. -/
def pspaceRatioLinear {u : MvPolynomial (Fin (N + 1)) K} (hu : u ∈ Grade K N d) (hd : 0 < d) :
    letI := sectionAlgebra (PSpace.str K N) (Proj.basicOpen (Grade K N) u)
    Grade K N d →ₗ[K] Γ(PSpace K N, Proj.basicOpen (Grade K N) u) := by
  let W := Proj.basicOpen (Grade K N) u
  letI := sectionAlgebra (PSpace.str K N) W
  refine { toFun := fun v => homogeneousRatio hu v.2
           map_add' := fun a b => homogeneousRatio_add hu a.2 b.2
           map_smul' := ?_ }
  intro r v
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change ((homogeneousRatio hu (Submodule.smul_mem _ r v.2)).1 x).val =
    (((algebraMap K Γ(PSpace K N, W) r).1 x) * (homogeneousRatio hu v.2).1 x).val
  rw [HomogeneousLocalization.val_mul]
  erw [homogeneousRatio_val, homogeneousRatio_val, pspace_algebraMap_basicOpen_val N hu hd]
  rw [MvPolynomial.smul_eq_C_mul, Localization.mk_eq_mk', Localization.mk_eq_mk']
  exact (IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _).symm

/-- The ratio after pullback to a scheme over projective space. -/
def projectiveRatio {X : Scheme.{u}} (i : X ⟶ PSpace K N)
    {u v : MvPolynomial (Fin (N + 1)) K} (hu : u ∈ Grade K N d) (hv : v ∈ Grade K N d) :
    Γ(X, i ⁻¹ᵁ Proj.basicOpen (Grade K N) u) :=
  (i.app _).hom (homogeneousRatio hu hv)

theorem basicOpen_projectiveRatio {X : Scheme.{u}} (i : X ⟶ PSpace K N)
    {u v : MvPolynomial (Fin (N + 1)) K} (hu : u ∈ Grade K N d) (hv : v ∈ Grade K N d) :
    X.basicOpen (projectiveRatio i hu hv) =
      (i ⁻¹ᵁ Proj.basicOpen (Grade K N) u) ⊓ (i ⁻¹ᵁ Proj.basicOpen (Grade K N) v) := by
  change X.basicOpen ((i.app _).hom (homogeneousRatio hu hv)) = _
  rw [← i.preimage_basicOpen, basicOpen_homogeneousRatio]
  rfl

end GlobalTheory.SchemeCohomology
