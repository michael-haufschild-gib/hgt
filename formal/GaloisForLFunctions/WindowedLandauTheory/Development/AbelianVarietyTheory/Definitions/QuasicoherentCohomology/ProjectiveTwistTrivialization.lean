import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveTwistSections

/-! Powers of a degree-one coordinate trivialize each twist on its coordinate open. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology.ProjTwist

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

private def coordinateFraction (u : A) (k : ℤ) (x : ProjectiveSpectrum 𝒜)
    (hx : u ∉ x.asHomogeneousIdeal) : Loc 𝒜 x :=
  Localization.mk (u ^ k.toNat) ⟨u ^ (-k).toNat, fun h => hx (x.isPrime.mem_of_pow_mem _ h)⟩

private theorem coordinateFraction_mul_neg (u : A) (k : ℤ) (x : ProjectiveSpectrum 𝒜)
    (hx : u ∉ x.asHomogeneousIdeal) :
    coordinateFraction u k x hx * coordinateFraction u (-k) x hx = 1 := by
  rw [coordinateFraction, coordinateFraction, Localization.mk_mul, ← Localization.mk_one,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [neg_neg, Submonoid.coe_mul, Submonoid.coe_one, one_mul, mul_one]
  ring

private theorem isLocallyFraction_coordinateFraction {v : A} (hv : v ∈ 𝒜 1) (k : ℤ)
    {W : (Proj 𝒜).Opens} (hW : W ≤ Proj.basicOpen 𝒜 v) :
    (isLocallyFraction 𝒜 k).pred (fun x : W => coordinateFraction v k x.1 (hW x.2)) := by
  intro x
  refine ⟨W, x.2, 𝟙 W, (-k).toNat, k.toNat, by omega, v ^ k.toNat, v ^ (-k).toNat, ?_, ?_,
    fun y h => nmem_of_mem (𝒜 := 𝒜) ⟨y.1, hW y.2⟩ (y.1.isPrime.mem_of_pow_mem _ h), fun _ => rfl⟩
  · simpa [smul_eq_mul] using SetLike.pow_mem_graded k.toNat hv
  · simpa [smul_eq_mul] using SetLike.pow_mem_graded (-k).toNat hv

/-- The section (v^k) on the coordinate open where (v) is invertible. -/
def coordinatePower {v : A} (hv : v ∈ 𝒜 1) (k : ℤ) :
    Γ(twistingSheaf 𝒜 k, Proj.basicOpen 𝒜 v) :=
  mkSection (fun x => coordinateFraction v k x.1 x.2)
    (isLocallyFraction_coordinateFraction hv k le_rfl)

/-- The coordinate power generates the twist freely on every subopen of its chart. -/
theorem coordinatePower_basis {v : A} (hv : v ∈ 𝒜 1) (k : ℤ)
    {W : (Proj 𝒜).Opens} (hW : W ≤ Proj.basicOpen 𝒜 v) :
    Function.Bijective (fun r : Γ(Proj 𝒜, W) =>
      r • (twistingSheaf 𝒜 k).presheaf.map (homOfLE hW).op (coordinatePower hv k)) := by
  let s := (twistingSheaf 𝒜 k).presheaf.map (homOfLE hW).op (coordinatePower hv k)
  have hs (x : W) : val s x = coordinateFraction v k x.1 (hW x.2) := rfl
  constructor
  · intro a b hab
    apply Subtype.ext
    funext x
    apply HomogeneousLocalization.val_injective
    have hx := congrArg (fun z => val z x) hab
    change val (a • s) x = val (b • s) x at hx
    rw [val_smul, val_smul, hs] at hx
    have hinv := coordinateFraction_mul_neg v k x.1 (hW x.2)
    simpa only [mul_assoc, hinv, mul_one] using
      congrArg (· * coordinateFraction v (-k) x.1 (hW x.2)) hx
  · intro z
    obtain ⟨r, hr⟩ := exists_section_of_isLocallyFraction_zero _
      (isLocallyFraction_mul (add_neg_cancel k) (isLocallyFraction_val z)
        (isLocallyFraction_coordinateFraction hv (-k) hW))
    refine ⟨r, ?_⟩
    ext x
    rw [val_smul, hs, hr]
    change val z x * coordinateFraction v (-k) x.1 (hW x.2) *
      coordinateFraction v k x.1 (hW x.2) = val z x
    rw [mul_assoc, mul_comm (coordinateFraction v (-k) x.1 (hW x.2)),
      coordinateFraction_mul_neg, mul_one]

/-- A degree-zero ratio of coordinates (v/u), regular over the (u)-chart. -/
def coordinateRatio {u v : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1) :
    Γ(Proj 𝒜, Proj.basicOpen 𝒜 u) :=
  (Proj.awayToSection 𝒜 u).hom
    (HomogeneousLocalization.mk ⟨1, ⟨v, hv⟩, ⟨u, hu⟩, ⟨1, pow_one u⟩⟩)

private theorem coordinateRatio_val {u v : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1)
    (x : Proj.basicOpen 𝒜 u) :
    ((coordinateRatio hu hv).1 x).val = Localization.mk v ⟨u, x.2⟩ := by
  change (HomogeneousLocalization.mk ⟨1, ⟨v, hv⟩, ⟨u, hu⟩, x.2⟩).val = _
  rw [HomogeneousLocalization.val_mk]

/-- Inverting the ratio of two coordinates restricts to their common chart. -/
theorem basicOpen_coordinateRatio {u v : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1) :
    (Proj 𝒜).basicOpen (coordinateRatio hu hv) = Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v := by
  ext x
  change x ∈ (Proj 𝒜).basicOpen (coordinateRatio hu hv) ↔
    x ∈ Proj.basicOpen 𝒜 u ∧ x ∈ Proj.basicOpen 𝒜 v
  rw [Scheme.mem_basicOpen'']
  have hunit (hx : x ∈ Proj.basicOpen 𝒜 u) :
      IsUnit ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ _ x hx
        (coordinateRatio hu hv)) ↔ x ∈ Proj.basicOpen 𝒜 v := by
    let e := Proj.stalkIso' 𝒜 x
    have h : IsUnit (e ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ _ x hx
        (coordinateRatio hu hv))) ↔ x ∈ Proj.basicOpen 𝒜 v := by
      dsimp only [e]
      erw [Proj.stalkIso'_germ]
      rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
      erw [coordinateRatio_val]
      rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
      rfl
    exact ⟨fun h' => h.mp (h'.map e), fun h' => by
      simpa only [RingEquiv.symm_apply_apply] using (h.mpr h').map e.symm⟩
  exact ⟨fun ⟨hx, h⟩ => ⟨hx, (hunit hx).mp h⟩, fun ⟨hx, h⟩ => ⟨hx, (hunit hx).mpr h⟩⟩

theorem coordinateRatio_self {u : A} (hu : u ∈ 𝒜 1) : coordinateRatio hu hu = 1 := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  erw [coordinateRatio_val, Proj.one_apply, HomogeneousLocalization.val_one]
  exact Localization.mk_self ⟨u, x.2⟩

theorem coordinateRatio_mul {u v w : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1) (hw : w ∈ 𝒜 1) :
    let W := Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v
    (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : W ≤ Proj.basicOpen 𝒜 u)).op
        (coordinateRatio hu hv) *
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_right : W ≤ Proj.basicOpen 𝒜 v)).op
        (coordinateRatio hv hw) =
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : W ≤ Proj.basicOpen 𝒜 u)).op
        (coordinateRatio hu hw) := by
  dsimp only
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change ((coordinateRatio hu hv).1 ⟨x.1, x.2.1⟩ * (coordinateRatio hv hw).1 ⟨x.1, x.2.2⟩).val = _
  rw [HomogeneousLocalization.val_mul]
  erw [coordinateRatio_val, coordinateRatio_val, coordinateRatio_val]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]; ring⟩

/-- The two negative coordinate powers differ by the transition ratio on their common chart. -/
theorem coordinatePower_neg_overlap {u v : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1) (m : ℕ) :
    let W := Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v
    let F := twistingSheaf 𝒜 (-(m : ℤ))
    F.presheaf.map (homOfLE (inf_le_left : W ≤ Proj.basicOpen 𝒜 u)).op
        (coordinatePower hu (-(m : ℤ))) =
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : W ≤ Proj.basicOpen 𝒜 u)).op
        (coordinateRatio hu hv) ^ m •
      F.presheaf.map (homOfLE (inf_le_right : W ≤ Proj.basicOpen 𝒜 v)).op
        (coordinatePower hv (-(m : ℤ))) := by
  dsimp only
  apply ProjTwist.ext
  funext x
  rw [val_smul]
  change coordinateFraction u (-(m : ℤ)) x.1 x.2.1 =
    (((coordinateRatio hu hv).1 ⟨x.1, x.2.1⟩) ^ m).val *
      coordinateFraction v (-(m : ℤ)) x.1 x.2.2
  rw [HomogeneousLocalization.val_pow, coordinateRatio_val]
  simp only [coordinateFraction, Int.toNat_neg_natCast, neg_neg, Int.toNat_natCast, pow_zero,
    Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one,
    one_mul, mul_one]⟩

end GlobalTheory.SchemeCohomology.ProjTwist
