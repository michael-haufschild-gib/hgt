import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ClosedTrivialityLocus
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeGeneratorRestriction

/-! Field-fibre triviality and open trivializations can be tested on affine charts of the base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw.Seesaw

namespace GlobalTheory.AbLaw.Cube

variable {Y T : Scheme.{0}} {L : LB Y}

/-- Points admitting a field-valued lift on whose fibre the bundle is trivial. -/
def fibreTriviality (p : Y ⟶ T) (L : LB Y) : Set T :=
  {t | ∃ (K : Type) (_ : Field K) (b : Spec (CommRingCat.of K) ⟶ T)
    (Z : Scheme.{0}) (π : Z ⟶ Y) (g : Z ⟶ Spec (CommRingCat.of K)),
    t ∈ Set.range b ∧ IsPullback π g p b ∧ ∃ u : (L.pull π).Gen, u.IsGen}

/-- A trivialization over an open base restricts to every residue fibre in that open. -/
theorem mem_fibreTriviality_of_trivial_on_open (p : Y ⟶ T) {U : T.Opens}
    {t : T} (ht : t ∈ U) {u : (L.pull (p ⁻¹ᵁ U).ι).Gen} (hu : u.IsGen) :
    t ∈ fibreTriviality p L := by
  let b := T.fromSpecResidueField t
  let π := pullback.fst p b
  have hb : Set.range b = {t} := Scheme.range_fromSpecResidueField t
  have hsub : Set.range π ⊆ Set.range (p ⁻¹ᵁ U).ι := by
    dsimp only [π]
    rw [Scheme.Pullback.range_fst, hb, Scheme.Opens.range_ι]
    intro y hy
    exact (congrArg (· ∈ U) (Set.mem_singleton_iff.1 hy)).mpr ht
  let a := IsOpenImmersion.lift (p ⁻¹ᵁ U).ι π hsub
  have ha : a ≫ (p ⁻¹ᵁ U).ι = π := IsOpenImmersion.lift_fac _ _ _
  refine ⟨T.residueField t, inferInstance, b, _, π, pullback.snd p b, hb.ge rfl,
    IsPullback.of_hasPullback p b, ?_⟩
  rw [← ha]
  exact ⟨_, hu.pullGen (fun _ : PUnit => (p ⁻¹ᵁ U).ι) (fun _ => 1) a⟩

private theorem trivial_pull_comp_iff (hL : L.IsLB) {W Z : Scheme.{0}} (q : W ⟶ Y) (π : Z ⟶ W) :
    (∃ u : ((L.pull q).pull π).Gen, u.IsGen) ↔ ∃ u : (L.pull (π ≫ q)).Gen, u.IsGen :=
  trivial_pull_linComb L hL (fun _ : PUnit => q) (fun _ => 1) π

private theorem mem_range_Spec_map {R K : Type} [CommRing R] [Field K] (α : R →+* K)
    (x : PrimeSpectrum R) : x ∈ Set.range (Spec.map (CommRingCat.ofHom α)) ↔ RingHom.ker α = x.asIdeal := by
  have key (y : PrimeSpectrum K) : (PrimeSpectrum.comap α y).asIdeal = RingHom.ker α := by
    rw [PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime y.asIdeal]
    rfl
  constructor
  · rintro ⟨y, rfl⟩
    exact (key y).symm
  · intro h
    exact ⟨default, PrimeSpectrum.ext ((key _).trans h)⟩

/-- On an affine open of the base the two definitions of the fibre locus agree. -/
theorem mem_fibreTriviality_iff (hL : L.IsLB) {p : Y ⟶ T}
    {R : Type} [CommRing R] {j : Spec (CommRingCat.of R) ⟶ T} [IsOpenImmersion j]
    {W : Scheme.{0}} {q : W ⟶ Y} {f : W ⟶ Spec (CommRingCat.of R)}
    (H : IsPullback q f p j) (x : PrimeSpectrum R) :
    j x ∈ fibreTriviality p L ↔ x ∈ fieldFibreTriviality f (L.pull q) := by
  constructor
  · rintro ⟨K, _, b, Z, π, g, ⟨y, hy⟩, hp, ht⟩
    haveI : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have hsub : Set.range b ⊆ Set.range j := by
      rintro _ ⟨y', rfl⟩
      rw [Subsingleton.elim y' y, hy]
      exact ⟨x, rfl⟩
    let b' := IsOpenImmersion.lift j b hsub
    have hb' : b' ≫ j = b := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨α, hα⟩ := Spec.map_surjective b'
    have e := ((congrArg (· ≫ j) hα).trans hb')
    have w : π ≫ p = (g ≫ Spec.map α) ≫ j := by rw [hp.w, Category.assoc, e]
    let a := H.lift π (g ≫ Spec.map α) w
    have ha : a ≫ q = π := H.lift_fst _ _ _
    refine ⟨K, inferInstance, α.hom, Z, a, g, ?_, ?_, ?_⟩
    · apply (mem_range_Spec_map α.hom x).1
      refine ⟨y, j.isOpenEmbedding.injective ?_⟩
      exact (congrArg (fun b : Spec (CommRingCat.of K) ⟶ T => b y) e).trans hy
    · refine IsPullback.of_right ?_ (H.lift_snd _ _ _) H
      rw [ha]
      change IsPullback π g p (Spec.map α ≫ j)
      exact e.symm ▸ hp
    · apply (trivial_pull_comp_iff hL q a).2
      rwa [ha]
  · rintro ⟨K, _, α, Z, π, g, hα, hp, ht⟩
    obtain ⟨y, hy⟩ := (mem_range_Spec_map α x).2 hα
    exact ⟨K, inferInstance, Spec.map (CommRingCat.ofHom α) ≫ j, Z, π ≫ q, g,
      ⟨y, congrArg j hy⟩, hp.paste_horiz H, (trivial_pull_comp_iff hL q π).1 ht⟩

/-- Closed affine loci with basic-open trivializations give a closed global locus
and trivializations over neighborhoods of every point in it. -/
theorem closed_and_locally_trivial_of_affine_charts (hL : L.IsLB) (p : Y ⟶ T)
    (charts : ∀ t : T, ∃ (R : Type) (_ : CommRing R) (j : Spec (CommRingCat.of R) ⟶ T)
      (_ : IsOpenImmersion j) (x : PrimeSpectrum R) (W : Scheme.{0}) (q : W ⟶ Y)
      (f : W ⟶ Spec (CommRingCat.of R)), j x = t ∧ IsPullback q f p j ∧
        IsClosed (fieldFibreTriviality f (L.pull q)) ∧
        (∀ y ∈ fieldFibreTriviality f (L.pull q), ∃ r : R, r ∉ y.asIdeal ∧
          ∃ u : ((L.pull q).pull (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, u.IsGen)) :
    IsClosed (fibreTriviality p L) ∧
      ∀ t ∈ fibreTriviality p L, ∃ U : T.Opens, t ∈ U ∧
        ∃ u : (L.pull (p ⁻¹ᵁ U).ι).Gen, u.IsGen := by
  constructor
  · refine ⟨isOpen_iff_forall_mem_open.2 fun t ht => ?_⟩
    obtain ⟨R, _, j, _, x, W, q, f, rfl, H, hc, -⟩ := charts t
    let D := (fieldFibreTriviality f (L.pull q))ᶜ
    refine ⟨j '' D, ?_, j.isOpenEmbedding.isOpenMap D hc.isOpen_compl, x, ?_, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩ hy'
      exact hy ((mem_fibreTriviality_iff hL H y).1 hy')
    · exact fun hx => ht ((mem_fibreTriviality_iff hL H x).2 hx)
  · intro t ht
    obtain ⟨R, _, j, _, x, W, q, f, rfl, H, -, ho⟩ := charts t
    obtain ⟨r, hr, ht⟩ := ho x ((mem_fibreTriviality_iff hL H x).1 ht)
    let D := PrimeSpectrum.basicOpen r
    let U := j ''ᵁ D
    haveI : IsOpenImmersion q := MorphismProperty.of_isPullback H.flip (inferInstance : IsOpenImmersion j)
    let a := (f ⁻¹ᵁ D).ι ≫ q
    have hsub : Set.range (p ⁻¹ᵁ U).ι ⊆ Set.range a := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨x', hx', e⟩ := y.2
      obtain ⟨w, hw, hw'⟩ := Scheme.exists_preimage_of_isPullback H y.1 x' e.symm
      exact ⟨⟨w, (congrArg (· ∈ D) hw').mpr hx'⟩, hw⟩
    let b := IsOpenImmersion.lift a (p ⁻¹ᵁ U).ι hsub
    have hb : b ≫ a = (p ⁻¹ᵁ U).ι := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨v, hv⟩ := (trivial_pull_comp_iff hL q (f ⁻¹ᵁ D).ι).1 ht
    refine ⟨U, ⟨x, hr, rfl⟩, ?_⟩
    rw [← hb]
    exact ⟨_, hv.pullGen (fun _ : PUnit => a) (fun _ => 1) b⟩

end GlobalTheory.AbLaw.Cube
