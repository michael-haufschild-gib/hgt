import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.PerfectSectionsTriviality
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.SeesawKernelPivot
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Ideal.Nonunits

/-! Near a trivial fibre, the scheme where a line bundle becomes trivial is cut out by a
finite set of matrix entries. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.SchemeCohomology GlobalTheory.LineBundleSections

namespace GlobalTheory.AbLaw.Seesaw

variable {R S : Type} [CommRing R] [CommRing S] {X Y : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of S)} {π : Y ⟶ X}

private theorem mem_basicOpen_scalar (W : Y.Opens) (c : S) {y : Y} (hy : y ∈ W) :
    letI := sectionAlgebra g W
    y ∈ Y.basicOpen (algebraMap S Γ(Y, W) c) ↔ c ∉ (g y).asIdeal := by
  let b := (Scheme.ΓSpecIso (CommRingCat.of S)).inv c
  change y ∈ Y.basicOpen (g.appLE ⊤ W le_top b) ↔ _
  rw [Scheme.basicOpen_appLE, basicOpen_eq_of_affine]
  exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩

private theorem isUnit_of_unit_values {L : LB X} (P : PerfectSections f L)
    [Surjective g] (c : S) (v : Fin P.a → S)
    (hv : ∀ i, IsUnit (P.value π g (c • v) i)) : IsUnit c := by
  by_contra hc
  obtain ⟨m, hm, hcm⟩ := exists_max_ideal_of_mem_nonunits hc
  obtain ⟨y, hy⟩ := g.surjective (⟨m, hm.isPrime⟩ : PrimeSpectrum S)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (P.cover.ge (Set.mem_univ (π y)))
  have h := hv i
  rw [PerfectSections.value_smul] at h
  have hW : y ∈ π ⁻¹ᵁ P.W i := hi
  letI := sectionAlgebra g (π ⁻¹ᵁ P.W i)
  have hunit : IsUnit (algebraMap S Γ(Y, π ⁻¹ᵁ P.W i) c) := isUnit_of_mul_isUnit_left h
  have hx : y ∈ Y.basicOpen (algebraMap S Γ(Y, π ⁻¹ᵁ P.W i) c) := by
    rw [Y.basicOpen_of_isUnit hunit]
    exact hW
  have hn := (mem_basicOpen_scalar (g := g) _ c hW).1 hx
  exact hn (hy.symm ▸ hcm)

/-- The see-saw lemma on an affine base. The determinantal neighborhood contains the given
fibre, and on that neighborhood a finite ideal represents triviality under base change. -/
theorem triviality_locus_near_fibre {L : LB X} (hL : L.IsLB) [UniversallyClosed f] [Surjective f]
    (P : PerfectSections f L) {K : Type} [Field K] (α₀ : R →+* K)
    {X₀ : Scheme.{0}} {π₀ : X₀ ⟶ X} {f₀ : X₀ ⟶ Spec (CommRingCat.of K)}
    (H₀ : IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom α₀)))
    (hΓ : Function.Surjective f₀.appTop) (ht : ∃ t : (L.pull π₀).Gen, t.IsGen) :
    ∃ (r : R) (I : Ideal R), α₀ r ≠ 0 ∧ I.FG ∧
      ∀ (S : Type) [CommRing S] (α : R →+* S) (Y : Scheme.{0})
        (π : Y ⟶ X) (g : Y ⟶ Spec (CommRingCat.of S)),
        IsPullback π g f (Spec.map (CommRingCat.ofHom α)) → IsUnit (α r) →
          ((∃ t : (L.pull π).Gen, t.IsGen) ↔ I ≤ RingHom.ker α) := by
  obtain ⟨v, hv, hu, hline⟩ := P.values_of_trivial hL H₀ ht
  haveI : Surjective f₀ := MorphismProperty.of_isPullback H₀ inferInstance
  have hv₀ : v ≠ 0 := by
    intro e
    have h := isUnit_of_unit_values P (π := π₀) (g := f₀) (0 : K) 0
      (by rw [zero_smul, ← e]; exact hu)
    exact not_isUnit_zero h
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector α₀ P.d₀ v hv₀ (hline hΓ)
  let z : Spec (CommRingCat.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  let W : X.Opens := ⨆ i, X.basicOpen (P.valueBase v₀ i)
  have hclosed : IsClosed (f '' (W : Set X)ᶜ) := f.isClosedMap _ W.isOpen.isClosed_compl
  have hz : Spec.map (CommRingCat.ofHom α₀) z ∈ (f '' (W : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, hfx⟩
    obtain ⟨y, rfl, _⟩ := Scheme.exists_preimage_of_isPullback H₀ x z hfx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (P.cover.ge (Set.mem_univ (π₀ y)))
    obtain ⟨c, hc⟩ := hker K α₀ hδ.isUnit v hv
    have u := hu i
    rw [hc, PerfectSections.value_smul, P.value_comp H₀] at u
    have hmem : y ∈ X₀.basicOpen (π₀.app (P.W i) (P.valueBase v₀ i)) := by
      rw [X₀.basicOpen_of_isUnit (isUnit_of_mul_isUnit_right u)]
      exact hi
    rw [← Scheme.preimage_basicOpen] at hmem
    exact hx (Opens.mem_iSup.mpr ⟨i, hmem⟩)
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      hz hclosed.isOpen_compl
  have hr₀ : α₀ r ≠ 0 := hr
  refine ⟨δ * r, Ideal.span (Set.range (P.d₀.mulVec v₀)), ?_,
    Submodule.fg_span (Set.finite_range _), ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hδ hr₀
  intro S _ α Y π g H hunit
  haveI : Surjective g := MorphismProperty.of_isPullback H inferInstance
  rw [map_mul] at hunit
  have hI : Ideal.span (Set.range (P.d₀.mulVec v₀)) ≤ RingHom.ker α ↔
      (P.d₀.map α).mulVec (α ∘ v₀) = 0 := by
    rw [Ideal.span_le, Set.range_subset_iff, funext_iff]
    refine forall_congr' fun j => ?_
    rw [← RingHom.map_mulVec]
    rfl
  rw [hI]
  constructor
  · intro Ht
    obtain ⟨w, hw, hw', _⟩ := P.values_of_trivial hL H Ht
    obtain ⟨c, rfl⟩ := hker S α (isUnit_of_mul_isUnit_left hunit) w hw
    rw [Matrix.mulVec_smul] at hw
    exact ((isUnit_of_unit_values P c _ hw').smul_eq_zero).1 hw
  · intro Hker
    refine P.trivial_of_values H Hker fun y => ?_
    have hy : π y ∈ W := by
      by_contra hy
      have e : f (π y) = Spec.map (CommRingCat.ofHom α) (g y) := congrArg (fun q => q y) H.w
      have hm : f (π y) ∈ PrimeSpectrum.basicOpen r := by
        rw [e]
        change α r ∉ (g y).asIdeal
        exact fun hn => (g y).isPrime.ne_top
          (Ideal.eq_top_of_isUnit_mem _ hn (isUnit_of_mul_isUnit_right hunit))
      exact hsub hm ⟨π y, hy, rfl⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    refine ⟨i, ?_⟩
    rw [P.value_comp H, ← Scheme.preimage_basicOpen]
    exact hi

end GlobalTheory.AbLaw.Seesaw
