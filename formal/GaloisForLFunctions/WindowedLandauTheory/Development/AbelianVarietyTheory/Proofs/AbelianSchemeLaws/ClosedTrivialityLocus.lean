import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.DualLineBundleSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProperFieldSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectLineBundleSections
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! On proper geometrically integral fibres, the triviality locus is closed and is
defined by the maximal minors of the two section models. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.LineBundleSections

namespace GlobalTheory.AbLaw.Seesaw

private theorem exists_ker_iff_minors {K : Type} [Field K] {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) K) :
    (∃ v : Fin a → K, v ≠ 0 ∧ D.mulVec v = 0) ↔
      ∀ σ : Fin a → Fin b, (D.submatrix σ id).det = 0 := by
  classical
  constructor
  · rintro ⟨v, hv, h⟩ σ
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, ?_⟩
    funext i
    exact congrFun h (σ i)
  · intro h
    by_contra hn
    have hinj : Function.Injective D.mulVec := by
      intro v w e
      by_contra hvw
      exact hn ⟨v - w, sub_ne_zero.2 hvw, by rw [Matrix.mulVec_sub, e, sub_self]⟩
    have hcol : LinearIndependent K D.col := Matrix.mulVec_injective_iff.1 hinj
    have hrank : D.rank = a := by
      rw [← Matrix.rank_transpose]
      simpa using (LinearIndependent.rank_matrix (M := D.transpose) hcol)
    obtain ⟨I, e, _, hspan, hli⟩ := exists_linearIndependent' K D.row
    letI : Finite I := hli.finite
    letI : Fintype I := Fintype.ofFinite I
    have hcard : Fintype.card I = a := by
      rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row, hrank]
    let η : Fin a ≃ I := (Fintype.equivFinOfCardEq hcard).symm
    have hli' : LinearIndependent K (D.submatrix (e ∘ η) id).row := hli.comp η η.injective
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hli')
    exact hu.ne_zero (h (e ∘ η))

private theorem nontrivial_ker_iff {R K : Type} [CommRing R] [Field K]
    (α : R →+* K) {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) :
    Nontrivial {v : Fin a → K // (D.map α).mulVec v = 0} ↔
      ∀ σ : Fin a → Fin b, (D.submatrix σ id).det ∈ RingHom.ker α := by
  have h := exists_ker_iff_minors (D.map α)
  have e (σ : Fin a → Fin b) : ((D.map α).submatrix σ id).det = α (D.submatrix σ id).det := by
    rw [RingHom.map_det]
    rfl
  simp only [e] at h
  simp only [RingHom.mem_ker]
  rw [← h, nontrivial_iff_exists_ne ⟨0, Matrix.mulVec_zero _⟩]
  exact ⟨fun ⟨v, hv⟩ => ⟨v.1, fun e => hv (Subtype.ext e), v.2⟩,
    fun ⟨v, hv, hv'⟩ => ⟨⟨v, hv'⟩, fun e => hv (congrArg Subtype.val e)⟩⟩

variable {R : Type} [CommRing R] {X : Scheme.{0}} {L : LB X}
  {f : X ⟶ Spec (CommRingCat.of R)}

/-- A proper integral fibre is trivial for the bundle when both section models have
nonzero kernel. -/
theorem trivial_fibre_iff_minors (hL : L.IsLB) (P : PerfectSections f L)
    (Q : PerfectSections f (dual L)) [IsProper f] [GeometricallyIntegral f]
    {K : Type} [Field K] (α : R →+* K) {Y : Scheme.{0}} {π : Y ⟶ X}
    {g : Y ⟶ Spec (CommRingCat.of K)}
    (H : IsPullback π g f (Spec.map (CommRingCat.ofHom α))) :
    (∃ t : (L.pull π).Gen, t.IsGen) ↔
      (∀ σ : Fin P.a → Fin P.b, (P.d₀.submatrix σ id).det ∈ RingHom.ker α) ∧
        (∀ σ : Fin Q.a → Fin Q.b, (Q.d₀.submatrix σ id).det ∈ RingHom.ker α) := by
  haveI : IsIntegral Y := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  haveI : IsProper g := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  haveI : GeometricallyIntegral g :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H inferInstance
  haveI : IsIso g.appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_field g
  have hunit (x : Γ(Y, ⊤)) (hx : x ≠ 0) : IsUnit x := by
    let b := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso b).2 x
    have hc : c ≠ 0 := by
      intro e
      exact hx (e ▸ map_zero b.hom)
    exact hc.isUnit.map b.hom
  obtain ⟨E, _⟩ := (P.compare K α Y π g H).1
  obtain ⟨F, _⟩ := (Q.compare K α Y π g H).1
  rw [exists_gen_iff_nontrivial_sections_and_dual (L.pull π) (hL.pull π) hunit,
    ← pull_dual, ← nontrivial_ker_iff α P.d₀, ← nontrivial_ker_iff α Q.d₀,
    E.nontrivial_congr, F.nontrivial_congr]

/-- The points over which some field fibre has a trivialization. -/
def fieldFibreTriviality (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) : Set (PrimeSpectrum R) :=
  {x | ∃ (K : Type) (_ : Field K) (α : R →+* K)
    (Y : Scheme.{0}) (π : Y ⟶ X) (g : Y ⟶ Spec (CommRingCat.of K)),
    RingHom.ker α = x.asIdeal ∧ IsPullback π g f (Spec.map (CommRingCat.ofHom α)) ∧
      ∃ t : (L.pull π).Gen, t.IsGen}

/-- The triviality locus on proper geometrically integral fibres is the common
vanishing locus of the maximal minors for the bundle and its dual. -/
theorem isClosed_triviality_locus (hL : L.IsLB) (P : PerfectSections f L)
    (Q : PerfectSections f (dual L)) [IsProper f] [GeometricallyIntegral f] :
    IsClosed (fieldFibreTriviality f L) := by
  convert PrimeSpectrum.isClosed_zeroLocus
    ((Set.range fun σ : Fin P.a → Fin P.b => (P.d₀.submatrix σ id).det) ∪
      Set.range fun σ : Fin Q.a → Fin Q.b => (Q.d₀.submatrix σ id).det) using 1
  ext x
  rw [fieldFibreTriviality, Set.mem_setOf_eq, PrimeSpectrum.mem_zeroLocus, Set.union_subset_iff,
    Set.range_subset_iff, Set.range_subset_iff]
  constructor
  · rintro ⟨K, _, α, Y, π, g, hx, H, ht⟩
    rw [← hx]
    exact (trivial_fibre_iff_minors hL P Q α H).1 ht
  · intro hx
    let K := x.asIdeal.ResidueField
    let α := algebraMap R K
    have hker : RingHom.ker α = x.asIdeal := Ideal.ker_algebraMap_residueField _
    have H := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom α))
    refine ⟨K, inferInstance, α, _, _, _, hker, H, (trivial_fibre_iff_minors hL P Q α H).2 ?_⟩
    rwa [hker]

end GlobalTheory.AbLaw.Seesaw
