import GaloisForLFunctions.HTGeometry.DGroupSourceRankLaw
import GaloisForLFunctions.HTGeometry.SpanRankMaximalSubfamily

/-!
# The numerical source-boundary rank identity

The differential rank of a finite family of observables shifting by base increments equals the
rank, over the constant-coefficient differential operators, of the span of the boundary classes of
those increments.

Both numbers are computed by the same subfamily: a maximal linearly independent set of boundary
classes is, by the source-boundary law, also a maximal differentially independent subfamily of the
observables.  On the linear side its size is the rank of the span, because the quotient by its span
is torsion; on the differential side it is a basis of the differential matroid.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C K L : Type u} [Field C] [Field K] [Field L]
  [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
  [Differential K] [Differential L] [DifferentialAlgebra K L] [CharZero K] [CharZero L]
  {I : Type u} (tau : I → K ≃+* K) (sigma : I → L ≃+* L)

/-- **The numerical form of the source-boundary rank law.**  The differential rank of the family
and the operator rank of the span of its boundary classes are the same natural number. -/
theorem eRk_eq_rank_span_boundaryClass
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ w : L, (∀ i, sigma i w = w) → ∃ c : C, algebraMap C L c = w)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    {κ : Type u} [Fintype κ] [DecidableEq κ] (z : κ → L) (omega : I → κ → K)
    (hshift : ∀ i p, sigma i (z p) = z p + algebraMap K L (omega i p)) :
    ∃ r : ℕ,
      (differentialMatroid K L).eRk (Set.range z) = r ∧
      Module.rank (Polynomial C) (Submodule.span (Polynomial C)
        (Set.range fun p : κ => boundaryClass tau hC hfix hderiv fun i => omega i p)) = r := by
  classical
  set B : κ → sourceBoundaryModule tau hC hfix hderiv :=
    fun p => boundaryClass tau hC hfix hderiv fun i => omega i p with hBdef
  obtain ⟨T, hTind, htor, hdep⟩ :=
    exists_maximal_linearIndepOn_finset (R := Polynomial C) B
  have hequiv : ∀ (κ' : Type u) (e : κ' → κ),
      DifferentialIndependent K (fun t : κ' => z (e t)) ↔
        LinearIndependent (Polynomial C) (fun t : κ' => B (e t)) := by
    intro κ' e
    exact differentialIndependent_iff_linearIndependent_boundaryClass tau sigma hcomp hderivL
      hCfixed hfixed hC hfix hderiv (fun t => z (e t)) (fun i t => omega i (e t))
      (fun i t => hshift i (e t))
  have hTdiff : DifferentialIndependent K (fun t : ((T : Set κ)) => z t) :=
    (hequiv _ (Subtype.val : ((T : Set κ)) → κ)).2 hTind
  have hinjT : Set.InjOn z (T : Set κ) := by
    intro a ha b hb hab
    have := hTdiff.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab
    exact congrArg Subtype.val this
  have hDiffOn : DiffIndepOn K (z '' (T : Set κ)) := by
    let e : ((T : Set κ)) ≃ (z '' (T : Set κ) : Set L) :=
      Equiv.Set.imageOfInjOn z (T : Set κ) hinjT
    refine (GaloisForLFunctions.differentialIndependent_equiv e
      (Subtype.val : (z '' (T : Set κ) : Set L) → L)).1 ?_
    exact hTdiff
  refine ⟨T.card, ?_, ?_⟩
  · have hclosure : ∀ k : κ, z k ∈ differentialClosure K (z '' (T : Set κ)) := by
      intro k
      by_cases hzk : z k ∈ z '' (T : Set κ)
      · exact subset_differentialClosure _ hzk
      · have hkT : k ∉ T := by
          intro hk
          exact hzk ⟨k, hk, rfl⟩
        have hnotind := hdep k hkT
        have hnotdiff : ¬ DifferentialIndependent K
            (fun t : (((insert k T : Finset κ) : Set κ)) => z t) := by
          intro hcon
          exact hnotind ((hequiv _ (Subtype.val : _ → κ)).1 hcon)
        have hinjIns : Set.InjOn z ((insert k T : Finset κ) : Set κ) := by
          rw [Finset.coe_insert]
          intro a ha b hb hab
          rcases ha with rfl | ha
          · rcases hb with rfl | hb
            · rfl
            · exact absurd (hab ▸ ⟨b, hb, rfl⟩ : z a ∈ z '' (T : Set κ)) hzk
          · rcases hb with rfl | hb
            · exact absurd (hab ▸ ⟨a, ha, rfl⟩ : z b ∈ z '' (T : Set κ)) hzk
            · exact hinjT ha hb hab
        have hnotOn : ¬ DiffIndepOn K (z '' ((insert k T : Finset κ) : Set κ)) := by
          intro hcon
          apply hnotdiff
          let e : (((insert k T : Finset κ) : Set κ)) ≃
              (z '' ((insert k T : Finset κ) : Set κ) : Set L) :=
            Equiv.Set.imageOfInjOn z _ hinjIns
          exact (GaloisForLFunctions.differentialIndependent_equiv e
            (Subtype.val : (z '' ((insert k T : Finset κ) : Set κ) : Set L) → L)).2 hcon
        rw [Finset.coe_insert, Set.image_insert_eq, diffIndepOn_insert_iff hzk] at hnotOn
        push Not at hnotOn
        exact hnotOn hDiffOn
    have hbasis : (differentialMatroid K L).IsBasis (z '' (T : Set κ)) (Set.range z) := by
      refine Matroid.Indep.isBasis_of_subset_of_subset_closure
        (differentialMatroid_indep_iff.2 hDiffOn) ?_ ?_
      · rintro - ⟨t, ht, rfl⟩
        exact ⟨t, rfl⟩
      · rintro - ⟨k, rfl⟩
        rw [differentialMatroid_closure_eq_differentialClosure]
        exact hclosure k
    rw [← hbasis.encard_eq_eRk, hinjT.encard_image, Set.encard_coe_eq_coe_finsetCard]
  · have hs : LinearIndepOn (Polynomial C) id (B '' (T : Set κ)) := hTind.id_image
    rw [rank_span_eq_mk_of_torsion_generators B (B '' (T : Set κ)) hs
      (Set.image_subset_range _ _) htor]
    rw [Cardinal.mk_image_eq_of_injOn _ _ hTind.injOn]
    simp

/-- **Equation `(7)`.**  For a family of points of a commutative algebraic `D`-group with an
arbitrary source family, the differential rank of the coordinates of the points equals the rank of
the span of the boundary classes of their logarithmic source increments. -/
theorem dGroup_eRk_coordFamily_eq_rank_span_boundaryClass
    {G : Type*} [CommGroup G] {n d : ℕ}
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ w : L, (∀ i, sigma i w = w) → ∃ c : C, algebraMap C L c = w)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    {P : DGroupPresentation G K L n d} {S : Type u} [Fintype S] [DecidableEq S] {g : S → G}
    (Dat : DGroupSourceData P sigma g) :
    ∃ r : ℕ,
      (differentialMatroid K L).eRk (Set.range (P.coordFamily g)) = r ∧
      Module.rank (Polynomial C) (Submodule.span (Polynomial C)
        (Set.range fun p : S × Fin d =>
          boundaryClass tau hC hfix hderiv fun i => Dat.omegaFamily i p)) = r := by
  classical
  obtain ⟨r, hrk, hrank⟩ := eRk_eq_rank_span_boundaryClass tau sigma hcomp hderivL hCfixed hfixed
    hC hfix hderiv (P.ellFamily g) Dat.omegaFamily (fun i p => Dat.sigma_ellFamily i p)
  exact ⟨r, (P.eRk_coordFamily_eq_ellFamily g).trans hrk, hrank⟩

end

end GaloisForLFunctions.HTGeometry
