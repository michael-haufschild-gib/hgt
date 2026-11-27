import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineCechJoinComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CechOrderReindex

/-! Two covers with affine mixed intersections compute ordinary coherent
cohomology by their mixed Čech complex. A third affine cover compares both
complexes through exact augmented slices. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace HTGeometry
open HTGeometry.FinsetCechDatum GlobalTheory.WH GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {K : Type} [Field K] {X : Scheme.{0}}
  (f : X ⟶ Spec (.of K)) (F : X.Modules)
  {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → X.Opens) (V : κ → X.Opens) (W : ν → X.Opens)

private theorem map_join_assoc (I : Finset ι) (J : Finset κ) (L : Finset ν) :
    (uni (uni I J) L).map (OrderIso.sumLexAssoc ι κ ν).toEquiv.toEmbedding = uni I (uni J L) := by
  ext s
  rw [Finset.mem_map_equiv]
  obtain ⟨s, rfl⟩ := toLex.surjective s
  rcases s with i | s
  · change toLex (Sum.inl (toLex (Sum.inl i))) ∈ uni (uni I J) L ↔
      toLex (Sum.inl i) ∈ uni I (uni J L)
    simp [uni]
  · obtain ⟨s, rfl⟩ := toLex.surjective s
    rcases s with j | l
    · change toLex (Sum.inl (toLex (Sum.inr j))) ∈ uni (uni I J) L ↔
        toLex (Sum.inr (toLex (Sum.inl j))) ∈ uni I (uni J L)
      simp [uni]
    · change toLex (Sum.inr l) ∈ uni (uni I J) L ↔
        toLex (Sum.inr (toLex (Sum.inr l))) ∈ uni I (uni J L)
      simp [uni]

private theorem cover_join_assoc :
    joinedCover U (joinedCover V W) ∘ OrderIso.sumLexAssoc ι κ ν =
      joinedCover (joinedCover U V) W := by
  funext s
  obtain ⟨s, rfl⟩ := toLex.surjective s
  rcases s with s | l
  · obtain ⟨s, rfl⟩ := toLex.surjective s
    rcases s <;> rfl
  · rfl

private theorem nonempty_homology_equiv_join_assoc
    (P : Set (Finset ι)) (Q : Set (Finset κ)) (S : Set (Finset ν))
    (hP : P.OrdConnected) (hQ : Q.OrdConnected) (hS : S.OrdConnected) (n : ℕ) :
    Nonempty ((cechOnSupport f F (joinedCover (joinedCover U V) W) (joinedSupport (joinedSupport P Q) S)
      (joinedSupport_ordConnected (joinedSupport_ordConnected hP hQ) hS)).homology n ≃ₗ[K]
      (cechOnSupport f F (joinedCover U (joinedCover V W)) (joinedSupport P (joinedSupport Q S))
        (joinedSupport_ordConnected hP (joinedSupport_ordConnected hQ hS))).homology n) := by
  let j := OrderIso.sumLexAssoc ι κ ν
  let m (s : Finset ((ι ⊕ₗ κ) ⊕ₗ ν)) := s.map j.toEquiv.toEmbedding
  have hm : Monotone m := fun _ _ h => Finset.map_subset_map.2 h
  let E := joinedCover U (joinedCover V W)
  let E' := joinedCover (joinedCover U V) W
  let D := sectionDatum F E
  letI (s : Finset (ι ⊕ₗ (κ ⊕ₗ ν))) := sectionDatumModule f F E s
  let R := joinedSupport P (joinedSupport Q S)
  let hR := joinedSupport_ordConnected hP (joinedSupport_ordConnected hQ hS)
  let T := D.truncate (R := K) R hR
  have hp : m ⁻¹' R = joinedSupport (joinedSupport P Q) S := by
    ext s
    obtain ⟨a, L, rfl⟩ : ∃ a L, s = uni a L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    obtain ⟨I, J, rfl⟩ : ∃ I J, a = uni I J := ⟨lft a, rgt a, (uni_lft_rgt a).symm⟩
    simp only [Set.mem_preimage, m, j, map_join_assoc, R, joinedSupport, Set.mem_setOf_eq, lft_uni, rgt_uni]
    exact and_assoc.symm
  have e (s : Finset ((ι ⊕ₗ κ) ⊕ₗ ν)) :
      coverInter (⊤ : X.Opens) E (m s) = coverInter ⊤ E' s := by
    exact (coverInter_orderEmbedding (⊤ : X.Opens) E j.toOrderEmbedding s).trans
      (congrArg (fun v => coverInter ⊤ v s) (cover_join_assoc U V W))
  obtain ⟨A⟩ := nonempty_homology_equiv_cechSlice f F E E' m hm R hR e n
  let B := T.linearComplexIsoReindex (D.truncate_linear R hR (res_base_smul f F E)) j
  rw [← cechOnSupport_congr f F E' (hR.preimage_mono hm)
    (joinedSupport_ordConnected (joinedSupport_ordConnected hP hQ) hS) hp]
  exact ⟨A.trans (HomologicalComplex.homologyMapIso B.symm n).toLinearEquiv⟩

private theorem affine_inf_of_le {T : Type} [LinearOrder T] (E : T → X.Opens)
    (hE : ∀ i B, IsAffineOpen B → IsAffineOpen (E i ⊓ B))
    (I : Finset T) {B : X.Opens} (hB : IsAffineOpen B) (h : I.inf E ≤ B) :
    IsAffineOpen (I.inf E) := by
  have e : coverInter B E I = I.inf E := inf_eq_right.mpr h
  exact e ▸ affine_coverInter_of_inter_affine E hE hB I

variable [HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X)] [F.IsQuasicoherent]
  [Fintype ι] [Fintype κ] [Fintype ν]

/-- Ordinary Čech cohomology on an affine cover and mixed Čech cohomology
on a pair of covers agree, with the degree shifted by one. -/
theorem nonempty_homology_equiv_affine_mixed
    (hU : ∀ i B, IsAffineOpen B → IsAffineOpen (U i ⊓ B))
    (hV : ∀ j B, IsAffineOpen B → IsAffineOpen (V j ⊓ B))
    (hW : ∀ k B, IsAffineOpen B → IsAffineOpen (W k ⊓ B))
    (haff : ∀ k, IsAffineOpen (W k)) (hUV : ∀ i j, IsAffineOpen (U i ⊓ V j))
    (cU : ⨆ i, U i = ⊤) (cV : ⨆ j, V j = ⊤) (cW : ⨆ k, W k = ⊤) (n : ℕ) :
    Nonempty ((cech f F W).homology n ≃ₗ[K]
      (cechOnSupport f F (joinedCover U V)
        (joinedSupport (nonemptyIntersections ι) (nonemptyIntersections κ))
        (joinedSupport_ordConnected (nonemptyIntersections_ordConnected ι)
          (nonemptyIntersections_ordConnected κ))).homology (n + 1)) := by
  let P := nonemptyIntersections ι
  let Q := nonemptyIntersections κ
  let R := nonemptyIntersections ν
  let hP := nonemptyIntersections_ordConnected ι
  let hQ := nonemptyIntersections_ordConnected κ
  let hR := nonemptyIntersections_ordConnected ν
  have hUV₁ (s : ι ⊕ₗ κ) (B : X.Opens) (hB : IsAffineOpen B) :
      IsAffineOpen (joinedCover U V s ⊓ B) := by
    obtain ⟨s, rfl⟩ := toLex.surjective s
    rcases s with i | j
    · exact hU i B hB
    · exact hV j B hB
  have hVW₁ (s : κ ⊕ₗ ν) (B : X.Opens) (hB : IsAffineOpen B) :
      IsAffineOpen (joinedCover V W s ⊓ B) := by
    obtain ⟨s, rfl⟩ := toLex.surjective s
    rcases s with j | k
    · exact hV j B hB
    · exact hW k B hB
  have hWa (I : Finset ν) (hI : I ∈ R) : IsAffineOpen (I.inf W) := by
    obtain ⟨k, hk⟩ := hI
    exact affine_inf_of_le W hW I (haff k) (Finset.inf_le hk)
  have hUVa (s : Finset (ι ⊕ₗ κ)) (hs : s ∈ joinedSupport P Q) :
      IsAffineOpen (s.inf (joinedCover U V)) := by
    obtain ⟨i, hi⟩ := hs.1
    obtain ⟨j, hj⟩ := hs.2
    refine affine_inf_of_le (joinedCover U V) hUV₁ s (hUV i j) ?_
    rw [inf_joinedCover]
    exact inf_le_inf (Finset.inf_le hi) (Finset.inf_le hj)
  have hVWa (s : Finset (κ ⊕ₗ ν)) (hs : s ∈ joinedSupport Q R) :
      IsAffineOpen (s.inf (joinedCover V W)) := by
    obtain ⟨k, hk⟩ := hs.2
    refine affine_inf_of_le (joinedCover V W) hVW₁ s (haff k) ?_
    rw [inf_joinedCover]
    exact inf_le_right.trans (Finset.inf_le hk)
  obtain ⟨A⟩ := nonempty_homology_equiv_affine_rightJoin f F V W R hR
    (by simp [R, nonemptyIntersections]) hWa hV cV n
  obtain ⟨B⟩ := nonempty_homology_equiv_affine_rightJoin f F U (joinedCover V W)
    (joinedSupport Q R) (joinedSupport_ordConnected hQ hR)
    (by
      rw [← uni_empty_empty (ι := κ) (κ := ν)]
      intro hs
      exact Finset.not_nonempty_empty (by
        simpa only [lft_uni] using (show (lft (uni (∅ : Finset κ) (∅ : Finset ν))).Nonempty from hs.1)))
    hVWa hU cU (n + 1)
  obtain ⟨C⟩ := nonempty_homology_equiv_join_assoc f F U V W P Q R hP hQ hR (n + 2)
  obtain ⟨E⟩ := nonempty_homology_equiv_affine_leftJoin f F (joinedCover U V) W
    (joinedSupport P Q) (joinedSupport_ordConnected hP hQ)
    (by
      rw [← uni_empty_empty (ι := ι) (κ := κ)]
      intro hs
      exact Finset.not_nonempty_empty (by
        simpa only [lft_uni] using (show (lft (uni (∅ : Finset ι) (∅ : Finset κ))).Nonempty from hs.1)))
    hUVa hW cW (n + 1)
  exact ⟨(HomologicalComplex.homologyMapIso (cechOnNonemptyIso f F W).symm n).toLinearEquiv.trans
    (A.trans (B.trans (C.symm.trans E.symm)))⟩

end GlobalTheory.LineBundleSections
