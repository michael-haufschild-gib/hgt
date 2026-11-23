import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AugmentedCechExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechEdgeBoundary
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverFormRestrictions
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineCoverCechExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsQuasicoherent

/-! Right columns in a joined cover of a smooth scheme are augmented
Čech complexes of relative forms on the affine left intersections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry
open GlobalTheory.CechDR GlobalTheory.WH GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

local instance columnHasExt (X : Scheme.{0}) :
    HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X.carrier) := hasExt_of_enoughInjectives _

variable {k ι κ : Type} [Field k] [LinearOrder ι] [LinearOrder κ]
  {X : Scheme.{0}} [IsIntegral X] {s : X ⟶ Spec (CommRingCat.of k)}
  [Algebra k X.functionField] [Smooth s] {U : ι → X.Opens} {V : κ → X.Opens}
  {B : Finset (ι ⊕ₗ κ) → Subalgebra k X.functionField}

private abbrev G (p : ℕ) (I : Finset (ι ⊕ₗ κ)) := omB k X.functionField (B I) p

/-- The right Čech cover of each affine left intersection is exact,
including its degree-zero augmentation. -/
theorem IsAffCover.rightColumn_exact (h : IsAffCover s (joinedCover U V) B)
    (hV : iSup V = ⊤) (p : ℕ) (I : Finset ι) (hI : I.Nonempty) (n : ℤ) :
    (acx (fun J => G (B := B) p (uni I J)) 1).Z n ≤
      (acx (fun J => G (B := B) p (uni I J)) 1).B n := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeForms s p)
  let V₀ := I.inf U
  let D := sheafCech F V₀ V
  let W (J : Finset κ) := coverInter V₀ V J
  let W' (J : Finset κ) := coverInter ⊤ (joinedCover U V) (uni I J)
  have hIJ (J : Finset κ) : (uni I J).Nonempty := by
    rw [← Finset.card_pos, card_uni]
    have he := Finset.card_pos.mpr hI
    omega
  have hW (J : Finset κ) : W J = W' J := by
    simp only [W, W', V₀, coverInter, top_inf_eq, inf_joinedCover, lft_uni, rgt_uni]
  have haff (J : Finset κ) : IsAffineOpen (W J) := by
    rw [hW J]
    simpa only [W', coverInter, top_inf_eq] using h.affine (uni I J) (hIJ J)
  have haff₀ : IsAffineOpen V₀ := by
    have he : IsAffineOpen (coverInter V₀ V (∅ : Finset κ)) := haff ∅
    rwa [coverInter_empty] at he
  have hcov : V₀ ≤ iSup V := by rw [hV]; exact le_top
  let u (J : Finset κ) : D.obj J ≃+ (h.formCechDatum p).obj (uni I J) :=
    (F.1.mapIso (eqToIso (hW J).symm).op).addCommGroupIsoToAddEquiv
  let e (J : Finset κ) : D.obj J ≃+ G (B := B) p (uni I J) :=
    (u J).trans (h.sectionRationalForms (hIJ J) p)
  letI := relativeForms_isQuasicoherent s p
  refine acx_exact_of_cechDatum D _ e (fun {J K} hJK x => ?_)
    (sheafCech_exactBot F hcov)
    (quasicoherent_cech_exactAt_of_isAffine (relativeForms s p) haff₀ hcov (fun J _ => haff J)) n
  have h' : uni I J ⊆ uni I K :=
    Finset.map_subset_map.mpr (Finset.disjSum_mono subset_rfl hJK)
  have hu : u K (D.res hJK x) = (h.formCechDatum p).res h' (u J x) := by
    change F.1.map (eqToHom (hW K).symm).op
      (F.1.map (homOfLE (coverInter_anti (V := V₀) (U := V) hJK)).op x) =
      F.1.map (homOfLE (coverInter_anti (V := ⊤) (U := joinedCover U V) h')).op
        (F.1.map (eqToHom (hW J).symm).op x)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
  change (h.sectionRationalForms (hIJ K) p (u K (D.res hJK x)) : DR k X.functionField) =
    h.sectionRationalForms (hIJ J) p (u J x)
  rw [hu]
  exact h.sectionRationalForms_res (hIJ J) h' p (u J x)

/-- Right columns of the left-supported complex are exact, including
the zero column whose left index set is empty. -/
theorem IsAffCover.leftSupported_rightColumns_exact (h : IsAffCover s (joinedCover U V) B)
    (hV : iSup V = ⊤) (p : ℕ) (I : Finset ι) (n : ℤ) :
    (rightColumn (leftSupported (G (B := B) p)) 1 I).Z n ≤
      (rightColumn (leftSupported (G (B := B) p)) 1 I).B n := by
  change (acx (fun J => leftSupported (G (B := B) p) (uni I J)) 1).Z n ≤
    (acx (fun J => leftSupported (G (B := B) p) (uni I J)) 1).B n
  by_cases hI : I.Nonempty
  · simpa only [leftSupported, lft_uni, if_pos hI] using h.rightColumn_exact hV p I hI n
  · intro c hc
    have h₀ : c = 0 := funext fun J => (Submodule.mem_bot k).mp (by
      simpa only [leftSupported, lft_uni, if_neg hI, ite_self] using acx_mem_terms_iff.mp hc.1 J)
    rw [h₀]
    exact zero_mem _

/-- A mixed primitive for the edge of a regular left cocycle gives a
regular primitive on the left affine cover. -/
theorem IsAffCover.leftBoundary_of_mixedEdge [Fintype ι] [Fintype κ]
    (h : IsAffCover s (joinedCover U V) B) (hV : iSup V = ⊤) (p q : ℕ)
    {a : Finset ι → DR k X.functionField}
    (ha : a ∈ (cech (fun I => G (B := B) p (uni I (∅ : Finset κ)))).Z q)
    (hb : edge1 a ∈ (mixedCech (fun I J => G (B := B) p (uni I J))).B ((q : ℤ) + 2)) :
    a ∈ (cech (fun I => G (B := B) p (uni I (∅ : Finset κ)))).B q := by
  refine left_boundary_of_edge_boundary (G (B := B) p) ?_
    (h.leftSupported_rightColumns_exact hV p) ha hb
  apply acx_isCx _ _ (fun _ _ => Commute.one_left _)
  intro t i _ m hm
  change m ∈ leftSupported (G (B := B) p) (insert i t)
  by_cases ht : (lft t).Nonempty
  · have ht' : t.Nonempty := by
      rcases t.eq_empty_or_nonempty with rfl | ht'
      · obtain ⟨j, hj⟩ := ht
        exact (by simpa only [lft, Finset.mem_toLeft, Finset.map_empty,
          Finset.notMem_empty] using hj : False).elim
      · exact ht'
    have hsub := Finset.subset_insert i t
    have hi : (lft (insert i t)).Nonempty := ht.mono
      (Finset.toLeft_monotone (Finset.map_subset_map.mpr hsub))
    rw [leftSupported, if_pos ht] at hm
    rw [leftSupported, if_pos hi]
    exact omB_mono (h.algebra_le ht' hsub) p hm
  · have hzero : m = 0 := (Submodule.mem_bot k).mp (by
      simpa only [leftSupported, if_neg ht] using hm)
    rw [hzero]
    exact zero_mem _

end GlobalTheory.PD
