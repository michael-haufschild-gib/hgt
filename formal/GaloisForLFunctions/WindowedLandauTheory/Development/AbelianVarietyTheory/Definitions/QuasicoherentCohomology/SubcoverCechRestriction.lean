import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.GodementCechComparison

/-! Restriction of sheaf Čech cochains to a subcover indexed by an order
embedding. -/

noncomputable section

open CategoryTheory Opposite TopologicalSpace HTGeometry
open GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.SchemeCohomology

variable {X : TopCat.{0}} {ι κ : Type} [DecidableEq ι] [LinearOrder ι]
  [DecidableEq κ] [LinearOrder κ] (V : Opens X) (U : ι → Opens X) (j : κ ↪o ι)

omit [DecidableEq ι] [DecidableEq κ] in
theorem coverInter_orderEmbedding (I : Finset κ) :
    coverInter V U (I.map j.toEmbedding) = coverInter V (U ∘ j) I := by
  rw [coverInter, coverInter, Finset.inf_map]
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
/-- An order-preserving inclusion preserves the Čech deletion sign. -/
theorem cechSign_orderEmbedding {R : Type*} [CommRing R] (I : Finset κ) (i : κ) :
    (cechSign (I.map j.toEmbedding) (j i) : R) = cechSign I i := by
  have hf : I.filter ((· < j i) ∘ j.toEmbedding) = I.filter (· < i) :=
    Finset.filter_congr fun a _ => j.lt_iff_lt
  rw [cechSign, cechSign, belowCard, belowCard, Finset.filter_map, Finset.card_map, hf]

variable (F : TopCat.Sheaf AddCommGrpCat.{0} X)

/-- Restrict a cochain to intersections that use indices of the subcover. -/
def subcoverCochain (a : (sheafCech F V U).Cochain) :
    (sheafCech F V (U ∘ j)).Cochain := fun I =>
  F.1.map (eqToHom (coverInter_orderEmbedding V U j I).symm).op (a (I.map j.toEmbedding))

theorem subcoverCochain_d (a : (sheafCech F V U).Cochain) :
    subcoverCochain V U j F ((sheafCech F V U).d a) =
      (sheafCech F V (U ∘ j)).d (subcoverCochain V U j F a) := by
  funext I
  let D := sheafCech F V U
  let E := sheafCech F V (U ∘ j)
  let e (I : Finset κ) := eqToHom (coverInter_orderEmbedding V U j I).symm
  let m := j.toEmbedding
  change F.1.map (e I).op (D.d a (I.map m)) = E.d (subcoverCochain V U j F a) I
  rw [FinsetCechDatum.d, FinsetCechDatum.d, Finset.sum_map]
  refine (map_sum (F.1.map (e I).op).hom _ I).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : (cechSign (I.map m) (m i) : ℤ) = cechSign I i := cechSign_orderEmbedding j I i
  refine (map_zsmul (F.1.map (e I).op).hom _ _).trans (congrArg₂ (· • ·) hs ?_)
  have he : (I.map m).erase (j i) = (I.erase i).map m := (Finset.map_erase m I i).symm
  have hsub : (I.erase i).map m ⊆ I.map m :=
    (Finset.map_subset_map (f := m)).mpr (Finset.erase_subset i I)
  refine (congrArg (F.1.map (e I).op).hom
    (D.res_cochain_congr a he (Finset.erase_subset _ _) hsub)).trans ?_
  let r := homOfLE (coverInter_anti (V := V) (U := U) hsub)
  let r' := homOfLE (coverInter_anti (V := V) (U := U ∘ j) (Finset.erase_subset i I))
  change F.1.map (e I).op (F.1.map r.op (a ((I.erase i).map m))) =
    F.1.map r'.op (F.1.map (e (I.erase i)).op (a ((I.erase i).map m)))
  have hcomp : r.op ≫ (e I).op = (e (I.erase i)).op ≫ r'.op := Subsingleton.elim _ _
  let z := a ((I.erase i).map m)
  exact (ConcreteCategory.congr_hom (F.1.map_comp r.op (e I).op) z).symm.trans
    ((ConcreteCategory.congr_hom (congrArg F.1.map hcomp) z).trans
      (ConcreteCategory.congr_hom (F.1.map_comp (e (I.erase i)).op r'.op) z))

private def subcoverDegreeMap (n : ℕ) :
    (sheafCechComplex V U F).X n ⟶ (sheafCechComplex V (U ∘ j) F).X n :=
  AddCommGrpCat.ofHom
    { toFun := fun a => ⟨subcoverCochain V U j F a.1, fun I hI => by
        unfold subcoverCochain
        rw [a.2 _ (by rwa [Finset.card_map])]
        exact (F.1.map (eqToHom (coverInter_orderEmbedding V U j I).symm).op).hom.map_zero⟩
      map_zero' := Subtype.ext (funext fun I => map_zero _)
      map_add' := fun a b => Subtype.ext (funext fun I => map_add _ _ _) }

/-- Restriction to the subcover commutes with the differential. -/
def subcoverCechMap : sheafCechComplex V U F ⟶ sheafCechComplex V (U ∘ j) F :=
  CochainComplex.ofHom (subcoverDegreeMap V U j F) (by
    intro n
    apply AddCommGrpCat.ext
    intro a
    apply Subtype.ext
    let D := sheafCech F V U
    let E := sheafCech F V (U ∘ j)
    have he := congrArg Subtype.val
      (FinsetCechDatum.cochainComplex_d_apply E n (subcoverDegreeMap V U j F n a))
    have hd := congrArg (fun v : D.degreeCochains (n + 1) => subcoverCochain V U j F v.1)
      (FinsetCechDatum.cochainComplex_d_apply D n a)
    exact he.trans ((subcoverCochain_d V U j F a.1).symm.trans hd.symm))

theorem subcoverCechMap_apply (n : ℕ) (a : (sheafCech F V U).degreeCochains n) (I : Finset κ) :
    ((subcoverCechMap V U j F).f n a).val I = subcoverCochain V U j F a.1 I :=
  rfl

theorem subcoverCechMap_natural {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (φ : F ⟶ G) :
    sheafCechComplexMap V U φ ≫ subcoverCechMap V U j G =
      subcoverCechMap V U j F ≫ sheafCechComplexMap V (U ∘ j) φ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro z
  apply Subtype.ext
  funext I
  let e := eqToHom (coverInter_orderEmbedding V U j I).symm
  exact ConcreteCategory.congr_hom (φ.1.naturality e.op).symm (z.val (I.map j.toEmbedding))

/-- Restriction to a subcover is natural in the coefficient sheaf. -/
def subcoverCechNatTrans :
    abelianCechFunctor X V U ⟶ abelianCechFunctor X V (U ∘ j) where
  app := subcoverCechMap V U j
  naturality := fun {_ _} φ => subcoverCechMap_natural V U j φ

end GlobalTheory.SchemeCohomology
