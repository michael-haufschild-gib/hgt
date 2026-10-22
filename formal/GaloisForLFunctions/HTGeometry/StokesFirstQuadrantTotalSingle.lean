import GaloisForLFunctions.HTGeometry.StokesFirstQuadrantTotalExact
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Totalization of a bicomplex concentrated in one outer degree

Work with chain complexes, indexed by `ℕ`, of module presheaves over a presheaf of commutative
rings `A` on a small category. For a chain complex `R` and `p : ℕ`, place `R` in outer degree `p`
to get a first-quadrant bicomplex. Its total complex is isomorphic to `R` shifted up by `p` with
every differential multiplied by the sign `ε(p) = (-1)^p`; the sign twist is itself isomorphic to
`R` by rescaling degree `n` by `ε(p)^n`. These isomorphisms are natural in `R`, so totalizing the
single-row bicomplex preserves quasi-isomorphisms.

## Main results

- `totalSingleIso`: the total complex of the bicomplex with `R` in outer degree `p` is isomorphic
  to the sign-twisted shift `shiftedSignTwist A R p`.
- `totalSingleIso_naturality`: this isomorphism is natural in `R`.
- `signTwistIso`: the sign-twisted complex is isomorphic to `R`.
- `totalSingleMap_quasiIso`: if `φ : R ⟶ S` is a quasi-isomorphism, so is the induced map of
  total complexes of the single-row bicomplexes.

## Hypotheses

Unconditional. The quasi-isomorphism statements take `[QuasiIso φ]` as their input.
-/

open CategoryTheory Category Limits

universe u

namespace GaloisForLFunctions.IrregularStokes.FirstQuadrantTotalSingle

variable {C : Type u} [SmallCategory C]
variable (A : Cᵒᵖ ⥤ CommRingCat.{u})

/-- Module presheaves over the ring presheaf `A`. -/
abbrev M :=
  GaloisForLFunctions.IrregularStokes.FirstQuadrantTotalExact.ModulePresheaf A

/-- Multiplication by a sign `s ∈ ℤˣ` as an automorphism of an object. -/
noncomputable def unitsSmulIso (X : M A) (s : ℤˣ) : X ≅ X where
  hom := s • 𝟙 X
  inv := s⁻¹ • 𝟙 X
  hom_inv_id := by
    simp [Linear.comp_units_smul, smul_smul]
  inv_hom_id := by
    simp [Linear.comp_units_smul, smul_smul]

/-- The complex `R` with every differential multiplied by the sign `ε(p) = (-1)^p`. -/
noncomputable def signTwist (R : ChainComplex (M A) ℕ) (p : ℕ) :
    ChainComplex (M A) ℕ where
  X := R.X
  d i j := (ComplexShape.down ℕ).ε p • R.d i j
  shape i j hij := by rw [R.shape i j hij, smul_zero]
  d_comp_d' i j k hij hjk := by
    simp [Linear.units_smul_comp, Linear.comp_units_smul,
      R.d_comp_d i j k]

/-- A chain map induces a chain map between sign twists, with the same components. -/
noncomputable def signTwistMap {R S : ChainComplex (M A) ℕ} (φ : R ⟶ S) (p : ℕ) :
    signTwist A R p ⟶ signTwist A S p where
  f := φ.f
  comm' i j hij := by
    dsimp [signTwist]
    rw [Linear.comp_units_smul, Linear.units_smul_comp, φ.comm i j]

/-- The sign twist of `R` is isomorphic to `R`, rescaling degree `n` by `ε(p)^n`. -/
noncomputable def signTwistIso (R : ChainComplex (M A) ℕ) (p : ℕ) :
    signTwist A R p ≅ R :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => unitsSmulIso A (R.X n) (((ComplexShape.down ℕ).ε p) ^ n))
    (fun i j hij => by
      change j + 1 = i at hij
      subst i
      dsimp [signTwist, unitsSmulIso]
      simp only [Linear.units_smul_comp, Linear.comp_units_smul, id_comp, comp_id,
        smul_smul]
      congr 1
      exact pow_succ _ _)

@[simp]
lemma signTwistIso_hom_f (R : ChainComplex (M A) ℕ) (p n : ℕ) :
    (signTwistIso A R p).hom.f n =
      ((ComplexShape.down ℕ).ε p) ^ n • 𝟙 (R.X n) := rfl

@[simp]
lemma signTwistIso_inv_f (R : ChainComplex (M A) ℕ) (p n : ℕ) :
    (signTwistIso A R p).inv.f n =
      (((ComplexShape.down ℕ).ε p) ^ n)⁻¹ • 𝟙 (R.X n) := rfl

/-- The isomorphism `signTwistIso` is natural in the complex. -/
lemma signTwistIso_naturality {R S : ChainComplex (M A) ℕ} (φ : R ⟶ S) (p : ℕ) :
    signTwistMap A φ p ≫ (signTwistIso A S p).hom =
      (signTwistIso A R p).hom ≫ φ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change φ.f n ≫ (((ComplexShape.down ℕ).ε p) ^ n • 𝟙 (S.X n)) =
    (((ComplexShape.down ℕ).ε p) ^ n • 𝟙 (R.X n)) ≫ φ.f n
  rw [Linear.comp_units_smul, Linear.units_smul_comp, comp_id, id_comp]

/-- Sign twisting preserves quasi-isomorphisms. -/
theorem signTwistMap_quasiIso {R S : ChainComplex (M A) ℕ} (φ : R ⟶ S)
    [QuasiIso φ] (p : ℕ) : QuasiIso (signTwistMap A φ p) := by
  haveI : QuasiIso (signTwistMap A φ p ≫ (signTwistIso A S p).hom) := by
    rw [signTwistIso_naturality A φ p]
    infer_instance
  exact quasiIso_of_comp_right
    (signTwistMap A φ p) (signTwistIso A S p).hom

/-- The embedding `n ↦ n + p` of the descending `ℕ` complex shape into itself. -/
abbrev shiftEmbedding (p : ℕ) :
    (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
  ComplexShape.embeddingDown'Add 1 p

/-- The sign twist of `R` shifted up by `p`, padded with zeros in degrees below `p`. -/
noncomputable def shiftedSignTwist (R : ChainComplex (M A) ℕ) (p : ℕ) :
    ChainComplex (M A) ℕ :=
  (signTwist A R p).extend (shiftEmbedding p)

/-- The chain map induced on shifted sign twists. -/
noncomputable def shiftedSignTwistMap {R S : ChainComplex (M A) ℕ}
    (φ : R ⟶ S) (p : ℕ) : shiftedSignTwist A R p ⟶ shiftedSignTwist A S p :=
  HomologicalComplex.extendMap (signTwistMap A φ p) (shiftEmbedding p)

/-- Shifted sign twisting preserves quasi-isomorphisms. -/
theorem shiftedSignTwistMap_quasiIso {R S : ChainComplex (M A) ℕ} (φ : R ⟶ S)
    [QuasiIso φ] (p : ℕ) : QuasiIso (shiftedSignTwistMap A φ p) := by
  change QuasiIso (HomologicalComplex.extendMap (signTwistMap A φ p) (shiftEmbedding p))
  rw [HomologicalComplex.quasiIso_extendMap_iff]
  exact signTwistMap_quasiIso A φ p

/-- The bicomplex with `R` in outer degree `p` and zero elsewhere. -/
noncomputable abbrev outerSingle (R : ChainComplex (M A) ℕ) (p : ℕ) :
    HomologicalComplex₂ (M A) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (HomologicalComplex.single (ChainComplex (M A) ℕ) (ComplexShape.down ℕ) p).obj R

/-- Cofan exhibiting the degree-`n` object of the shifted sign twist as the antidiagonal coproduct
of the single-row bicomplex in total degree `n`. -/
noncomputable def totalSingleCofan (R : ChainComplex (M A) ℕ) (p n : ℕ) :
    (outerSingle A R p).toGradedObject.CofanMapObjFun
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) n :=
  GradedObject.CofanMapObjFun.mk _ _ _ ((shiftedSignTwist A R p).X n) (fun ij hn => by
    rcases ij with ⟨i, j⟩
    change i + j = n at hn
    by_cases hi : i = p
    · exact ((HomologicalComplex.singleObjXIsoOfEq
          (ComplexShape.down ℕ) p R i hi).hom.f j) ≫
        ((signTwist A R p).extendXIso (shiftEmbedding p)
          (i := j) (i' := n) (by
            subst i
            change j + p = n
            omega)).inv
    · exact ((HomologicalComplex.eval (M A) (ComplexShape.down ℕ) j).map_isZero
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) p R i hi)).to_ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma totalSingleCofan_inj (R : ChainComplex (M A) ℕ) (p j n : ℕ)
    (h : p + j = n) :
    (totalSingleCofan A R p n).inj ⟨⟨p, j⟩, by
      change p + j = n
      exact h⟩ =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) p R).hom.f j ≫
        ((signTwist A R p).extendXIso (shiftEmbedding p)
          (i := j) (i' := n) (by
            change j + p = n
            omega)).inv := by
  simp [totalSingleCofan]
  dsimp [HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The total-degree cofan is a colimit: only the summand `(p, n - p)` is nonzero. -/
noncomputable def totalSingleCofanIsColimit (R : ChainComplex (M A) ℕ) (p n : ℕ) :
    IsColimit (totalSingleCofan A R p n) :=
  by
  classical
  exact Cofan.IsColimit.mk _
    (fun s => if h : ∃ j : ℕ, (shiftEmbedding p).f j = n then
      ((signTwist A R p).extendXIso (shiftEmbedding p) h.choose_spec).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) p R).inv.f h.choose ≫
        s.inj ⟨⟨p, h.choose⟩, by
          change p + h.choose = n
          have hs := h.choose_spec
          change h.choose + p = n at hs
          omega⟩
    else
      ((signTwist A R p).isZero_extend_X (shiftEmbedding p) n
        (fun j hj => h ⟨j, hj⟩)).to_ s.pt)
    (fun s => by
      rintro ⟨⟨i, j⟩, hn⟩
      change i + j = n at hn
      by_cases hi : i = p
      · subst i
        have h : ∃ q : ℕ, (shiftEmbedding p).f q = n :=
          ⟨j, by
            change j + p = n
            omega⟩
        rw [dif_pos h]
        have hj : h.choose = j := by
          apply (shiftEmbedding p).injective_f
          rw [h.choose_spec]
          change n = j + p
          omega
        subst hj
        rw [totalSingleCofan_inj A R p h.choose n hn]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        have ht :
            (HomologicalComplex.singleObjXSelf
                (ComplexShape.down ℕ) p R).hom.f h.choose ≫
              (HomologicalComplex.singleObjXSelf
                (ComplexShape.down ℕ) p R).inv.f h.choose = 𝟙 _ := by
          simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
            congrArg (fun f => f.f h.choose)
            (Iso.hom_inv_id
              (HomologicalComplex.singleObjXSelf
                (ComplexShape.down ℕ) p R))
        rw [← Category.assoc, ht]
        let idx :
            (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (ComplexShape.down ℕ)) ⁻¹' {n} :=
          ⟨⟨p, h.choose⟩, by
            change p + h.choose = n
            exact hn⟩
        change 𝟙 _ ≫ s.inj idx = s.inj idx
        exact Category.id_comp _
      · exact ((HomologicalComplex.eval (M A) (ComplexShape.down ℕ) j).map_isZero
          (HomologicalComplex.isZero_single_obj_X
            (ComplexShape.down ℕ) p R i hi)).eq_of_src _ _)
    (fun s m hm => by
      by_cases h : ∃ j : ℕ, (shiftEmbedding p).f j = n
      · rw [dif_pos h]
        let e := (signTwist A R p).extendXIso (shiftEmbedding p) h.choose_spec
        let u := (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) p R).inv.f h.choose
        change ((shiftedSignTwist A R p).X n ⟶ s.pt) at m
        rw [← cancel_epi e.inv]
        have hsum : p + h.choose = n := by
          have hs := h.choose_spec
          change h.choose + p = n at hs
          omega
        have hfac := hm ⟨⟨p, h.choose⟩, hsum⟩
        rw [totalSingleCofan_inj A R p h.choose n hsum] at hfac
        have hfac' := congrArg (fun z => u ≫ z) hfac
        simpa [totalSingleCofan, e, u, Category.assoc] using hfac'
      · exact ((signTwist A R p).isZero_extend_X (shiftEmbedding p) n
          (fun j hj => h ⟨j, hj⟩)).eq_of_src _ _)

/-- Degreewise isomorphism between the total complex and the shifted sign twist. -/
noncomputable def totalSingleXIso (R : ChainComplex (M A) ℕ) (p n : ℕ) :
    ((outerSingle A R p).total (ComplexShape.down ℕ)).X n ≅
      (shiftedSignTwist A R p).X n :=
  (GradedObject.CofanMapObjFun.iso (totalSingleCofanIsColimit A R p n)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma outerSingle_ιTotal_totalSingleXIso_hom
    (R : ChainComplex (M A) ℕ) (p j n : ℕ) (h : p + j = n) :
    (outerSingle A R p).ιTotal (ComplexShape.down ℕ) p j n (by
      change p + j = n
      exact h) ≫ (totalSingleXIso A R p n).hom =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) p R).hom.f j ≫
        ((signTwist A R p).extendXIso (shiftEmbedding p)
          (i := j) (i' := n) (by
            change j + p = n
            omega)).inv := by
  dsimp [totalSingleXIso]
  erw [GradedObject.CofanMapObjFun.ιMapObj_iso_inv]
  rw [totalSingleCofan_inj A R p j n h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The total complex of the bicomplex with `R` in outer degree `p` is isomorphic to the shifted
sign twist of `R`. -/
noncomputable def totalSingleIso (R : ChainComplex (M A) ℕ) (p : ℕ) :
    (outerSingle A R p).total (ComplexShape.down ℕ) ≅ shiftedSignTwist A R p :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => totalSingleXIso A R p n)
    (fun i j hij => by
      apply HomologicalComplex₂.total.hom_ext
      intro a b hab
      by_cases ha : a = p
      · subst a
        change j + 1 = i at hij
        subst i
        by_cases hb : b = 0
        · subst b
          change j + 1 = p + 0 at hij
          exact ((signTwist A R p).isZero_extend_X (shiftEmbedding p) j
            (fun q hq => by
              change q + p = j at hq
              omega)).eq_of_tgt _ _
        · obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
          have hsource : p + (b + 1) = j + 1 := by
            change j + 1 = p + (b + 1) at hij
            omega
          have htarget : p + b = j := by omega
          have htotalSource : p + (b + 1) =
              (ComplexShape.down ℕ).π (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, b + 1) := rfl
          have hshiftSource : (shiftEmbedding p).f (b + 1) =
              (ComplexShape.down ℕ).π (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, b + 1) := by
            change b + 1 + p = p + (b + 1)
            omega
          have hshiftTarget : (shiftEmbedding p).f b = j := by
            change b + p = j
            omega
          rw [outerSingle_ιTotal_totalSingleXIso_hom_assoc
              A R p (b + 1) _ htotalSource]
          dsimp only [shiftedSignTwist]
          rw [(signTwist A R p).extend_d_eq (shiftEmbedding p)
            hshiftSource hshiftTarget]
          simp only [Iso.inv_hom_id_assoc]
          rw [HomologicalComplex₂.total_d, Preadditive.add_comp,
            Preadditive.comp_add,
            HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
          have hbb : (ComplexShape.down ℕ).Rel (b + 1) b := by rfl
          have hvertical :
              (((outerSingle A R p).X p).d (b + 1) b ≫
                  (outerSingle A R p).ιTotal (ComplexShape.down ℕ) p b j (by
                    change p + b = j
                    exact htarget)) ≫
                (totalSingleXIso A R p j).hom =
              (((outerSingle A R p).X p).d (b + 1) b ≫
                  (HomologicalComplex.singleObjXSelf
                    (ComplexShape.down ℕ) p R).hom.f b) ≫
                ((signTwist A R p).extendXIso (shiftEmbedding p)
                  hshiftTarget).inv := by
            rw [Category.assoc,
              outerSingle_ιTotal_totalSingleXIso_hom A R p b j htarget,
              Category.assoc]
          let ε : ℤˣ := ComplexShape.ε₂ (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, b + 1)
          have hverticalSmul :
              (ε • (((outerSingle A R p).X p).d (b + 1) b ≫
                  (outerSingle A R p).ιTotal (ComplexShape.down ℕ) p b j (by
                    change p + b = j
                    exact htarget))) ≫
                (totalSingleXIso A R p j).hom =
              ε • ((((outerSingle A R p).X p).d (b + 1) b ≫
                  (HomologicalComplex.singleObjXSelf
                    (ComplexShape.down ℕ) p R).hom.f b) ≫
                ((signTwist A R p).extendXIso (shiftEmbedding p)
                  hshiftTarget).inv) := by
            simpa only [Linear.units_smul_comp] using
              congrArg (fun z => ε • z) hvertical
          have hhorizontal :
              (outerSingle A R p).d₁ (ComplexShape.down ℕ) p (b + 1) j ≫
                (totalSingleXIso A R p j).hom = 0 := by
            simp [HomologicalComplex₂.d₁, outerSingle]
          rw [(outerSingle A R p).d₂_eq (ComplexShape.down ℕ) p hbb j
            (by
              change p + b = j
              exact htarget)]
          rw [hhorizontal, zero_add, hverticalSmul]
          have hsign : (signTwist A R p).d (b + 1) b =
              (ComplexShape.down ℕ).ε p • R.d (b + 1) b := rfl
          have hε : ε = (ComplexShape.down ℕ).ε p := rfl
          rw [hsign, hε, ← Category.assoc, Linear.comp_units_smul,
            Linear.units_smul_comp]
          rw [(HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) p R).hom.comm (b + 1) b]
      · exact ((HomologicalComplex.eval (M A) (ComplexShape.down ℕ) b).map_isZero
          (HomologicalComplex.isZero_single_obj_X
            (ComplexShape.down ℕ) p R a ha)).eq_of_src _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma outerSingle_ιTotal_totalSingleIso_hom_f
    (R : ChainComplex (M A) ℕ) (p j n : ℕ) (h : p + j = n) :
    (outerSingle A R p).ιTotal (ComplexShape.down ℕ) p j n (by
      change p + j = n
      exact h) ≫ (totalSingleIso A R p).hom.f n =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) p R).hom.f j ≫
        ((signTwist A R p).extendXIso (shiftEmbedding p)
          (i := j) (i' := n) (by
            change j + p = n
            omega)).inv := by
  exact outerSingle_ιTotal_totalSingleXIso_hom A R p j n h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma outerSingle_ιTotal_totalSingleIso_hom_f_of_shift
    (R : ChainComplex (M A) ℕ) (p j n : ℕ) (h : p + j = n)
    (hshift : (shiftEmbedding p).f j = n) :
    (outerSingle A R p).ιTotal (ComplexShape.down ℕ) p j n (by
      change p + j = n
      exact h) ≫ (totalSingleIso A R p).hom.f n =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) p R).hom.f j ≫
        ((signTwist A R p).extendXIso (shiftEmbedding p) hshift).inv := by
  exact outerSingle_ιTotal_totalSingleIso_hom_f A R p j n h

noncomputable abbrev outerSingleMap {R S : ChainComplex (M A) ℕ}
    (φ : R ⟶ S) (p : ℕ) : outerSingle A R p ⟶ outerSingle A S p :=
  (HomologicalComplex.single (ChainComplex (M A) ℕ)
    (ComplexShape.down ℕ) p).map φ

lemma outerSingleMap_f_self_f {R S : ChainComplex (M A) ℕ}
    (φ : R ⟶ S) (p j : ℕ) :
    ((outerSingleMap A φ p).f p).f j =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) p R).hom.f j ≫ φ.f j ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) p S).inv.f j := by
  simpa only [HomologicalComplex.comp_f] using congrArg (fun f => f.f j)
    (HomologicalComplex.single_map_f_self (ComplexShape.down ℕ) p φ)

lemma shiftedSignTwistMap_f {R S : ChainComplex (M A) ℕ}
    (φ : R ⟶ S) (p j n : ℕ) (h : (shiftEmbedding p).f j = n) :
    (shiftedSignTwistMap A φ p).f n =
      ((signTwist A R p).extendXIso (shiftEmbedding p) h).hom ≫
        (signTwistMap A φ p).f j ≫
          ((signTwist A S p).extendXIso (shiftEmbedding p) h).inv := by
  change (HomologicalComplex.extendMap (signTwistMap A φ p)
    (shiftEmbedding p)).f n = _
  rw [HomologicalComplex.extendMap_f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `totalSingleIso` with respect to chain maps `R ⟶ S`. -/
lemma totalSingleIso_naturality {R S : ChainComplex (M A) ℕ}
    (φ : R ⟶ S) (p : ℕ) :
    HomologicalComplex₂.total.map (outerSingleMap A φ p)
        (ComplexShape.down ℕ) ≫ (totalSingleIso A S p).hom =
      (totalSingleIso A R p).hom ≫ shiftedSignTwistMap A φ p := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  simp only [HomologicalComplex.comp_f]
  by_cases ha : a = p
  · subst a
    have hsum : p + b = n := by
      change p + b = n at hab
      exact hab
    have hshift : (shiftEmbedding p).f b = n := by
      change b + p = n
      omega
    rw [HomologicalComplex₂.ιTotal_map_assoc,
      outerSingleMap_f_self_f A φ p b,
      outerSingle_ιTotal_totalSingleIso_hom_f_of_shift A S p b n hsum hshift]
    rw [outerSingle_ιTotal_totalSingleIso_hom_f_of_shift_assoc
        A R p b n hsum hshift,
      shiftedSignTwistMap_f A φ p b n hshift]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have ht :
        (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) p S).inv.f b ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) p S).hom.f b = 𝟙 _ := by
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
        congrArg (fun f => f.f b)
          (Iso.inv_hom_id (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) p S))
    rw [← cancel_mono
      ((signTwist A S p).extendXIso (shiftEmbedding p) hshift).hom]
    simp only [Category.assoc]
    have hext :
        ((signTwist A S p).extendXIso (shiftEmbedding p) hshift).inv ≫
          ((signTwist A S p).extendXIso (shiftEmbedding p) hshift).hom =
            𝟙 (S.X b) :=
      Iso.inv_hom_id
        ((signTwist A S p).extendXIso (shiftEmbedding p) hshift)
    rw [hext, Category.comp_id, ht, Category.comp_id]
    rfl
  · exact ((HomologicalComplex.eval (M A) (ComplexShape.down ℕ) b).map_isZero
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) p R a ha)).eq_of_src _ _

/-- Totalization of single-row bicomplexes preserves quasi-isomorphisms. -/
theorem totalSingleMap_quasiIso {R S : ChainComplex (M A) ℕ}
    (φ : R ⟶ S) [QuasiIso φ] (p : ℕ) :
    QuasiIso (HomologicalComplex₂.total.map (outerSingleMap A φ p)
      (ComplexShape.down ℕ)) := by
  letI : QuasiIso (shiftedSignTwistMap A φ p) :=
    shiftedSignTwistMap_quasiIso A φ p
  haveI : QuasiIso
      (HomologicalComplex₂.total.map (outerSingleMap A φ p)
          (ComplexShape.down ℕ) ≫ (totalSingleIso A S p).hom) := by
    rw [totalSingleIso_naturality A φ p]
    infer_instance
  exact quasiIso_of_comp_right _ (totalSingleIso A S p).hom

end GaloisForLFunctions.IrregularStokes.FirstQuadrantTotalSingle
