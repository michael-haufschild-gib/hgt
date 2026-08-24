import GaloisForLFunctions.HTGeometry.StokesFirstQuadrantTotalExact
import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Finite prefix filtration of nonnegative complexes

This file fills the missing inclusion API for finite stupid prefixes of `ℕ`-indexed chain
complexes. Adjacent prefixes form a natural short exact sequence whose quotient is the new top
component concentrated in one degree. The construction is generic over an abelian category and
will drive finite-stage comparison for first-quadrant total complexes.
-/

open CategoryTheory Limits

universe v u

namespace GaloisForLFunctions.IrregularStokes.NonnegativePrefixFiltration


def prefixShape (r : ℕ) : ComplexShape (Fin (r + 1)) where
  Rel i j := j.val + 1 = i.val
  next_eq h h' := Fin.ext (by omega)
  prev_eq h h' := Fin.ext (by omega)

def prefixEmbedding (r : ℕ) :
    (prefixShape r).Embedding (ComplexShape.down ℕ) :=
  ComplexShape.Embedding.mk' _ _ Fin.val Fin.val_injective (by
    intro i j
    rfl)

instance (r : ℕ) : (prefixEmbedding r).IsTruncGE where
  rel' i j h := h
  mem_next {j k} h := by
    have hj := j.isLt
    change k + 1 = j.val at h
    exact ⟨⟨k, by omega⟩, rfl⟩

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasZeroObject D]

noncomputable abbrev prefixTrunc (K : ChainComplex D ℕ) (r : ℕ) :=
  K.stupidTrunc (prefixEmbedding r)

noncomputable def prefixXIso (K : ChainComplex D ℕ) (r i : ℕ) (hi : i ≤ r) :
    (prefixTrunc K r).X i ≅ K.X i :=
  K.stupidTruncXIso (prefixEmbedding r)
    (i := ⟨i, Nat.lt_succ_iff.mpr hi⟩) (i' := i) rfl

lemma prefixXIso_hom_eq (K : ChainComplex D ℕ) (r i : ℕ) (hi : i ≤ r) :
    (prefixXIso K r i hi).hom =
      ((K.restriction (prefixEmbedding r)).extendXIso (prefixEmbedding r)
        (i := ⟨i, Nat.lt_succ_iff.mpr hi⟩) (i' := i) rfl).hom := by
  change _ ≫ 𝟙 _ = _
  simp

lemma prefixXIso_inv_eq (K : ChainComplex D ℕ) (r i : ℕ) (hi : i ≤ r) :
    (prefixXIso K r i hi).inv =
      ((K.restriction (prefixEmbedding r)).extendXIso (prefixEmbedding r)
        (i := ⟨i, Nat.lt_succ_iff.mpr hi⟩) (i' := i) rfl).inv := by
  change 𝟙 _ ≫ _ = _
  simp

lemma prefix_d_eq (K : ChainComplex D ℕ) (r : ℕ)
    {i j : ℕ} (hi : i ≤ r) (hj : j ≤ r) :
    (prefixTrunc K r).d i j =
      (prefixXIso K r i hi).hom ≫ K.d i j ≫
      (prefixXIso K r j hj).inv := by
  let ii : Fin (r + 1) := ⟨i, Nat.lt_succ_iff.mpr hi⟩
  let jj : Fin (r + 1) := ⟨j, Nat.lt_succ_iff.mpr hj⟩
  have hExt := HomologicalComplex.extend_d_eq
    (K.restriction (prefixEmbedding r)) (prefixEmbedding r)
    (i := ii) (j := jj) (i' := i) (j' := j) rfl rfl
  change ((K.restriction (prefixEmbedding r)).extend
    (prefixEmbedding r)).d i j = _
  rw [hExt]
  change _ ≫ K.d i j ≫ _ = _
  rw [prefixXIso_hom_eq, prefixXIso_inv_eq]
  rfl

lemma prefix_isZero_X (K : ChainComplex D ℕ) (r i : ℕ) (hi : r < i) :
    IsZero ((prefixTrunc K r).X i) := by
  apply K.isZero_stupidTrunc_X (prefixEmbedding r)
  intro x hx
  change x.val = i at hx
  have hxlt := x.isLt
  omega

noncomputable def prefixMap (K : ChainComplex D ℕ) (r : ℕ) :
    prefixTrunc K r ⟶ prefixTrunc K (r + 1) where
  f i := if hi : i ≤ r then
      (prefixXIso K r i hi).hom ≫
        (prefixXIso K (r + 1) i (by omega)).inv
    else 0
  comm' i j hij := by
    change j + 1 = i at hij
    by_cases hi : i ≤ r
    · have hj : j ≤ r := by omega
      simp only [dif_pos hi, dif_pos hj]
      rw [prefix_d_eq K r hi hj,
        prefix_d_eq K (r + 1) (by omega) (by omega)]
      simp
    · apply (prefix_isZero_X K r i (by omega)).eq_of_src

@[simp]
lemma prefixMap_f_of_le (K : ChainComplex D ℕ) (r i : ℕ) (hi : i ≤ r) :
    (prefixMap K r).f i =
      (prefixXIso K r i hi).hom ≫
        (prefixXIso K (r + 1) i (by omega)).inv := by
  simp [prefixMap, hi]

@[simp]
lemma prefixMap_f_of_lt (K : ChainComplex D ℕ) (r i : ℕ) (hi : r < i) :
    (prefixMap K r).f i = 0 := by
  simp [prefixMap, Nat.not_le.mpr hi]

noncomputable def prefixπ (K : ChainComplex D ℕ) (r : ℕ) :
    prefixTrunc K (r + 1) ⟶
      (HomologicalComplex.single D (ComplexShape.down ℕ) (r + 1)).obj (K.X (r + 1)) :=
  HomologicalComplex.mkHomToSingle
    (prefixXIso K (r + 1) (r + 1) le_rfl).hom (fun i hi => by
      change r + 1 + 1 = i at hi
      apply (prefix_isZero_X K (r + 1) i (by omega)).eq_of_src)

@[simp]
lemma prefixπ_f_top (K : ChainComplex D ℕ) (r : ℕ) :
    (prefixπ K r).f (r + 1) =
      (prefixXIso K (r + 1) (r + 1) le_rfl).hom ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) (r + 1) (K.X (r + 1))).inv := by
  simp [prefixπ]

lemma prefixMap_comp_prefixπ (K : ChainComplex D ℕ) (r : ℕ) :
    prefixMap K r ≫ prefixπ K r = 0 := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, prefixMap_f_of_lt K r (r + 1) (by omega),
    zero_comp]
  rfl

noncomputable def prefixShortComplex (K : ChainComplex D ℕ) (r : ℕ) :
    ShortComplex (ChainComplex D ℕ) :=
  ShortComplex.mk (prefixMap K r) (prefixπ K r) (prefixMap_comp_prefixπ K r)

theorem prefixShortExact {E : Type u} [Category.{v} E] [Abelian E]
    (K : ChainComplex E ℕ) (r : ℕ) :
    (prefixShortComplex K r).ShortExact := by
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (C := E) (c := ComplexShape.down ℕ) (prefixShortComplex K r)).2
  intro i
  let S := (prefixShortComplex K r).map
    (HomologicalComplex.eval E (ComplexShape.down ℕ) i)
  change S.ShortExact
  by_cases hi : i ≤ r
  · have hzero3 : IsZero
        (((HomologicalComplex.single E (ComplexShape.down ℕ) (r + 1)).obj
          (K.X (r + 1))).X i) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    haveI : IsIso ((prefixMap K r).f i) := by
      rw [prefixMap_f_of_le K r i hi]
      infer_instance
    have hg : S.g = 0 := hzero3.eq_of_tgt _ _
    letI : Mono S.f := by
      change Mono ((prefixMap K r).f i)
      infer_instance
    letI : Epi S.f := by
      change Epi ((prefixMap K r).f i)
      infer_instance
    letI : Epi S.g := hzero3.epi _
    exact ShortComplex.ShortExact.mk' ((S.exact_iff_epi hg).2 inferInstance)
      inferInstance inferInstance
  · have hir : r < i := Nat.lt_of_not_ge hi
    by_cases hitop : i = r + 1
    · subst hitop
      have hzero1 := prefix_isZero_X K r (r + 1) (by omega)
      have hf : S.f = 0 := hzero1.eq_of_src _ _
      haveI : IsIso ((prefixπ K r).f (r + 1)) := by
        rw [prefixπ_f_top]
        infer_instance
      letI : Mono S.f := hzero1.mono _
      letI : Mono S.g := by
        change Mono ((prefixπ K r).f (r + 1))
        infer_instance
      letI : Epi S.g := by
        change Epi ((prefixπ K r).f (r + 1))
        infer_instance
      exact ShortComplex.ShortExact.mk' ((S.exact_iff_mono hf).2 inferInstance)
        inferInstance inferInstance
    · have hmid : IsZero ((prefixTrunc K (r + 1)).X i) :=
        prefix_isZero_X K (r + 1) i (by omega)
      have hsrc : IsZero ((prefixTrunc K r).X i) :=
        prefix_isZero_X K r i (by omega)
      have htgt : IsZero
          (((HomologicalComplex.single E (ComplexShape.down ℕ) (r + 1)).obj
            (K.X (r + 1))).X i) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hitop
      have hf : S.f = 0 := hsrc.eq_of_src _ _
      letI : Mono S.f := hsrc.mono _
      letI : Mono S.g := hmid.mono _
      letI : Epi S.g := htgt.epi _
      exact ShortComplex.ShortExact.mk' ((S.exact_iff_mono hf).2 inferInstance)
        inferInstance inferInstance

noncomputable def prefixTruncMap {K L : ChainComplex D ℕ} (φ : K ⟶ L) (r : ℕ) :
    prefixTrunc K r ⟶ prefixTrunc L r :=
  HomologicalComplex.stupidTruncMap φ (prefixEmbedding r)

/-- Canonical inclusion of a finite stupid prefix into the original nonnegative complex. -/
noncomputable def prefixInclusion (K : ChainComplex D ℕ) (r : ℕ) :
    prefixTrunc K r ⟶ K where
  f i := if hi : i ≤ r then (prefixXIso K r i hi).hom else 0
  comm' i j hij := by
    change j + 1 = i at hij
    by_cases hi : i ≤ r
    · have hj : j ≤ r := by omega
      simp only [dif_pos hi, dif_pos hj]
      rw [prefix_d_eq K r hi hj]
      simp
    · exact (prefix_isZero_X K r i (by omega)).eq_of_src _ _

@[simp]
lemma prefixInclusion_f_of_le (K : ChainComplex D ℕ) (r i : ℕ) (hi : i ≤ r) :
    (prefixInclusion K r).f i = (prefixXIso K r i hi).hom := by
  simp [prefixInclusion, hi]

@[simp]
lemma prefixInclusion_f_of_lt (K : ChainComplex D ℕ) (r i : ℕ) (hi : r < i) :
    (prefixInclusion K r).f i = 0 := by
  simp [prefixInclusion, Nat.not_le.mpr hi]

@[reassoc]
lemma prefixTruncMap_prefixXIso_hom {K L : ChainComplex D ℕ} (φ : K ⟶ L)
    (r i : ℕ) (hi : i ≤ r) :
    (prefixTruncMap φ r).f i ≫ (prefixXIso L r i hi).hom =
      (prefixXIso K r i hi).hom ≫ φ.f i := by
  simp [prefixTruncMap, prefixXIso,
    HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom]

lemma prefixInclusion_naturality {K L : ChainComplex D ℕ} (φ : K ⟶ L) (r : ℕ) :
    prefixTruncMap φ r ≫ prefixInclusion L r = prefixInclusion K r ≫ φ := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i ≤ r
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      prefixInclusion_f_of_le K r i hi, prefixInclusion_f_of_le L r i hi]
    exact prefixTruncMap_prefixXIso_hom φ r i hi
  · exact (prefix_isZero_X K r i (by omega)).eq_of_src _ _

lemma prefixMap_naturality {K L : ChainComplex D ℕ} (φ : K ⟶ L) (r : ℕ) :
    prefixTruncMap φ r ≫ prefixMap L r =
      prefixMap K r ≫ prefixTruncMap φ (r + 1) := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i ≤ r
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      prefixMap_f_of_le K r i hi, prefixMap_f_of_le L r i hi]
    rw [← cancel_mono (prefixXIso L (r + 1) i (by omega)).hom]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id, Category.comp_id]
    rw [prefixTruncMap_prefixXIso_hom φ (r + 1) i (by omega)]
    simp only [Iso.inv_hom_id_assoc]
    exact prefixTruncMap_prefixXIso_hom φ r i hi
  · apply (prefix_isZero_X K r i (by omega)).eq_of_src

lemma prefixπ_naturality {K L : ChainComplex D ℕ} (φ : K ⟶ L) (r : ℕ) :
    prefixTruncMap φ (r + 1) ≫ prefixπ L r =
      prefixπ K r ≫
        (HomologicalComplex.single D (ComplexShape.down ℕ) (r + 1)).map (φ.f (r + 1)) := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    prefixπ_f_top K r, prefixπ_f_top L r]
  simp only [Category.assoc, HomologicalComplex.single_map_f_self,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc, prefixTruncMap_prefixXIso_hom]
  simp only [Category.assoc]

noncomputable def prefixShortComplexMap {K L : ChainComplex D ℕ}
    (φ : K ⟶ L) (r : ℕ) : prefixShortComplex K r ⟶ prefixShortComplex L r where
  τ₁ := prefixTruncMap φ r
  τ₂ := prefixTruncMap φ (r + 1)
  τ₃ := (HomologicalComplex.single D (ComplexShape.down ℕ) (r + 1)).map (φ.f (r + 1))
  comm₁₂ := prefixMap_naturality φ r
  comm₂₃ := prefixπ_naturality φ r

end GaloisForLFunctions.IrregularStokes.NonnegativePrefixFiltration
