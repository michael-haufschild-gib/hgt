import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProductSectionRings
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveEmbeddingCoordinates
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! Projective embeddings survive affine base change, and their products have Segre ratios. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology UpperTheory.Cb

namespace GlobalTheory.ProjectiveSections

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}

private theorem map_mem_range_of_polynomial_generators
    {A B K ι κ : Type} [CommRing A] [CommRing B] [CommRing K]
    (j : A →+* B) (k : R →+* A) (r : ι → A) (F : MvPolynomial κ K →+* B)
    (hr : Function.Surjective (MvPolynomial.eval₂Hom k r))
    (hc : ∀ c, j (k c) ∈ F.range) (hs : ∀ i, j (r i) ∈ F.range)
    (x : A) : j x ∈ F.range := by
  obtain ⟨P, rfl⟩ := hr x
  induction P using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C]; exact hc c
  | add P Q hP hQ =>
    rw [map_add, map_add]
    exact add_mem hP hQ
  | mul_X P i hP =>
    rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']
    exact mul_mem hP (hs i)

section Coordinates

variable (p : Z ⟶ X) (q : Z ⟶ Y)
  {n m d : ℕ} (e : Fin (d + 1) ≃ Fin (n + 1) × Fin (m + 1))
  (C : Coordinates X n) (D : Coordinates Y m)

private abbrev productOpen (i : Fin (d + 1)) :=
  p ⁻¹ᵁ C.U (e i).1 ⊓ q ⁻¹ᵁ D.U (e i).2

private def productRatio (i j : Fin (d + 1)) : Γ(Z, productOpen p q e C D i) :=
  p.appLE _ _ inf_le_left (C.ratio (e i).1 (e j).1) *
    q.appLE _ _ inf_le_right (D.ratio (e i).2 (e j).2)

private def productCoordinates : Coordinates Z d where
  U := productOpen p q e C D
  ratio := productRatio p q e C D
  cover := by
    refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (C.cover.ge (Set.mem_univ (p z)))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (D.cover.ge (Set.mem_univ (q z)))
    apply Opens.mem_iSup.mpr
    refine ⟨e.symm (i, j), ?_⟩
    simpa only [productOpen, Equiv.apply_symm_apply] using
      (show z ∈ p ⁻¹ᵁ C.U i ⊓ q ⁻¹ᵁ D.U j from ⟨hi, hj⟩)
  ratio_self i := by
    simp only [productRatio, C.ratio_self, D.ratio_self, map_one, mul_one]
  basicOpen_ratio i j := by
    simp only [productRatio, Scheme.basicOpen_mul, Scheme.basicOpen_appLE,
      C.basicOpen_ratio, D.basicOpen_ratio, Scheme.Hom.preimage_inf]
    apply SetLike.ext
    intro z
    simp only [productOpen, Opens.mem_inf]
    tauto
  ratio_mul i j k := by
    let V := productOpen p q e C D i ⊓ productOpen p q e C D j
    have hi : V ≤ p ⁻¹ᵁ C.U (e i).1 := inf_le_left.trans inf_le_left
    have hj : V ≤ p ⁻¹ᵁ C.U (e j).1 := inf_le_right.trans inf_le_left
    have hi' : V ≤ q ⁻¹ᵁ D.U (e i).2 := inf_le_left.trans inf_le_right
    have hj' : V ≤ q ⁻¹ᵁ D.U (e j).2 := inf_le_right.trans inf_le_right
    have eC : V ≤ p ⁻¹ᵁ (C.U (e i).1 ⊓ C.U (e j).1) := fun z hz => ⟨hi hz, hj hz⟩
    have eD : V ≤ q ⁻¹ᵁ (D.U (e i).2 ⊓ D.U (e j).2) := fun z hz => ⟨hi' hz, hj' hz⟩
    have hC := congrArg (p.appLE _ V eC).hom
      (C.ratio_mul (e i).1 (e j).1 (e k).1)
    have hD := congrArg (q.appLE _ V eD).hom
      (D.ratio_mul (e i).2 (e j).2 (e k).2)
    simp only [map_mul, appLE_resG] at hC hD
    simp only [productRatio, map_mul, resG_appLE]
    rw [mul_mul_mul_comm, hC, hD]

private theorem product_eval_surjective (H : IsPullback p q f g)
    (haff : ∀ i, IsAffineOpen (C.U i)) (haff' : ∀ j, IsAffineOpen (D.U j))
    (hC : ∀ i, Function.Surjective
      (MvPolynomial.eval₂Hom (algebraMap R (SectionRing f (C.U i))) (C.ratio i)))
    (hD : ∀ j, Function.Surjective
      (MvPolynomial.eval₂Hom (algebraMap R (SectionRing g (D.U j))) (D.ratio j)))
    (i : Fin (d + 1)) :
    Function.Surjective (MvPolynomial.eval₂Hom
      (algebraMap R (SectionRing (p ≫ f) (productOpen p q e C D i))) (productRatio p q e C D i)) := by
  let a := (e i).1
  let b := (e i).2
  let V := productOpen p q e C D i
  let F := MvPolynomial.eval₂Hom (algebraMap R (SectionRing (p ≫ f) V)) (productRatio p q e C D i)
  let p' := sectionPullbackLE (p := p) (f := f) (q := p) (g := f) rfl
    (inf_le_left : V ≤ p ⁻¹ᵁ C.U a)
  let q' := sectionPullbackLE H.w (inf_le_right : V ≤ q ⁻¹ᵁ D.U b)
  have hp (j : Fin (n + 1)) : p' (C.ratio a j) ∈ F.range := by
    refine ⟨MvPolynomial.X (e.symm (j, b)), ?_⟩
    simp only [F, MvPolynomial.eval₂Hom_X', productRatio, Equiv.apply_symm_apply, D.ratio_self,
      map_one, mul_one, p', sectionPullbackLE_apply, a, b]
  have hq (j : Fin (m + 1)) : q' (D.ratio b j) ∈ F.range := by
    refine ⟨MvPolynomial.X (e.symm (a, j)), ?_⟩
    simp only [F, MvPolynomial.eval₂Hom_X', productRatio, Equiv.apply_symm_apply, C.ratio_self,
      map_one, one_mul, q', sectionPullbackLE_apply, a, b]
  have H' := isPushout_productSections H (C.U a) (D.U b) (haff a) (haff' b)
  have hclose : Subring.closure (Set.range p'.toRingHom ∪ Set.range q'.toRingHom) =
      (⊤ : Subring (SectionRing (p ≫ f) V)) :=
    CommRingCat.closure_range_union_range_eq_top_of_isPushout H'
  change Function.Surjective F
  rw [← RingHom.range_eq_top, ← top_le_iff, ← hclose, Subring.closure_le]
  rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
  · exact map_mem_range_of_polynomial_generators p'.toRingHom _ (C.ratio a) F (hC a)
      (fun c => ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C]; exact (p'.commutes c).symm⟩) hp x
  · exact map_mem_range_of_polynomial_generators q'.toRingHom _ (D.ratio b) F (hD b)
      (fun c => ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C]; exact (q'.commutes c).symm⟩) hq x

end Coordinates

/-- The fibre product of two projective schemes over an affine base is projective. -/
theorem isProjOver_product {p : Z ⟶ X} {q : Z ⟶ Y}
    (H : IsPullback p q f g) (hf : IsProjOver f) (hg : IsProjOver g) :
    IsProjOver (p ≫ f) := by
  cases subsingleton_or_nontrivial R
  · haveI : IsEmpty (Spec (CommRingCat.of R)) := inferInstanceAs (IsEmpty (PrimeSpectrum R))
    haveI : IsEmpty Z := Function.isEmpty (p ≫ f)
    exact isProjOver_of_isEmpty (p ≫ f)
  · obtain ⟨n, a, _, ha⟩ := hf
    obtain ⟨m, b, _, hb⟩ := hg
    let e : Fin (n * m + n + m + 1) ≃ Fin (n + 1) × Fin (m + 1) :=
      (finCongr (by ring)).trans finProdFinEquiv.symm
    let C := Coordinates.ofMorphism a
    let D := Coordinates.ofMorphism b
    have hA := Coordinates.ofMorphism_isAffineOpen a
    have hB := Coordinates.ofMorphism_isAffineOpen b
    exact (productCoordinates p q e C D).isProjOver (p ≫ f)
      (fun i => isAffineOpen_product H (hA (e i).1) (hB (e i).2))
      (product_eval_surjective p q e C D H hA hB
        (Coordinates.ofMorphism_eval_surjective a ha) (Coordinates.ofMorphism_eval_surjective b hb))

section BaseChange

variable {S : Type} [CommRing S] {π : Y ⟶ X} {s : Y ⟶ Spec (CommRingCat.of S)}
  {n : ℕ} (C : Coordinates X n)

private def preimageCoordinates : Coordinates Y n where
  U i := π ⁻¹ᵁ C.U i
  cover := π.iSup_preimage_eq_top C.cover
  ratio i j := π.app (C.U i) (C.ratio i j)
  ratio_self i := by rw [C.ratio_self, map_one]
  basicOpen_ratio i j := by
    rw [← Scheme.preimage_basicOpen, C.basicOpen_ratio, Scheme.Hom.preimage_inf]
  ratio_mul i j k := by
    have h := congrArg (π.app (C.U i ⊓ C.U j)).hom (C.ratio_mul i j k)
    simp only [Scheme.Hom.app_eq_appLE, map_mul, appLE_resG] at h
    simp only [Scheme.Hom.app_eq_appLE, resG_appLE]
    exact h

/-- Projectivity over an affine base survives arbitrary extension of the coefficient ring. -/
theorem isProjOver_baseChange (α : R →+* S)
    (H : IsPullback π s f (Spec.map (CommRingCat.ofHom α))) (hf : IsProjOver f) : IsProjOver s := by
  cases subsingleton_or_nontrivial S
  · haveI : IsEmpty (Spec (CommRingCat.of S)) := inferInstanceAs (IsEmpty (PrimeSpectrum S))
    haveI : IsEmpty Y := Function.isEmpty s
    exact isProjOver_of_isEmpty s
  · haveI : Nontrivial R := α.domain_nontrivial
    letI : Algebra R S := α.toAlgebra
    obtain ⟨n, a, _, ha⟩ := hf
    let C := Coordinates.ofMorphism a
    let D := preimageCoordinates (π := π) C
    haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
    have hU (i : Fin (n + 1)) : IsAffineOpen (C.U i) := Coordinates.ofMorphism_isAffineOpen a i
    refine D.isProjOver s (fun i => (hU i).preimage π) fun i => ?_
    let U := C.U i
    let V := π ⁻¹ᵁ U
    let A := SectionRing f U
    let B := SectionRing s V
    let F := MvPolynomial.eval₂Hom (algebraMap S B) (D.ratio i)
    let j := (π.appLE U V le_rfl).hom
    have hP := isPushout_sectionAlgebra H (hU i) rfl
    have hclose : Subring.closure (Set.range (algebraMap S B) ∪ Set.range j) = (⊤ : Subring B) :=
      CommRingCat.closure_range_union_range_eq_top_of_isPushout hP
    change Function.Surjective F
    rw [← RingHom.range_eq_top, ← top_le_iff, ← hclose, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨MvPolynomial.C x, MvPolynomial.eval₂Hom_C _ _ _⟩
    · refine map_mem_range_of_polynomial_generators j (algebraMap R A) (C.ratio i) F ?_ ?_ ?_ x
      · exact Coordinates.ofMorphism_eval_surjective a ha i
      · intro r
        refine ⟨MvPolynomial.C (α r), ?_⟩
        change F _ = _
        rw [MvPolynomial.eval₂Hom_C]
        exact (appLE_base_algebraMap H.w le_rfl r).symm
      · intro k
        refine ⟨MvPolynomial.X k, ?_⟩
        change F _ = _
        rw [MvPolynomial.eval₂Hom_X']
        exact ConcreteCategory.congr_hom (π.app_eq_appLE (U := U)) _

end BaseChange

end GlobalTheory.ProjectiveSections
