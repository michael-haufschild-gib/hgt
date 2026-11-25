import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CechOneAffine
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.PointedCechTensors

/-! A cocycle trivial on a pointed horizontal slice has primitives over each affine strip. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.SchemeCohomology GlobalTheory.LineBundleSections

namespace GlobalTheory.CechOne

private theorem contract_restrict {K A B C : Type} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (l : A →ₗ[K] K) (r : B →ₗ[K] C) (x : A ⊗[K] B) :
    TensorProduct.lid K C (l.rTensor C (r.lTensor A x)) =
      r (TensorProduct.lid K B (l.rTensor B x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, map_smul]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem eval_contract {K A B : Type} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (l : A →ₗ[K] K) (r : B →ₗ[K] K) (x : A ⊗[K] B) :
    r (TensorProduct.lid K B (l.rTensor B x)) =
      l (TensorProduct.rid K A (r.lTensor A x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, TensorProduct.rid_tmul, map_smul, smul_eq_mul, mul_comm]
  | add a b ha hb => simp only [map_add, ha, hb]

variable {K : Type} [Field K] {X Y Z : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of K)} {g : Y ⟶ Spec (CommRingCat.of K)}
  {p : Z ⟶ X} {q : Z ⟶ Y} (H : IsPullback p q f g)
  {I : Type} {V : I → Z.Opens} {φ : ∀ i j, Γ(Z, V i ⊓ V j)}

/-- Restriction to a point of the second factor detects the horizontal obstruction
when the second factor has only scalar functions. -/
theorem exists_splitting_on_strip [CompactSpace X] [X.IsSeparated] [Y.IsSeparated]
    (hg : Function.Surjective g.appTop) {y : Spec (CommRingCat.of K) ⟶ Y} (hy : y ≫ g = 𝟙 _)
    {a : X ⟶ Z} (ha : a ≫ p = 𝟙 X) (ha' : a ≫ q = f ≫ y)
    (B₀ : Y.affineOpens) (hB₀ : ⊤ ≤ y ⁻¹ᵁ B₀.1) (hc : ⨆ i, V i = ⊤)
    (hφ : IsCocycle V φ) (ρ : ∀ i, Γ(X, a ⁻¹ᵁ V i))
    (hρ : ∀ i j, a.app (V i ⊓ V j) (φ i j) =
      resG X (a.preimage_mono inf_le_left) (ρ i) - resG X (a.preimage_mono inf_le_right) (ρ j))
    (B : Y.affineOpens) : ∃ τ, Splits V φ (q ⁻¹ᵁ B.1) τ := by
  obtain ⟨A, hA, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
    (show IsCompact ((⊤ : X.Opens) : Set X) by simpa only [Opens.coe_top] using isCompact_univ)
  haveI : Finite A := hA.to_subtype
  let U : A → X.Opens := fun i => i.1.1
  have hU (i : A) : IsAffineOpen (U i) := i.1.2
  have hUtop : iSup U = ⊤ := by rw [e, iSup_subtype]
  let U₂ := overlap U
  have hU₂ (k : A × A) : IsAffineOpen (U₂ k) := (hU k.1).inf (hU k.2)
  have l₁ (k : A × A) : p ⁻¹ᵁ U₂ k ≤ p ⁻¹ᵁ U k.1 := p.preimage_mono inf_le_left
  have l₂ (k : A × A) : p ⁻¹ᵁ U₂ k ≤ p ⁻¹ᵁ U k.2 := p.preimage_mono inf_le_right
  choose σ hσ using fun (i : A) (j : Y.affineOpens) =>
    exists_splitting_on_affine hc hφ (isAffineOpen_product H (hU i) j.2)
  choose c hcd using fun (j : Y.affineOpens) (k : A × A) =>
    exists_difference hc (hσ k.1 j) (hσ k.2 j) (P := p ⁻¹ᵁ U₂ k ⊓ q ⁻¹ᵁ j.1)
      (inf_le_inf_right _ (l₁ k)) (inf_le_inf_right _ (l₂ k))
  choose z hz using fun j : Y.affineOpens => exists_tensor_of_sections H U₂ j.1 hU₂ j.2 (c j)
  have hcompat (j k : Y.affineOpens) : ∃ w,
      (sectionRes g (homOfLE (inf_le_left : j.1 ⊓ k.1 ≤ j.1))).toLinearMap.lTensor _ (z j) -
        (sectionRes g (homOfLE (inf_le_right : j.1 ⊓ k.1 ≤ k.1))).toLinearMap.lTensor _ (z k) -
          (chartDifference (f := f) U).rTensor _ w = 0 := by
    have hW := j.2.inf k.2
    have m₁ : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ j.1 := q.preimage_mono inf_le_left
    have m₂ : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ k.1 := q.preimage_mono inf_le_right
    choose d hd using fun i : A => exists_difference hc (hσ i j) (hσ i k)
      (P := p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1)) (inf_le_inf_left _ m₁) (inf_le_inf_left _ m₂)
    obtain ⟨w, hw⟩ := exists_tensor_of_sections H U (j.1 ⊓ k.1) hU hW d
    refine ⟨w, tensor_eq_of_sections_eq H U₂ (j.1 ⊓ k.1) hU₂ hW fun m => ?_⟩
    rw [map_sub, map_sub, map_zero, tensorComponent_restrict_right, tensorComponent_restrict_right,
      tensorComponent_difference]
    have a₁ := congrArg (resG Z (inf_le_inf_left (p ⁻¹ᵁ U₂ m) m₁)) (hz j m)
    have a₂ := congrArg (resG Z (inf_le_inf_left (p ⁻¹ᵁ U₂ m) m₂)) (hz k m)
    have a₃ := congrArg (resG Z (inf_le_inf_right (q ⁻¹ᵁ (j.1 ⊓ k.1)) (l₁ m))) (hw m.1)
    have a₄ := congrArg (resG Z (inf_le_inf_right (q ⁻¹ᵁ (j.1 ⊓ k.1)) (l₂ m))) (hw m.2)
    simp only [res_tensorComponent] at a₁ a₂ a₃ a₄
    rw [a₁, a₂, a₃, a₄]
    refine sections_ext_on_cover V (by rw [hc]; exact le_top) _ _ fun i => ?_
    let M := p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V i
    have b₁ := hcd j m i M (inf_le_left.trans (inf_le_inf_left _ m₁)) inf_le_right
    have b₂ := hcd k m i M (inf_le_left.trans (inf_le_inf_left _ m₂)) inf_le_right
    have b₃ := hd m.1 i M (inf_le_left.trans (inf_le_inf_right _ (l₁ m))) inf_le_right
    have b₄ := hd m.2 i M (inf_le_left.trans (inf_le_inf_right _ (l₂ m))) inf_le_right
    simp only [map_sub, map_zero, resG_resG]
    linear_combination b₁ - b₂ - b₃ + b₄
  have hN (N : X.Opens) : N ≤ a ⁻¹ᵁ (p ⁻¹ᵁ N ⊓ q ⁻¹ᵁ B₀.1) := by
    rw [a.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ha, ha']
    exact le_inf le_rfl (le_top.trans (f.preimage_mono hB₀))
  obtain ⟨x, hx⟩ := pullback_difference_of_coboundary hc a ρ hρ
    (fun i => p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ B₀.1) (fun i => σ i B₀) (fun i => hσ i B₀) U (fun i => hN (U i))
  have hz₀ : TensorProduct.rid K (chartSections (f := f) U₂)
      ((evalAt hy hB₀).toLinearMap.lTensor _ (z B₀)) = chartDifference (f := f) U x := by
    funext m
    refine (tensorComponent_on_slice hy hB₀ H U₂ ha ha' m inf_le_left inf_le_right (hN _) (z B₀)).symm.trans ?_
    rw [hz B₀ m]
    exact hx m.1 m.2 _ _ _ _ (hcd B₀ m) _ inf_le_left inf_le_right _
  have hl : ∀ l : chartSections (f := f) U₂ →ₗ[K] K, l ∘ₗ chartDifference (f := f) U = 0 →
      TensorProduct.lid K _ (l.rTensor _ (z B)) = 0 := by
    intro l hl
    let b (j : Y.affineOpens) := TensorProduct.lid K _ (l.rTensor _ (z j))
    obtain ⟨β, hβ⟩ := exists_fun_of_cover (fun j : Y.affineOpens => j.1) (fun _ => le_top)
      (iSup_affineOpens_eq_top Y).ge b (by
        intro j k
        obtain ⟨w, hw⟩ := hcompat j k
        have e := congrArg (fun t => TensorProduct.lid K _ (l.rTensor _ t)) hw
        simp only [map_sub, map_zero] at e
        rw [contract_restrict, contract_restrict, ← LinearMap.rTensor_comp_apply, hl] at e
        simp only [LinearMap.rTensor_zero, LinearMap.zero_apply, map_zero, sub_zero] at e
        exact sub_eq_zero.mp e)
    have hs : Function.Surjective (algebraMap K (SectionRing g ⊤)) := by
      have e : g.appLE ⊤ ⊤ le_top = g.appTop := by
        simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top]
      change Function.Surjective (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ ⊤ le_top).hom)
      rw [e]
      exact hg.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    obtain ⟨r, rfl⟩ := hs β
    have hb (j : Y.affineOpens) : b j = algebraMap K (SectionRing g j.1) r :=
      (hβ j).symm.trans ((sectionRes g (homOfLE le_top)).commutes r)
    have e := eval_contract l (evalAt hy hB₀).toLinearMap (z B₀)
    rw [hz₀, show l (chartDifference (f := f) U x) = 0 from LinearMap.congr_fun hl x] at e
    change evalAt hy hB₀ (b B₀) = 0 at e
    rw [hb, AlgHom.commutes] at e
    rw [hb B, e, map_zero]
  obtain ⟨w, hw⟩ := mem_range_rTensor_of_forall_dual (chartDifference (f := f) U) (z B) hl
  refine splittings_glue (fun i => p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ B.1) (fun i => σ i B) (fun i => hσ i B)
    (fun i => tensorComponent H U B.1 i inf_le_left inf_le_right w) ?_ _ ?_
  · intro i k j M hi hk hj
    have hM : M ≤ p ⁻¹ᵁ U₂ (i, k) ⊓ q ⁻¹ᵁ B.1 :=
      le_inf (le_inf (hi.trans inf_le_left) (hk.trans inf_le_left)) (hi.trans inf_le_right)
    have e := hcd B (i, k) j M hM hj
    rw [← hz B (i, k), res_tensorComponent, ← hw, tensorComponent_difference] at e
    rw [res_tensorComponent, res_tensorComponent]
    exact e.symm
  · rw [← iSup_inf_eq, ← p.preimage_iSup, hUtop]
    exact le_inf le_top le_rfl

end GlobalTheory.CechOne
