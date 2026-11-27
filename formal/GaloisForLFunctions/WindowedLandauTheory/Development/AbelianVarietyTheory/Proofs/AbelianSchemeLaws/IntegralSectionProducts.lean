import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionModule
import Mathlib.AlgebraicGeometry.FunctionField

/-! Multiplication by a nonzero section of a formal line-bundle product
is injective on an integral scheme. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.MulSplit

variable {X Y B : Scheme.{0}} [IsIntegral Y] {L : LB X} {p : Y ⟶ B}

private theorem section_zero_of_coord_zero {M : LB Y} (s : M.Sec) {i : M.ι}
    (hi : (M.U i : Set Y).Nonempty) (hzero : s.f i = 0) (j : M.ι) : s.f j = 0 := by
  by_cases hj : (M.U j : Set Y).Nonempty
  · have hn : ((M.U j ⊓ M.U i : Y.Opens) : Set Y).Nonempty :=
      nonempty_preirreducible_inter (M.U j).isOpen (M.U i).isOpen hj hi
    letI : Nonempty (M.U j ⊓ M.U i : Y.Opens) := hn.to_subtype
    let a : (M.U j ⊓ M.U i : Y.Opens) ⟶ M.U j := homOfLE inf_le_left
    apply map_injective_of_isIntegral Y a
    rw [map_zero]
    have h := s.compat j i
    rw [hzero, map_zero, mul_zero] at h
    exact h
  · exact fn_ext fun z hz => (hj ⟨z, hz⟩).elim

private theorem gs_identity_injective (y : Y) {V : Y.Opens} (hy : (𝟙 Y) y ∈ V) :
    Function.Injective (gs (𝟙 Y) y V) := by
  let a := (𝟙 Y : Y ⟶ Y).app V
  letI : IsIso a := inferInstanceAs (IsIso ((𝟙 Y : Y ⟶ Y).app V))
  intro u v huv
  have h : (Y.presheaf.germ ((𝟙 Y) ⁻¹ᵁ V) y hy).hom (a u) =
      (Y.presheaf.germ ((𝟙 Y) ⁻¹ᵁ V) y hy).hom (a v) :=
    (gs_eq (𝟙 Y) y V hy u).symm.trans (huv.trans (gs_eq (𝟙 Y) y V hy v))
  exact (ConcreteCategory.bijective_of_isIso a).injective
    (germ_injective_of_isIntegral Y y hy h)

private theorem section_value_ne_zero_at_identity {D : (Y ⟶ X) →₀ ℤ} {v : Sg L p D}
    (hv : v ≠ 0) (y : Y) (J : (Y ⟶ X) → L.ι) (hJ : Good L y J) :
    v.1 ⟨(y, J, 𝟙 Y), hJ, Category.id_comp p⟩ ≠ 0 := by
  obtain ⟨s, hs⟩ := v.2
  let f (j : D.support) := j.1
  let i (j : D.support) := J (𝟙 Y ≫ f j)
  let V := LB.wchart L f i
  have hy : (𝟙 Y) y ∈ V := hJ.mem f (𝟙 Y)
  intro hz
  apply hv
  apply Subtype.ext
  have he : gs (𝟙 Y) y V (s.f i) = 0 :=
    (congrFun hs ⟨(y, J, 𝟙 Y), hJ, Category.id_comp p⟩).trans hz
  have h₀ : gs (𝟙 Y) y V 0 = 0 := by rw [gs_eq _ _ _ hy, map_zero, map_zero]
  have hs₀ := gs_identity_injective y hy (he.trans h₀.symm)
  exact hs.symm.trans (ev_zero (section_zero_of_coord_zero s ⟨y, hy⟩ hs₀))

/-- A nonzero section gives an injective linear map into the module for
the sum of the two formal products. At identity probes, nonzero sections
have nonzero values in the integral stalk rings. -/
theorem exists_injective_mul_section (hL : L.IsLB) {D E : (Y ⟶ X) →₀ ℤ}
    {w : Sg L p E} (hw : w ≠ 0) :
    ∃ μ : Sg L p D →ₗ[Γ(B, ⊤)] Sg L p (E + D), Function.Injective μ := by
  classical
  let μ : Sg L p D →ₗ[Γ(B, ⊤)] Sg L p (E + D) :=
    { toFun := fun v => ⟨w.1 * v.1, mul_mem_Sg hL w.2 v.2 rfl⟩
      map_add' := fun v v' => Subtype.ext (mul_add w.1 v.1 v'.1)
      map_smul' := fun a v => Subtype.ext (Algebra.mul_smul_comm a w.1 v.1) }
  refine ⟨μ, (injective_iff_map_eq_zero μ).mpr fun v hv => ?_⟩
  by_contra hv'
  let y : Y := Classical.choice (inferInstance : Nonempty Y)
  choose J hJ using fun q : Y ⟶ X => exists_chart hL (q y)
  let i : Idx L p := ⟨(y, J, 𝟙 Y), hJ, Category.id_comp p⟩
  have hz : w.1 i * v.1 i = 0 := congrFun (congrArg Subtype.val hv) i
  exact mul_ne_zero (section_value_ne_zero_at_identity hw y J hJ)
    (section_value_ne_zero_at_identity hv' y J hJ) hz

end GlobalTheory.MulSplit
