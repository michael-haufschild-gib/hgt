import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AdditiveTranslationDifference
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AbelianSchemeGlobalSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FieldTranslationBundles
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.WeilTorsionCharacters
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionOperations
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalLineBundleCoordinates
import Mathlib.Algebra.Field.Equiv

/-! Away from the translation kernel, the translation difference has no nonzero sections.
Multiplying a section by its inversion pullback gives a scalar times a generator. -/

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LineBundleSections GlobalTheory.TwistTranslate
open scoped CategoryTheory.Obj

namespace GlobalTheory.TranslateAdditive

attribute [local instance] Over.cartesianMonoidalCategory

private theorem gs_mul_pullSec {Y : Scheme.{0}} {L : LB Y} {I : Type} [Fintype I]
    {f : I → (Y ⟶ Y)} {d : I → ℤ} (s : (LB.LinComb L f d).Sec)
    (ν : Y ⟶ Y) (z : Y) (i j : I → L.ι) (hi : z ∈ LB.wchart L f i)
    (hj : ν z ∈ LB.wchart L f j) :
    let k := Sum.elim i j
    let B := LB.LinComb L (Sum.elim f (fun l => ν ≫ f l)) (Sum.elim d d)
    gs (𝟙 Y) z (B.U k) ((mulSec s (pullSec s ν)).f k) =
      gs (𝟙 Y) z (LB.wchart L f i) (s.f i) * gs ν z (LB.wchart L f j) (s.f j) := by
  let k := Sum.elim i j
  let W := LB.wchart L (Sum.elim f (fun l => ν ≫ f l)) k
  let V := LB.wchart L (fun l => ν ≫ f l) j
  have h₁ : W ≤ LB.wchart L f i := fun _ hy => Set.mem_iInter.2 fun l => Set.mem_iInter.1 hy (Sum.inl l)
  have h₂ : W ≤ V := fun _ hy => Set.mem_iInter.2 fun l => Set.mem_iInter.1 hy (Sum.inr l)
  have h₃ : V ≤ ν ⁻¹ᵁ LB.wchart L f j := fun _ hy => Set.mem_iInter.2 fun l => Set.mem_iInter.1 hy l
  have hz : z ∈ W := Set.mem_iInter.2 (fun l => by
    cases l with
    | inl l => exact Set.mem_iInter.1 hi l
    | inr l => exact Set.mem_iInter.1 hj l)
  let s' := (pullSec s ν).f j
  change gs (𝟙 Y) z W (resG Y h₁ (s.f i) * resG Y h₂ s') = _
  exact (gs_mul (𝟙 Y) z W hz _ _).trans
    (congrArg₂ (· * ·) (gs_res (𝟙 Y) z h₁ hz _) ((gs_res (𝟙 Y) z h₂ hz _).trans
      ((gs_res (𝟙 Y) z h₃ (h₂ hz) _).trans ((gs_pull (𝟙 Y) ν z _ hj _).trans
        (congrArg (fun r : Y ⟶ Y => gs r z _ (s.f j)) (Category.id_comp ν))))))

/-- A nontrivial translating point of a principal polarization has an acyclic
translation difference in degree zero. -/
theorem section_eq_zero_of_translation_ne_one {K : Type} [Field K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) (hx : x ≠ 1)
    (s : (LB.LinComb L (K := Fin 2) ![(translate A x).left, 𝟙 A.left] ![1, -1]).Sec)
    (i : Fin 2 → L.ι) : s.f i = 0 := by
  by_contra hi
  letI := hA.smooth
  letI := hA.proper
  letI := hA.geomConnected
  letI : GeometricallyIntegral A.hom :=
    geometricallyIntegral_of_quasiCompact_of_smooth_of_geometricallyConnected A.hom
  letI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  letI : IsIso A.hom.appTop := hA.isIso_appTop
  let eK : Γ(A.left, ⊤) ≃+* K := (asIso A.hom.appTop).symm.commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  letI : Field Γ(A.left, ⊤) := (MulEquiv.isField (Semifield.toIsField K) eK.toMulEquiv).toField
  let ν : A ⟶ A := GrpObj.inv
  let f : Fin 2 → (A.left ⟶ A.left) := ![(translate A x).left, 𝟙 A.left]
  let d : Fin 2 → ℤ := ![1, -1]
  let F := Sum.elim f (fun l => ν.left ≫ f l)
  let D := Sum.elim d d
  let M := LB.LinComb L f d
  let B := LB.LinComb L F D
  let s' : B.Sec := mulSec s (pullSec s ν.left)
  obtain ⟨t, ht⟩ := exists_gen_inverse_product hA hL hAmp x
  let g : Fin 4 → (A.left ⟶ A.left) :=
    ![(translate A x).left, 𝟙 A.left, ν.left ≫ (translate A x).left, ν.left]
  obtain ⟨u, hu, -⟩ := exists_gen_of_formEq hL (g := F) (d := D)
    (f := g) (e := ![1, -1, 1, -1]) (fun U _ k => by
      rw [Fintype.prod_sum_type]
      simp only [F, D, f, d, g, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Sum.elim_inl, Sum.elim_inr, Category.comp_id, _root_.mul_one,
        zpow_one, zpow_neg_one, _root_.mul_assoc]) t ht
  obtain ⟨b, hb⟩ := section_proportional_to_gen (hL.linComb F D) s' u hu
  have hν : Function.Surjective ν.left := fun y => ⟨ν.left y,
    congrArg (fun v : A ⟶ A => v.left y) (GrpObj.inv_comp_inv A)⟩
  have hU : (A.left.basicOpen (s.f i) : Set A.left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h => hi ((basicOpen_eq_bot_iff _).1 (TopologicalSpace.Opens.ext h))
  have hV : (ν.left ⁻¹ᵁ A.left.basicOpen (s.f i) : Set A.left).Nonempty := by
    obtain ⟨y, hy⟩ := hU
    obtain ⟨z, rfl⟩ := hν y
    exact ⟨z, hy⟩
  obtain ⟨y, hy, hy'⟩ := nonempty_preirreducible_inter (A.left.basicOpen (s.f i)).isOpen
    (ν.left ⁻¹ᵁ A.left.basicOpen (s.f i)).isOpen hU hV
  have hunit {z : A.left} {j : Fin 2 → L.ι} {r : A.left ⟶ A.left}
      (h : r z ∈ A.left.basicOpen (s.f j)) : IsUnit (gs r z (M.U j) (s.f j)) := by
    rw [gs_eq r z _ (A.left.basicOpen_le (s.f j) h)]
    exact (A.left.mem_basicOpen _ z (A.left.basicOpen_le _ (by
      rw [← Scheme.preimage_basicOpen]; exact h))).1 (by rw [← Scheme.preimage_basicOpen]; exact h)
  have hb₀ : b ≠ 0 := by
    intro hz
    have e := gs_mul_pullSec s ν.left y i i (A.left.basicOpen_le _ hy) (A.left.basicOpen_le _ hy')
    have e₀ : s'.f (Sum.elim i i) = 0 := by
      rw [hb, hz, map_zero, zero_mul]
    have e₁ : gs (𝟙 A.left) y (B.U (Sum.elim i i)) 0 = 0 := by simp [gs]
    have he := (congrArg (gs (𝟙 A.left) y (B.U (Sum.elim i i))) e₀).trans e₁
    exact not_isUnit_zero ((congrArg IsUnit (e.symm.trans he)).mp ((hunit hy).mul (hunit hy')))
  have hu₀ : IsUnit b := Ne.isUnit hb₀
  have hcoeff (j : Fin 2 → L.ι) : IsUnit (s.f j) := by
    apply A.left.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    obtain ⟨k, hk⟩ := exists_chart (hL.linComb f d) (ν.left z)
    let l := Sum.elim j k
    have hzl : z ∈ B.U l := Set.mem_iInter.2 fun q => by
      cases q with
      | inl q => exact Set.mem_iInter.1 hz q
      | inr q => exact Set.mem_iInter.1 hk q
    have he : IsUnit (s'.f l) :=
      (congrArg IsUnit (hb l)).mpr ((hu₀.map (resG A.left le_top)).mul (u.s l).isUnit)
    have huv : IsUnit (gs (𝟙 A.left) z (B.U l) (s'.f l)) := by
      rw [gs_eq (𝟙 A.left) z (B.U l) hzl]
      exact (he.map _).map _
    have hr := isUnit_of_mul_isUnit_left
      ((congrArg IsUnit (gs_mul_pullSec s ν.left z j k hz hk)).mp huv)
    rwa [gs_eq (𝟙 A.left) z (M.U j) hz] at hr
  let v : M.Gen := ⟨fun j => (hcoeff j).unit⟩
  have hv : v.IsGen := fun j k => Units.ext (s.compat j k)
  let E := 𝟙_ (Over (Spec (.of K)))
  let p := snd E A
  let H : Fin 2 → ((E ⊗ A).left ⟶ A.left) := ![(translPt A x).left, p.left]
  have hf (j : Fin 2) : p.left ≫ f j = H j := by
    fin_cases j
    · change (p ≫ translate A x).left = (translPt A x).left
      refine congrArg Over.Hom.left ((MonObj.comp_mul _ _ _).trans ?_)
      exact congrArg₂ (· * ·) ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ x) (toUnit_unique (p ≫ toUnit A) (fst E A)))) (Category.comp_id p)
    · exact Category.comp_id p.left
  obtain ⟨w, hw, -⟩ := exists_gen_of_formEq hL (g := H) (d := d)
    (fun U _ k => Finset.prod_congr rfl fun j _ => congrArg (fun a => k a ^ d j) (hf j))
    (LB.pullGen L f d v p.left) (hv.pullGen f d p.left)
  exact hx (hK K (𝟙 _) x fun _ => ⟨⊤, trivial,
    (AbLaw.Cube.trivial_pull_linComb L hL H d _).2 ⟨_, hw.pullGen H d _⟩⟩)

end GlobalTheory.TranslateAdditive
