import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineCechJoinComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleCechBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleExternalProducts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MixedCechKunneth

/-! On joined affine covers, products of line-bundle sections identify the
mixed Čech cohomology with the tensor-product cohomology. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.WH GlobalTheory.SchemeCohomology
open HTGeometry.FinsetCechDatum Finset.HasAntidiagonal

namespace GlobalTheory.LineBundleSections

variable {K : Type} [Field K] {X Y Z : Scheme.{0}}
  {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)} {p : Z ⟶ X} {q : Z ⟶ Y}
  {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ]
  {M : LB X} {N : LB Y} (U : ι → X.Opens) (V : κ → Y.Opens)

private abbrev rectangleCover (p : Z ⟶ X) (q : Z ⟶ Y) (U : ι → X.Opens) (V : κ → Y.Opens) :=
  joinedCover (fun i => p ⁻¹ᵁ U i) (fun j => q ⁻¹ᵁ V j)

local notation "E" => rectangleCover p q U V
local notation "Ext" => twist (M.pull p) (N.pull q) 1

private theorem coverInter_rectangle (I : Finset ι) (J : Finset κ) :
    coverInter (⊤ : Z.Opens) E (uni I J) =
      p ⁻¹ᵁ (coverInter ⊤ U I) ⊓ q ⁻¹ᵁ (coverInter ⊤ V J) := by
  have hp : p ⁻¹ᵁ (coverInter ⊤ U I) = I.inf (fun i => p ⁻¹ᵁ U i) := by
    simpa only [coverInter, top_inf_eq] using (coverInter_pull (π := p) U I).symm
  have hq : q ⁻¹ᵁ (coverInter ⊤ V J) = J.inf (fun j => q ⁻¹ᵁ V j) := by
    simpa only [coverInter, top_inf_eq] using (coverInter_pull (π := q) V J).symm
  rw [hp, hq]
  simp only [rectangleCover, coverInter, top_inf_eq, inf_joinedCover, lft_uni, rgt_uni]

/-- The cohomology dimension on the mixed rectangles is the convolution from
the two Čech complexes, in the degree shifted by the second augmentation. -/
theorem finrank_cech_externalProduct_joined (H : IsPullback p q f g)
    (hM : M.IsLB) (hN : N.IsLB)
    (hU : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter ⊤ U I))
    (hV : ∀ J : Finset κ, J.Nonempty → IsAffineOpen (coverInter ⊤ V J))
    (hchartU : ∀ I : Finset ι, I.Nonempty → ∃ i : M.ι, coverInter ⊤ U I ≤ M.U i)
    (hchartV : ∀ J : Finset κ, J.Nonempty → ∃ j : N.ι, coverInter ⊤ V J ≤ N.U j)
    (hFinU : ∀ n, Module.Finite K ((cech f (toMod M) U).homology n))
    (hFinV : ∀ n, Module.Finite K ((cech g (toMod N) V).homology n)) (n : ℕ) :
    let P := joinedSupport (nonemptyIntersections ι) (nonemptyIntersections κ)
    let hP := joinedSupport_ordConnected (nonemptyIntersections_ordConnected ι) (nonemptyIntersections_ordConnected κ)
    Module.finrank K ((cechOnSupport (p ≫ f) (toMod Ext) E P hP).homology (n + 1)) =
      ∑ x ∈ antidiagonal n, Module.finrank K ((cech f (toMod M) U).homology x.1) *
        Module.finrank K ((cech g (toMod N) V).homology x.2) := by
  let A := sectionDatum (toMod M) U
  let B := sectionDatum (toMod N) V
  let D := sectionDatum (toMod Ext) E
  letI (I : Finset ι) := sectionDatumModule f (toMod M) U I
  letI (J : Finset κ) := sectionDatumModule g (toMod N) V J
  letI (s : Finset (ι ⊕ₗ κ)) := sectionDatumModule (p ≫ f) (toMod Ext) E s
  let P := joinedSupport (nonemptyIntersections ι) (nonemptyIntersections κ)
  let hP := joinedSupport_ordConnected (nonemptyIntersections_ordConnected ι) (nonemptyIntersections_ordConnected κ)
  let T := D.truncate (R := K) P hP
  have hm (I : Finset ι) (J : Finset κ) (hI : I.Nonempty) (hJ : J.Nonempty) : uni I J ∈ P := by
    change (lft (uni I J)).Nonempty ∧ (rgt (uni I J)).Nonempty
    rw [lft_uni, rgt_uni]
    exact ⟨hI, hJ⟩
  have hzero (I : Finset ι) (J : Finset κ) (h : ¬ (I.Nonempty ∧ J.Nonempty)) :
      Subsingleton (T.obj (uni I J)) :=
    D.subsingleton_truncate_obj P hP _ (fun hs => h (by
      change (lft (uni I J)).Nonempty ∧ (rgt (uni I J)).Nonempty at hs
      rwa [lft_uni, rgt_uni] at hs))
  let hrect (I : Finset ι) (J : Finset κ) :=
    coverInter_rectangle (p := p) (q := q) U V I J
  let μ (I : Finset ι) (J : Finset κ) : A.obj I ⊗[K] B.obj J →ₗ[K] D.obj (uni I J) :=
    externalProductMap M N H.w ((hrect I J).le.trans inf_le_left) ((hrect I J).le.trans inf_le_right)
  have hbij (I : Finset ι) (J : Finset κ) (hI : I.Nonempty) (hJ : J.Nonempty) :
      Function.Bijective (μ I J) := by
    obtain ⟨i, hi⟩ := hchartU I hI
    obtain ⟨j, hj⟩ := hchartV J hJ
    exact externalProductMap_bijective_of_eq M N H hM hN (hU I hI) (hV J hJ) (hrect I J) i j hi hj
  let μT (I : Finset ι) (J : Finset κ) (hI : I.Nonempty) (hJ : J.Nonempty) :
      A.obj I ⊗[K] B.obj J ≃ₗ[K] T.obj (uni I J) :=
    LinearEquiv.ofBijective ((μ I J).codRestrict (D.supportCoeff (R := K) P _) fun _ hs =>
      (hs (hm I J hI hJ)).elim)
      ⟨fun _ _ he => (hbij I J hI hJ).injective (congrArg Subtype.val he), fun z => by
        obtain ⟨x, hx⟩ := (hbij I J hI hJ).surjective z.1
        exact ⟨x, Subtype.ext hx⟩⟩
  have hnat {I I' : Finset ι} {J J' : Finset κ} (hi : I ⊆ I') (hj : J ⊆ J')
      (hI : I.Nonempty) (hJ : J.Nonempty) (x : A.obj I) (y : B.obj J) :
      T.res (uni_mono hi hj) (μT I J hI hJ (x ⊗ₜ y)) =
        μT I' J' (hI.mono hi) (hJ.mono hj) (A.res hi x ⊗ₜ B.res hj y) := by
    apply Subtype.ext
    rw [D.truncate_res_value (R := K), if_pos (hm I' J' (hI.mono hi) (hJ.mono hj))]
    change D.res (uni_mono hi hj) (μ I J (x ⊗ₜ y)) =
      μ I' J' (A.res hi x ⊗ₜ B.res hj y)
    exact (externalProductMap_restrict M N H.w _ _ _ _ (coverInter_anti hi)
      (coverInter_anti hj) (coverInter_anti (uni_mono hi hj)) x y).symm
  exact (finrank_mixed_cech A B T (res_base_smul f (toMod M) U)
    (res_base_smul g (toMod N) V) (D.truncate_linear P hP (res_base_smul (p ≫ f) (toMod Ext) E))
    hzero μT hnat hFinU hFinV n).2

end GlobalTheory.LineBundleSections
