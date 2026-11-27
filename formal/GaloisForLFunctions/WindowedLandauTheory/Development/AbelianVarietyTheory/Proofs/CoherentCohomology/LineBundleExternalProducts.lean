import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProductSectionRings
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionScalarChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwists

/-! On an affine rectangle contained in trivializing charts, external products
of line-bundle sections are the tensor product of the two section modules. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

private def sectionMul {X : Scheme.{0}} {M N : LB X} {V : X.Opens}
    (s : Γ(toMod M, V)) (t : Γ(toMod N, V)) : Γ(toMod (twist M N 1), V) :=
  mkTwistSection 1
    (fun p => resG X (inf_le_inf_left V inf_le_left) (coord s p.1) *
      resG X (inf_le_inf_left V inf_le_right) (coord t p.2))
    (fun p q _ hp hq => by
      have hs := coord_rel s p.1 q.1 (hp.trans (inf_le_inf_left V inf_le_left))
        (hq.trans (inf_le_inf_left V inf_le_left))
        (le_inf (hp.trans (inf_le_right.trans inf_le_left)) (hq.trans (inf_le_right.trans inf_le_left)))
      have ht := coord_rel t p.2 q.2 (hp.trans (inf_le_inf_left V inf_le_right))
        (hq.trans (inf_le_inf_left V inf_le_right))
        (le_inf (hp.trans (inf_le_right.trans inf_le_right)) (hq.trans (inf_le_right.trans inf_le_right)))
      rw [map_mul, map_mul, resG_resG, resG_resG, resG_resG, resG_resG, hs, ht, zpow_one, Units.val_mul]
      exact mul_mul_mul_comm _ _ _ _)

private theorem coord_sectionMul {X : Scheme.{0}} {M N : LB X} {V : X.Opens}
    (s : Γ(toMod M, V)) (t : Γ(toMod N, V)) (p : M.ι × N.ι) :
    coord (sectionMul s t) p = resG X (inf_le_inf_left V inf_le_left) (coord s p.1) *
      resG X (inf_le_inf_left V inf_le_right) (coord t p.2) := rfl

private theorem sectionMul_restrict {X : Scheme.{0}} {M N : LB X} {V W : X.Opens}
    (s : Γ(toMod M, V)) (t : Γ(toMod N, V)) (h : W ≤ V) :
    sectionMul ((toMod M).presheaf.map (homOfLE h).op s) ((toMod N).presheaf.map (homOfLE h).op t) =
      (toMod (twist M N 1)).presheaf.map (homOfLE h).op (sectionMul s t) := by
  apply sec_ext
  rintro ⟨i, j⟩
  let A := (twist M N 1).U (i, j)
  have e := (resG X (inf_le_inf_right A h)).map_mul
    (resG X (inf_le_inf_left V inf_le_left : V ⊓ A ≤ V ⊓ M.U i) (coord s i))
    (resG X (inf_le_inf_left V inf_le_right : V ⊓ A ≤ V ⊓ N.U j) (coord t j))
  simp only [coord_sectionMul, coord_map, resG_resG]
  simp only [A, resG_resG] at e
  exact e.symm

private theorem chartEquiv_sectionMul {X : Scheme.{0}} {M N : LB X} {V : X.Opens}
    (hM : M.IsLB) (hN : N.IsLB) (i : M.ι) (j : N.ι) (hi : V ≤ M.U i) (hj : V ≤ N.U j)
    (s : Γ(toMod M, V)) (t : Γ(toMod N, V)) :
    chartEquiv (twist_isLB hM hN 1) (i, j) (le_inf hi hj) (sectionMul s t) =
      chartEquiv hM i hi s * chartEquiv hN j hj t := by
  let A := (twist M N 1).U (i, j)
  have e := (resG X (le_inf le_rfl (le_inf hi hj) : V ≤ V ⊓ A)).map_mul
    (resG X (inf_le_inf_left V inf_le_left : V ⊓ A ≤ V ⊓ M.U i) (coord s i))
    (resG X (inf_le_inf_left V inf_le_right : V ⊓ A ≤ V ⊓ N.U j) (coord t j))
  simp only [chartEquiv_apply, coord_sectionMul]
  simp only [A, resG_resG] at e
  exact e

variable {K : Type} [Field K] {X Y Z : Scheme.{0}}
  {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)} {p : Z ⟶ X} {q : Z ⟶ Y}
  (M : LB X) (N : LB Y)

local notation "Ext" => twist (M.pull p) (N.pull q) 1

/-- Pull back each factor and multiply on the common open. -/
def externalProductMap (h : p ≫ f = q ≫ g)
    {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (hU : W ≤ p ⁻¹ᵁ U) (hV : W ≤ q ⁻¹ᵁ V) :
    letI := sectionBaseModule f (toMod M) U
    letI := sectionBaseModule g (toMod N) V
    letI := sectionBaseModule (p ≫ f) (toMod Ext) W
    Γ(toMod M, U) ⊗[K] Γ(toMod N, V) →ₗ[K] Γ(toMod Ext, W) := by
  letI := sectionBaseModule f (toMod M) U
  letI := sectionBaseModule g (toMod N) V
  letI := sectionBaseModule (p ≫ f) (toMod Ext) W
  letI := sectionAlgebra f U
  letI := sectionAlgebra g V
  letI := sectionAlgebra (p ≫ f) W
  let a := pullSection (ChartPull.pull M p) hU
  let b := pullSection (ChartPull.pull N q) hV
  refine TensorProduct.lift (LinearMap.mk₂ K (fun x y => sectionMul (a x) (b y)) ?_ ?_ ?_ ?_)
  · intro x x' y
    rw [map_add]
    exact sec_ext fun i => by
      simp only [coord_sectionMul, coord_add, map_add]
      exact (fun (R : CommRingCat.{0}) (a b c : R) => add_mul a b c)
        Γ(Z, W ⊓ (Ext).U i) _ _ _
  · intro r x y
    change sectionMul (a (algebraMap K Γ(X, U) r • x)) (b y) =
      algebraMap K Γ(Z, W) r • sectionMul (a x) (b y)
    have e := (sectionPullbackLE (f := f) (p := p) (g := f) (q := p) rfl hU).commutes r
    change p.appLE U W hU (algebraMap K Γ(X, U) r) = algebraMap K Γ(Z, W) r at e
    rw [show a (algebraMap K Γ(X, U) r • x) =
      p.appLE U W hU (algebraMap K Γ(X, U) r) • a x from pullSection_smul _ _ _ _, e]
    exact sec_ext fun i => by
      simp only [coord_sectionMul, coord_smul, map_mul, resG_resG]
      exact mul_assoc _ _ _
  · intro x y y'
    rw [map_add]
    exact sec_ext fun i => by
      simp only [coord_sectionMul, coord_add, map_add]
      exact (fun (R : CommRingCat.{0}) (a b c : R) => mul_add a b c)
        Γ(Z, W ⊓ (Ext).U i) _ _ _
  · intro r x y
    change sectionMul (a x) (b (algebraMap K Γ(Y, V) r • y)) =
      algebraMap K Γ(Z, W) r • sectionMul (a x) (b y)
    have e := (sectionPullbackLE h hV).commutes r
    change q.appLE V W hV (algebraMap K Γ(Y, V) r) = algebraMap K Γ(Z, W) r at e
    rw [show b (algebraMap K Γ(Y, V) r • y) =
      q.appLE V W hV (algebraMap K Γ(Y, V) r) • b y from pullSection_smul _ _ _ _, e]
    exact sec_ext fun i => by
      simp only [coord_sectionMul, coord_smul, map_mul, resG_resG]
      exact mul_left_comm _ _ _

theorem externalProductMap_restrict (h : p ≫ f = q ≫ g)
    {U U' : X.Opens} {V V' : Y.Opens} {W W' : Z.Opens}
    (hU : W ≤ p ⁻¹ᵁ U) (hV : W ≤ q ⁻¹ᵁ V) (hU' : W' ≤ p ⁻¹ᵁ U') (hV' : W' ≤ q ⁻¹ᵁ V')
    (i : U' ≤ U) (j : V' ≤ V) (k : W' ≤ W)
    (s : Γ(toMod M, U)) (t : Γ(toMod N, V)) :
    letI := sectionBaseModule f (toMod M) U
    letI := sectionBaseModule g (toMod N) V
    letI := sectionBaseModule f (toMod M) U'
    letI := sectionBaseModule g (toMod N) V'
    externalProductMap M N h hU' hV'
      (((toMod M).presheaf.map (homOfLE i).op s) ⊗ₜ ((toMod N).presheaf.map (homOfLE j).op t)) =
      (toMod Ext).presheaf.map (homOfLE k).op (externalProductMap M N h hU hV (s ⊗ₜ t)) := by
  change sectionMul (pullSection (ChartPull.pull M p) hU' ((toMod M).presheaf.map (homOfLE i).op s))
    (pullSection (ChartPull.pull N q) hV' ((toMod N).presheaf.map (homOfLE j).op t)) = _
  rw [pullSection_restrict _ hU hU' i k, pullSection_restrict _ hV hV' j k]
  exact sectionMul_restrict _ _ k

/-- Trivializing the two bundles identifies their external product map with
the affine rectangle isomorphism for regular functions. -/
theorem externalProductMap_bijective (H : IsPullback p q f g) (hM : M.IsLB) (hN : N.IsLB)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (i : M.ι) (j : N.ι) (hi : U ≤ M.U i) (hj : V ≤ N.U j) :
    Function.Bijective (externalProductMap M N H.w
      (W := p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) inf_le_left inf_le_right) := by
  let W := p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V
  letI := sectionAlgebra f U
  letI := sectionAlgebra g V
  letI := sectionAlgebra (p ≫ f) W
  letI := sectionBaseModule f (toMod M) U
  letI := sectionBaseModule g (toMod N) V
  letI := sectionBaseModule (p ≫ f) (toMod Ext) W
  letI : IsScalarTower K Γ(X, U) Γ(toMod M, U) := .of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower K Γ(Y, V) Γ(toMod N, V) := .of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower K Γ(Z, W) Γ(toMod Ext, W) := .of_algebraMap_smul fun _ _ => rfl
  let i' : (M.pull p).ι := fun _ => i
  let j' : (N.pull q).ι := fun _ => j
  have hi' : W ≤ (M.pull p).U i' :=
    inf_le_left.trans ((p.preimage_mono hi).trans (pull_chart M p i).ge)
  have hj' : W ≤ (N.pull q).U j' :=
    inf_le_right.trans ((q.preimage_mono hj).trans (pull_chart N q j).ge)
  let eX : Γ(toMod M, U) ≃ₗ[K] SectionRing f U := (chartEquiv hM i hi).restrictScalars K
  let eY : Γ(toMod N, V) ≃ₗ[K] SectionRing g V := (chartEquiv hN j hj).restrictScalars K
  let eZ : Γ(toMod Ext, W) ≃ₗ[K] SectionRing (p ≫ f) W :=
    (chartEquiv (twist_isLB (hM.pull p) (hN.pull q) 1) (i', j') (le_inf hi' hj')).restrictScalars K
  let e := (TensorProduct.congr eX eY).trans ((productSectionsEquiv H U V hU hV).toLinearEquiv.trans eZ.symm)
  have he : externalProductMap M N H.w (W := W) inf_le_left inf_le_right = e.toLinearMap := by
    refine TensorProduct.ext' fun s t => eZ.injective ?_
    change chartEquiv (twist_isLB (hM.pull p) (hN.pull q) 1) (i', j') (le_inf hi' hj')
      (sectionMul (pullSection (ChartPull.pull M p) inf_le_left s)
        (pullSection (ChartPull.pull N q) inf_le_right t)) = eZ (e (s ⊗ₜ t))
    rw [chartEquiv_sectionMul (hM.pull p) (hN.pull q) i' j' hi' hj',
      chartEquiv_pullSection _ hM (hM.pull p) _ hi hi',
      chartEquiv_pullSection _ hN (hN.pull q) _ hj hj']
    change _ = eZ (eZ.symm (productSectionsEquiv H U V hU hV (eX s ⊗ₜ eY t)))
    rw [eZ.apply_symm_apply, productSectionsEquiv_tmul]
    rfl
  rw [he]
  exact e.bijective

theorem externalProductMap_bijective_of_eq (H : IsPullback p q f g) (hM : M.IsLB) (hN : N.IsLB)
    {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : W = p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) (i : M.ι) (j : N.ι)
    (hi : U ≤ M.U i) (hj : V ≤ N.U j) :
    Function.Bijective (externalProductMap M N H.w (e.le.trans inf_le_left) (e.le.trans inf_le_right)) := by
  subst W
  exact externalProductMap_bijective M N H hM hN hU hV i j hi hj

end GlobalTheory.LineBundleSections
