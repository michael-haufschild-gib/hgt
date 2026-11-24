import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleJoinedCover
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphTensorPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartScalarMap
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartDifferential
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartColumnScaling

/-! The graph specialization of the weighted diagonal complex is
regular on the joined affine cover of the correspondence. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.WH

open GlobalTheory.PD

private theorem pullbackChartAlgebra_mono {k E L : Type}
    [Field k] [Field E] [Field L] [Algebra k E] [Algebra k L]
    (f : E →ₐ[k] L) {A B : Subalgebra k E} (h : A ≤ B) :
    pullbackChartAlgebra f A ≤ pullbackChartAlgebra f B := by
  have hmap : A.map f ≤ B.map f := Subalgebra.map_mono h
  letI : Algebra (A.map f) (B.map f) := (Subalgebra.inclusion hmap).toRingHom.toAlgebra
  letI : IsScalarTower (A.map f) (B.map f) L := .of_algebraMap_eq fun _ => rfl
  intro a ha
  exact (show IsIntegral (A.map f) a from ha).tower_top (A := B.map f)

private theorem graphFormPullback_lattice_le {k E L : Type}
    [Field k] [Field E] [Field L] [Algebra k E] [Algebra k L]
    (f₁ f₂ : E →ₐ[k] L) (A B : Subalgebra k E) (C : Subalgebra k L)
    (hA : A.map f₁ ≤ C) (hB : B.map f₂ ≤ C) (q p : ℕ) :
    tensorChartLattice (regularExteriorLattice A q) (regularExteriorLattice B p) ≤
      (omB k L C (q + p)).comap (graphFormPullback f₁ f₂) := by
  refine Submodule.map₂_le.mpr ?_
  intro u hu v hv
  have hu' : (u : DR k E) ∈ omB k E A q := hu
  have hv' : (v : DR k E) ∈ omB k E B p := hv
  have h₁ : pullbackDR f₁ (u : DR k E) ∈ omB k L C q :=
    IsDRMap.regularForms k (isDRMap_pullbackDR k f₁) hA q hu'
  have h₂ : pullbackDR f₂ (v : DR k E) ∈ omB k L C p :=
    IsDRMap.regularForms k (isDRMap_pullbackDR k f₂) hB p hv'
  change graphFormPullback f₁ f₂ (u ⊗ₜ[k] v) ∈ omB k L C (q + p)
  rw [graphFormPullback_tmul]
  exact mul_mem_omB (B := C) h₁ h₂

variable {k F E L : Type} [Field k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra E L] [Algebra F L]
  [IsScalarTower k F E] [IsScalarTower k E L] [IsScalarTower k F L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (j₂ : E →ₐ[k] L) (q p : ℕ)

local notation "j₁" => IsScalarTower.toAlgHom k E L
local notation "T" => normalizedDiagonalSystem (E := E) h q p
local notation "g" => graphScalarMap (j₁) j₂

/-- Scalar substitution in the diagonal chart system, with regular
forms on the two pulled-back charts. -/
def graphChartSystem : WeightedChartSystem k d L (DR k L) where
  act := Algebra.lsmul k k (DR k L)
  X i := Units.map (g).toMonoidHom ((T).X i)
  Y i := Units.map (g).toMonoidHom ((T).Y i)
  R := RY x j₂
  M I J := omB k L (RY x j₂ I J) (q + p)

local notation "U" => graphChartSystem h j₂ q p

private theorem leftChartImage_le (I : Finset (Fin (d + 1))) :
    (rB k E x I).map (j₁) ≤ rB k L x I := by
  rintro _ ⟨b, hb, rfl⟩
  exact (show IsIntegral (rA k x I) b from hb).algebraMap

omit [Algebra E L] [Algebra F L] [IsScalarTower k E L] [IsScalarTower k F L]
  [IsScalarTower F E L] in
/-- The right chart normalization contains the image of its chart algebra. -/
theorem rB_map_le_R2 (J : Finset (Fin (d + 1))) :
    (rB k E x J).map j₂ ≤ R2 x j₂ J :=
  fun a ha => isIntegral_algebraMap (x := (⟨a, ha⟩ : (rB k E x J).map j₂))

theorem graphScalarMap_mem {I J : Finset (Fin (d + 1))} {s : E ⊗[k] E}
    (hs : s ∈ tensorChartRing (rB k E x I) (rB k E x J)) :
    (g) s ∈ RY x j₂ I J := by
  obtain ⟨a, rfl⟩ := hs
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact zero_mem _
  | add u v hu hv => simpa only [map_add] using add_mem hu hv
  | tmul u v =>
    change (g) (Algebra.TensorProduct.map (rB k E x I).val (rB k E x J).val (u ⊗ₜ[k] v)) ∈
      RY x j₂ I J
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.productMap_apply_tmul]
    have h₁ : rB k L x I ≤ RY x j₂ I J := le_sup_left
    have h₂ : R2 x j₂ J ≤ RY x j₂ I J := le_sup_right
    have hu : (j₁) (u : E) ∈ (rB k E x I).map (j₁) := ⟨(u : E), u.property, rfl⟩
    have hv : j₂ (v : E) ∈ (rB k E x J).map j₂ := ⟨(v : E), v.property, rfl⟩
    exact mul_mem (h₁ (leftChartImage_le (k := k) (L := L) (x := x) I hu))
      (h₂ (rB_map_le_R2 j₂ (x := x) J hv))

theorem graphChartSystem_good : (U).Good := by
  let G := normalizedDiagonalSystem_good (E := E) h q p
  have hR (I I' J J' : Finset (Fin (d + 1))) (hI : I ⊆ I') (hJ : J ⊆ J') :
      RY x j₂ I J ≤ RY x j₂ I' J' := by
    have hleft : rB k L x I ≤ rB k L x I' := rB_mono hI
    have hright : R2 x j₂ J ≤ R2 x j₂ J' :=
      pullbackChartAlgebra_mono j₂ (rB_mono (k := k) (E := E) (x := x) hJ)
    exact sup_le_sup hleft hright
  refine ⟨fun I I' J J' _ _ hI hJ => hR I I' J J' hI hJ,
    fun I I' J J' _ _ hI hJ => omB_mono (hR I I' J J' hI hJ) (q + p), ?_, ?_, ?_⟩
  · intro I J _ _ r hr a ha
    exact smul_mem_omB hr ha
  · intro I J hJ i hi a
    simp only [graphChartSystem, ← map_inv, ← map_mul, Units.coe_map]
    exact graphScalarMap_mem j₂ (G.memX I J hJ i hi a)
  · intro I J hI j hj a
    simp only [graphChartSystem, ← map_inv, ← map_mul, Units.coe_map]
    exact graphScalarMap_mem j₂ (G.memY I J hI j hj a)

variable {κ : Type} [LinearOrder κ]

omit [IsScalarTower F E L] [LinearOrder κ] in
theorem graphChartSystem_normalizedWeight_map (n : κ → ℕ × ℕ) (z : κ → E ⊗[k] E)
    (i j : Fin (d + 1)) (l : κ) :
    (U).normalizedWeight n ((g) ∘ z) i j l = (g) ((T).normalizedWeight n z i j l) := by
  have hU : (U).weightUnit n i j l = Units.map (g).toMonoidHom ((T).weightUnit n i j l) := by
    simp only [weightUnit, map_mul, map_pow]
    rfl
  rw [normalizedWeight, hU, ← map_inv, Units.coe_map, normalizedWeight, map_mul]
  rfl

omit [LinearOrder κ] in
theorem graphChartSystem_admitted_map (n : κ → ℕ × ℕ) (z : κ → E ⊗[k] E)
    (hz : (T).Admitted n z) : (U).Admitted n ((g) ∘ z) := by
  intro i j l
  rw [graphChartSystem_normalizedWeight_map]
  exact graphScalarMap_mem j₂ (hz i j l)

omit [IsScalarTower F E L] [LinearOrder κ] in
/-- Graph pullback commutes with removal of the homogeneous
normalization product from a column component. -/
theorem graphFormPullback_unscale (n : κ → ℕ × ℕ) (i j : Fin (d + 1))
    (a : Finset κ → ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p)
    (K : Finset κ) :
    graphFormPullback (j₁) j₂ (((T).scaleColumn n i j).symm a K) =
      ((U).scaleColumn n i j).symm (fun S => graphFormPullback (j₁) j₂ (a S)) K := by
  have hprod : (U).normalizationProduct n i j K =
      Units.map (g).toMonoidHom ((T).normalizationProduct n i j K) := by
    simp only [normalizationProduct, map_prod]
    refine Finset.prod_congr rfl fun l _ => ?_
    simp only [weightUnit, map_mul, map_pow]
    rfl
  change graphFormPullback (j₁) j₂ (tensorScalarAction
    ((((T).normalizationProduct n i j K)⁻¹ : (E ⊗[k] E)ˣ) : E ⊗[k] E) (a K)) = _
  rw [graphFormPullback_action]
  change _ = ((((U).normalizationProduct n i j K)⁻¹ : Lˣ) : L) •
    graphFormPullback (j₁) j₂ (a K)
  rw [hprod, ← map_inv, Units.coe_map]
  rfl

private theorem graphFormPullback_mem_lattice (I J : Finset (Fin (d + 1))) :
    (T).M I J ≤ ((U).M I J).comap (graphFormPullback (j₁) j₂) := by
  have h₁ : (rB k E x I).map (j₁) ≤ RY x j₂ I J :=
    (leftChartImage_le (k := k) (L := L) (x := x) I).trans le_sup_left
  have h₂ : (rB k E x J).map j₂ ≤ RY x j₂ I J := (rB_map_le_R2 j₂ (x := x) J).trans le_sup_right
  exact graphFormPullback_lattice_le (j₁) j₂ (rB k E x I) (rB k E x J) (RY x j₂ I J) h₁ h₂ q p

/-- Chartwise pullback and exterior multiplication preserve the
weighted terms and commute with the total differential. -/
theorem graphFormPullback_isMap (n : κ → ℕ × ℕ) (z : κ → E ⊗[k] E) :
    IsMap ((T).complex n z) ((U).complex n ((g) ∘ z))
      (mapCochain (ι := ChartPair d ⊕ₗ κ)
        (M := ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p)
        (N := DR k L) (graphFormPullback (j₁) j₂)) :=
  isMap_of_scalarMap (T) (U) (g) _ (fun _ => rfl) (fun _ => rfl)
    (graphFormPullback_action (j₁) j₂) (fun I J _ _ => graphFormPullback_mem_lattice h j₂ q p I J) n z

end GlobalTheory.WH
