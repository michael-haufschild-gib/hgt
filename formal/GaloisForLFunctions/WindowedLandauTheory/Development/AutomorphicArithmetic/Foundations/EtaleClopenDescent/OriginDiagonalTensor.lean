import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginDiagonalMinor
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalGlobalClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartColumnScaling

/-! The selected diagonal component at the origin normalizes to a
regular tensor with the affine volume identity contraction. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d p q : ℕ} {x : Fin (d + 1) → F}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "π" => (Algebra.TensorProduct.lmul' k : F ⊗[k] F →ₐ[k] F)
local notation "V" => ExteriorDifferentials k E q
local notation "W" => ExteriorDifferentials k E p

/-- A regular tensor is a finite sum of tensors whose two factors
are regular on their respective charts. -/
theorem exists_tensorChartLattice_family {k M N : Type} [Field k]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {A : Submodule k M} {B : Submodule k N}
    {t : M ⊗[k] N} (ht : t ∈ tensorChartLattice A B) :
    ∃ (n : ℕ) (u : Fin n → A) (v : Fin n → B),
      t = ∑ j, (u j : M) ⊗ₜ[k] (v j : N) := by
  let f := TensorProduct.map A.subtype B.subtype
  have hle : tensorChartLattice A B ≤ LinearMap.range f := by
    refine Submodule.map₂_le.mpr fun a ha b hb => ?_
    exact ⟨(⟨a, ha⟩ : A) ⊗ₜ[k] (⟨b, hb⟩ : B), TensorProduct.map_tmul _ _ _ _⟩
  obtain ⟨s, rfl⟩ := hle ht
  clear ht
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a b =>
    exact ⟨1, fun _ => a, fun _ => b, by simp [f, TensorProduct.map_tmul]⟩
  | add u v hu hv =>
    obtain ⟨m, a, b, ha⟩ := hu
    obtain ⟨n, c, d, hc⟩ := hv
    refine ⟨m + n, Fin.append a c, Fin.append b d, ?_⟩
    rw [map_add, ha, hc, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

/-- Remove the homogeneous scale and the diagonal sign from the
selected component of the origin column. -/
theorem IsFinCover.affineIdentityTensor_of_originColumn (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E)
    (c : Finset (DiagonalIndex d) → V ⊗[k] W) :
    let T := diagonalChartSystem (E := E) h.pd q p
    let n := fun _ : DiagonalIndex d => ((1, 1) : ℕ × ℕ)
    let I := selectedIndices (diagonalIndexEmbedding (0 : Fin (d + 1)))
    c ∈ (T.columnComplex n T.homogeneousMinor {0} {0}).C (d : ℤ) →
    (∀ v : W, tensorContraction ((traceWedgeLeftDual (F := F) τ).flip v) (c I) =
      (-1 : ℤ) ^ d • (π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} I)) • v)) →
    let t := ((-1 : k) ^ d) • (T.scaleColumn n 0 0).symm c I
    t ∈ T.M {0} {0} ∧
      ∀ v : W, tensorContraction ((traceWedgeLeftDual (F := F) τ).flip v) t =
        (∏ j : Fin d, x j.succ / x 0) • v := by
  intro T n I hc hs t
  let a := (T.scaleColumn n 0 0).symm c
  have hscale : T.scaleColumn n 0 0 a = c := (T.scaleColumn n 0 0).apply_symm_apply c
  have hterm := (T.scaleColumn_mem_terms_iff
    (diagonalChartSystem_good (E := E) h.pd q p) n T.homogeneousMinor
    (Finset.mem_singleton_self 0) (Finset.mem_singleton_self 0) d a).mp (hscale.symm ▸ hc)
  have hcard : ((I.card : ℕ) : ℤ) = d := by simp [I, selectedIndices]
  have hmem : a I ∈ T.M {0} {0} := by
    simpa only [hcard, if_true] using acx_mem_terms_iff.mp hterm I
  refine ⟨Submodule.smul_mem _ _ hmem, ?_⟩
  intro v
  let f : V ⊗[k] W →ₗ[k] W := tensorContraction ((traceWedgeLeftDual (F := F) τ).flip v)
  let U := T.normalizationProduct n 0 0 I
  let H := orderedMinor T.minorRows (uni ({0} : Finset (Fin (d + 1))) I)
  let r : F := ∏ j : Fin d, x j.succ / x 0
  have hU : π (U : F ⊗[k] F) = ∏ _ : Fin d, x 0 * x 0 := by
    change π ((∏ j ∈ I, T.weightUnit n 0 0 j : (F ⊗[k] F)ˣ) : F ⊗[k] F) = _
    rw [Units.coe_prod, map_prod, show I = Finset.univ.map (diagonalIndexEmbedding 0).toEmbedding from rfl, Finset.prod_map]
    refine Finset.prod_congr rfl fun j _ => ?_
    change π ((T.X 0 ^ 1 * T.Y 0 ^ 1 : (F ⊗[k] F)ˣ) : F ⊗[k] F) = _
    simp only [pow_one, Units.val_mul, map_mul, show (T.X 0 : F ⊗[k] F) = x 0 ⊗ₜ[k] (1 : F) from rfl,
      show (T.Y 0 : F ⊗[k] F) = (1 : F) ⊗ₜ[k] x 0 from rfl,
      Algebra.TensorProduct.lmul'_apply_tmul, mul_one, one_mul]
  have hH : π H = ∏ j : Fin d, x j.succ * x 0 := by
    have hM : H = ∏ j : Fin d, (T.X j.succ : F ⊗[k] F) * (T.Y 0 : F ⊗[k] F) :=
      T.orderedMinor_originSelection
    rw [hM, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    change π ((x j.succ ⊗ₜ[k] (1 : F)) * ((1 : F) ⊗ₜ[k] x 0)) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      Algebra.TensorProduct.lmul'_apply_tmul]
  have heq : π H = π (U : F ⊗[k] F) * r := by
    dsimp only [r]
    rw [hH, hU, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    field_simp [h.pd.ne 0] <;> ring
  have hne : π (U : F ⊗[k] F) ≠ 0 := (U.isUnit.map (π).toMonoidHom).ne_zero
  have hsign := hs v
  have hu : tensorScalarAction (U : F ⊗[k] F) (a I) = c I := congrFun hscale I
  change f (c I) = (-1 : ℤ) ^ d • (π H • v) at hsign
  rw [← hu, tensorContraction_action, heq, mul_smul, smul_comm ((-1 : ℤ) ^ d)] at hsign
  have ha := smul_right_injective W hne hsign
  change f (((-1 : k) ^ d) • a I) = r • v
  rw [map_smul, ha]
  have hs' : ((-1 : k) ^ d) • ((-1 : ℤ) ^ d • (r • v)) = r • v := by
    rw [← Int.cast_smul_eq_zsmul k, Int.cast_pow, Int.cast_neg, Int.cast_one,
      smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]
  exact hs'

end GlobalTheory.PD
