import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalSystem

/-! The full function-field tensor acts on the regular forms on chart
pairs. The base coordinate equations retain their weights under this
extension of scalars. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

/-- Send each base coordinate tensor factor to the function field. -/
def diagonalScalarMap : F ⊗[k] F →ₐ[k] E ⊗[k] E :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom k F E) (IsScalarTower.toAlgHom k F E)

/-- The scalar algebra of the normalized chart pair is the tensor of
its two integral closures. -/
def normalizedDiagonalSystem (h : IsPd k x) (q p : ℕ) : WeightedChartSystem k d
    (E ⊗[k] E) (ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p) where
  act := tensorScalarAction
  X i := Units.map (diagonalScalarMap (k := k) (F := F) (E := E)).toMonoidHom
    ((diagonalChartSystem (E := E) h q p).X i)
  Y i := Units.map (diagonalScalarMap (k := k) (F := F) (E := E)).toMonoidHom
    ((diagonalChartSystem (E := E) h q p).Y i)
  R I J := tensorChartRing (rB k E x I) (rB k E x J)
  M := (diagonalChartSystem (E := E) h q p).M

theorem normalizedDiagonalSystem_X (h : IsPd k x) (q p : ℕ) (i : Fin (d + 1)) :
    ((normalizedDiagonalSystem (E := E) h q p).X i : E ⊗[k] E) =
      algebraMap F E (x i) ⊗ₜ[k] (1 : E) := by
  change diagonalScalarMap (x i ⊗ₜ[k] (1 : F)) = _
  rw [diagonalScalarMap, Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem normalizedDiagonalSystem_Y (h : IsPd k x) (q p : ℕ) (i : Fin (d + 1)) :
    ((normalizedDiagonalSystem (E := E) h q p).Y i : E ⊗[k] E) =
      (1 : E) ⊗ₜ[k] algebraMap F E (x i) := by
  change diagonalScalarMap ((1 : F) ⊗ₜ[k] x i) = _
  rw [diagonalScalarMap, Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem tmul_mem_tensorChartRing {A B : Subalgebra k E} {a b : E}
    (ha : a ∈ A) (hb : b ∈ B) : a ⊗ₜ[k] b ∈ tensorChartRing A B := by
  refine ⟨(⟨a, ha⟩ : A) ⊗ₜ[k] (⟨b, hb⟩ : B), ?_⟩
  exact Algebra.TensorProduct.map_tmul A.val B.val _ _

private theorem tensorChartRing_le {A B C D : Subalgebra k E}
    (hAC : A ≤ C) (hBD : B ≤ D) : tensorChartRing A B ≤ tensorChartRing C D := by
  rintro _ ⟨r, rfl⟩
  let f := Subalgebra.inclusion hAC
  let g := Subalgebra.inclusion hBD
  refine ⟨Algebra.TensorProduct.map f g r, ?_⟩
  change ((Algebra.TensorProduct.map C.val D.val).comp (Algebra.TensorProduct.map f g)) r = _
  rw [← Algebra.TensorProduct.map_comp]
  rfl

theorem diagonalScalarMap_mem {I J : Finset (Fin (d + 1))} {s : F ⊗[k] F}
    (hs : s ∈ tensorChartRing (rA k x I) (rA k x J)) :
    diagonalScalarMap (k := k) (F := F) (E := E) s ∈
      tensorChartRing (rB k E x I) (rB k E x J) := by
  obtain ⟨a, rfl⟩ := hs
  induction a using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (zero_mem (tensorChartRing (rB k E x I) (rB k E x J)))
  | add u v hu hv => simpa only [map_add] using add_mem hu hv
  | tmul u v =>
    change diagonalScalarMap (Algebra.TensorProduct.map (rA k x I).val (rA k x J).val (u ⊗ₜ[k] v)) ∈
      tensorChartRing (rB k E x I) (rB k E x J)
    rw [diagonalScalarMap, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    exact tmul_mem_tensorChartRing
      (show IsIntegral (rA k x I) (algebraMap F E (u : F)) from isIntegral_algebraMap (x := u))
      (show IsIntegral (rA k x J) (algebraMap F E (v : F)) from isIntegral_algebraMap (x := v))

theorem normalizedDiagonalSystem_good (h : IsPd k x) (q p : ℕ) :
    (normalizedDiagonalSystem (E := E) h q p).Good := by
  have hT := diagonalChartSystem_good (E := E) h q p
  refine ⟨?_, hT.monoM, ?_, ?_, ?_⟩
  · exact fun _ _ _ _ _ _ hI hJ => tensorChartRing_le (rB_mono (E := E) hI) (rB_mono (E := E) hJ)
  · intro I J _ _ s hs t ht
    have hreg (K : Finset (Fin (d + 1))) (r : ℕ) (a : E) (ha : a ∈ rB k E x K)
        (v : ExteriorDifferentials k E r) (hv : v ∈ regularExteriorLattice (rB k E x K) r) :
        a • v ∈ regularExteriorLattice (rB k E x K) r :=
      smul_mem_omB (B := rB k E x K) (p := r) ha hv
    exact tensorScalarAction_mem_chartLattice (hreg I q) (hreg J p) hs ht
  · intro I J hJ i hi a
    simp only [normalizedDiagonalSystem, ← map_inv, ← map_mul, Units.coe_map]
    exact diagonalScalarMap_mem (hT.memX I J hJ i hi a)
  · intro I J hI j hj a
    simp only [normalizedDiagonalSystem, ← map_inv, ← map_mul, Units.coe_map]
    exact diagonalScalarMap_mem (hT.memY I J hI j hj a)

/-- The action of a base tensor agrees with its action through the
two function-field embeddings. -/
theorem tensorScalarAction_diagonalScalarMap {q p : ℕ} (s : F ⊗[k] F) :
    (tensorScalarAction (diagonalScalarMap (E := E) s) :
      Module.End k (ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p)) =
      tensorScalarAction s := by
  induction s using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    refine TensorProduct.ext' fun u v => ?_
    simp only [diagonalScalarMap, Algebra.TensorProduct.map_tmul, tensorScalarAction_tmul]
    rfl

end GlobalTheory.PD
