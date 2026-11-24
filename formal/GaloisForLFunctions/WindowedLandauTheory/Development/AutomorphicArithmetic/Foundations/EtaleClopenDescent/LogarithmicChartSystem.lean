import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicCoefficientLattice
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCoefficientLift

/-! Wedge trace on the left converts the two form factors to a
logarithmic coefficient and a regular right form. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

/-- The left logarithmic coefficient system has the same coordinate
weights and chart rings as the regular form tensor system. -/
def logarithmicChartSystem (h : IsPd k x) (p : ℕ) :
    WeightedChartSystem k d (F ⊗[k] F) (F ⊗[k] ExteriorDifferentials k E p) where
  act := tensorScalarAction
  X := (diagonalChartSystem (E := E) h p p).X
  Y := (diagonalChartSystem (E := E) h p p).Y
  R := (diagonalChartSystem (E := E) h p p).R
  M I J := tensorChartLattice (logCoefficientLattice k x I)
    (regularExteriorLattice (rB k E x J) p)

theorem logarithmicChartSystem_good (h : IsPd k x) (p : ℕ) :
    (logarithmicChartSystem (E := E) h p).Good := by
  have hT := diagonalChartSystem_good (E := E) h p p
  refine ⟨hT.monoR, ?_, ?_, hT.memX, hT.memY⟩
  · intro I I' J J' hI _ hII hJJ
    refine Submodule.map₂_le.mpr fun a ha b hb =>
      Submodule.apply_mem_map₂ _ (h.logCoefficientLattice_mono hI hII ha) ?_
    exact omB_mono (rB_mono (E := E) (x := x) hJJ) p hb
  · intro I J hI _ r hr v hv
    exact tensorScalarAction_mem_chartLattice
      (fun _ hs _ hu => h.smul_mem_logCoefficientLattice hI hs hu)
      (smul_mem_regularExteriorLattice J p) hr hv

theorem logarithmicChartSystem_admitted (h : IsPd k x) (p : ℕ) :
    let T := logarithmicChartSystem (E := E) h p
    T.Admitted (fun _ => (1, 1)) T.homogeneousMinor :=
  diagonalChartSystem_admitted (E := E) h p p

/-- The collapse of a scalar tensor is the action of its coefficient
on the right form. -/
abbrev collapseLogarithmicTensor (p : ℕ) :
    F ⊗[k] ExteriorDifferentials k E p →ₗ[k] ExteriorDifferentials k E p :=
  tensorContraction (LinearMap.id : F →ₗ[F] F)

/-- A regular form on the union of the chart indices has a tensor
representative on the chart pair. Its collapsed value has the affine
volume factor required by the logarithmic lattice. -/
theorem IsPd.exists_logarithmicTensor_of_joinedForm (h : IsPd k x)
    {I J : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (hJ : J.Nonempty)
    {p : ℕ} (w : ExteriorDifferentials k E p)
    (hw : (w : DR k E) ∈ omB k E (rB k E x (I ∪ J)) p) :
    ∃ v ∈ (logarithmicChartSystem (E := E) h p).M I J,
      collapseLogarithmicTensor (k := k) (F := F) p v =
        (∏ l, x l / x i) • w := by
  obtain ⟨c, u, hc, hu, rfl⟩ := h.exists_regularScalar_smul_omB_of_union hJ w hw
  let a : F := ∏ l, x l / x i
  have ha : logCoefficientScale x i * a = 1 := by
    change (∏ l, x i / x l) * (∏ l, x l / x i) = 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun l _ => by rw [div_mul_div_cancel₀ (h.ne l), div_self (h.ne i)]
  have hac : a * c ∈ logCoefficientLattice k x I := by
    refine (h.mem_logCoefficientLattice_iff hi).mpr ?_
    rwa [← mul_assoc, ha, one_mul]
  refine ⟨(a * c) ⊗ₜ[k] u, Submodule.apply_mem_map₂ _ hac hu, ?_⟩
  rw [collapseLogarithmicTensor, tensorContraction_tmul, LinearMap.id_apply, mul_smul]

end GlobalTheory.PD
