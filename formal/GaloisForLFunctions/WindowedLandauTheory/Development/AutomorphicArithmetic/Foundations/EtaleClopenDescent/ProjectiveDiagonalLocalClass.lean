import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ChartMinorNormalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SpecializedChartMinors
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveIdentityOnChartPairs

/-! The diagonal determinants decorate the regular chart tensors.
After trace contraction, the resulting column is independent of
the two charts. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p q : ℕ}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "π" => (Algebra.TensorProduct.lmul' k : F ⊗[k] F →ₐ[k] F)

variable (h : IsPd k x)

local notation "T₀" => diagonalChartSystem (E := E) h q p

omit [CharZero k] in
/-- The determinant column scale is a scalar in the left factor. -/
theorem chartVolume_inv_tensor (i : Fin (d + 1)) :
    ((T₀).minorColumnScale i : F ⊗[k] F) = (∏ l, x i / x l) ⊗ₜ[k] (1 : F) := by
  let f := Algebra.TensorProduct.includeLeftRingHom (R := k) (A := F) (B := F)
  change ((T₀).minorColumnScale i : F ⊗[k] F) = f (∏ l, x i / x l)
  rw [minorColumnScale, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  change (((T₀).X i * ((T₀).X l)⁻¹ : (F ⊗[k] F)ˣ) : F ⊗[k] F) =
    (x i / x l) ⊗ₜ[k] (1 : F)
  rw [Units.val_mul, show ((T₀).X i : F ⊗[k] F) = x i ⊗ₜ[k] (1 : F) from rfl,
    show ((((T₀).X l)⁻¹ : (F ⊗[k] F)ˣ) : F ⊗[k] F) = (x l)⁻¹ ⊗ₜ[k] (1 : F) from rfl,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, div_eq_mul_inv]

omit [CharZero k] in
/-- On the diagonal, the column scale is the inverse of the affine volume. -/
theorem chartVolume_inv_diagonal (i : Fin (d + 1)) :
    π ((T₀).minorColumnScale i : F ⊗[k] F) = ∏ l, x i / x l := by
  rw [chartVolume_inv_tensor (E := E) (p := p) (q := q) h i,
    Algebra.TensorProduct.lmul'_apply_tmul, mul_one]

omit [CharZero k] in
/-- The homogeneous diagonal minors vanish under scalar multiplication
of the two coordinate factors. -/
theorem diagonalMinor_specializes (l : DiagonalIndex d) : π ((T₀).homogeneousMinor l) = 0 := by
  let a := (ofLex l).1
  let b := (ofLex l).2
  change π ((x a ⊗ₜ[k] (1 : F)) * ((1 : F) ⊗ₜ[k] x b) -
    (x b ⊗ₜ[k] (1 : F)) * ((1 : F) ⊗ₜ[k] x a)) = 0
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, mul_one, one_mul, one_mul, map_sub,
    Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
    mul_comm (x b), sub_self]

/-- A local regular diagonal column contracts to the diagonal
specialization of the corresponding determinant times the identity. -/
theorem IsFinCover.exists_diagonalColumn (H : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d)
    (i j : Fin (d + 1)) :
    let T := diagonalChartSystem (E := E) H.pd q p
    ∃ c ∈ (T.columnComplex (fun _ => (1, 1)) T.homogeneousMinor {i} {j}).Z (d : ℤ),
      ∀ L (a : ExteriorDifferentials k E p),
        tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) (c L) =
          π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) • a := by
  let T := diagonalChartSystem (E := E) H.pd q p
  obtain ⟨v, hv, hvId⟩ := H.exists_chartPairIdentityTensor τ hτ hpq i j
  refine ⟨T.chartMinorColumn i v, T.chartMinorColumn_mem_cycles
    (diagonalChartSystem_good (E := E) H.pd q p) (Finset.mem_singleton_self i)
    (Finset.mem_singleton_self j) hv, ?_⟩
  intro L a
  have hprod : (∏ l, x i / x l) * (∏ l, x l / x i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun l _ => by
      rw [div_mul_div_cancel₀ (H.pd.ne l), div_self (H.pd.ne i)]
  change tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a)
    (tensorScalarAction (orderedMinor T.minorRows (uni {i} L))
      (tensorScalarAction (T.minorColumnScale i : F ⊗[k] F) v)) = _
  rw [tensorContraction_action, tensorContraction_action, hvId,
    chartVolume_inv_diagonal (E := E) (p := p) (q := q) H.pd i,
    smul_smul (∏ l, x i / x l), hprod, one_smul]
  rw [T.map_orderedMinor_singleton_eq π
    (diagonalMinor_specializes (E := E) (p := p) (q := q) H.pd) L i 0]

end GlobalTheory.PD
