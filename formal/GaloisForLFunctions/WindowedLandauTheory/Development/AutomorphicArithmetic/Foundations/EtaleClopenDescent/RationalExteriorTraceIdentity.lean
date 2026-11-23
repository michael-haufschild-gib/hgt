import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalExteriorTrace

/-! Trace of a coefficient times an extended rational form is the field trace
of the coefficient times the original form. -/

noncomputable section

open GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.CechDR

variable {k E L : Type*} [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra k L] [Algebra E L] [IsScalarTower k E L]
  [Module.Finite E L] [Algebra.Etale E L]

/-- The projection formula for the trace on the entire exterior algebra. -/
theorem traceDR_smul_pullback (b : L) (ω : DR k E) :
    traceDR k E L (b • pullbackDR (IsScalarTower.toAlgHom k E L) ω) =
      Algebra.trace E L b • ω := by
  let f := IsScalarTower.toAlgHom k E L
  refine DirectSum.Decomposition.inductionOn (fun p => ⋀[E]^p Ω[E⁄k]) ?_ ?_ ?_ ω
  · simp only [map_zero, smul_zero]
  · intro p x
    rw [pullbackDR_degree]
    change traceDR k E L (↑(b • ExteriorDifferentials.map f p x : ExteriorDifferentials k L p)) = _
    rw [traceDR_degree, ← algebraFormPullback_eq_map k E L f rfl, finiteEtaleFormTrace_smul_pullback]
    change finiteEtaleAlgebraTrace E L b • (x : DR k E) = Algebra.trace E L b • (x : DR k E)
    exact congrArg (· • (x : DR k E)) (projectiveAlgebraTrace_eq_trace b)
  · intro x y hx hy
    simp only [map_add, smul_add, hx, hy]


/-- Trace of an exterior product with a pulled-back form equals the
product of the trace with the original form. -/
theorem traceDR_mul_pullback (v : DR k L) (w : DR k E) :
    traceDR k E L (v * pullbackDR (IsScalarTower.toAlgHom k E L) w) =
      traceDR k E L v * w := by
  let f := IsScalarTower.toAlgHom k E L
  refine DirectSum.Decomposition.inductionOn (fun q => ⋀[L]^q Ω[L⁄k]) ?_ ?_ ?_ v
  · simp only [zero_mul, map_zero]
  · intro q ω
    let h := algebraFormPullback_isBaseChange k E L q
    obtain ⟨u, rfl⟩ := h.equiv.surjective ω
    induction u using TensorProduct.induction_on with
    | zero => simp only [map_zero, Submodule.coe_zero, zero_mul]
    | tmul b a =>
      rw [h.equiv_tmul, algebraFormPullback_eq_map k E L f rfl,
        Submodule.coe_smul_of_tower, ← pullbackDR_degree, smul_mul_assoc,
        ← map_mul, traceDR_smul_pullback, traceDR_smul_pullback, smul_mul_assoc]
    | add x y hx hy => simp only [map_add, Submodule.coe_add, add_mul, hx, hy]
  · intro x y hx hy
    simp only [add_mul, map_add, hx, hy]

/-- Trace also satisfies the projection formula for a pulled-back
factor on the left. -/
theorem traceDR_pullback_mul (w : DR k E) (v : DR k L) :
    traceDR k E L (pullbackDR (IsScalarTower.toAlgHom k E L) w * v) =
      w * traceDR k E L v := by
  let f := IsScalarTower.toAlgHom k E L
  refine DirectSum.Decomposition.inductionOn (fun q => ⋀[L]^q Ω[L⁄k]) ?_ ?_ ?_ v
  · simp only [mul_zero, map_zero]
  · intro q ω
    let h := algebraFormPullback_isBaseChange k E L q
    obtain ⟨u, rfl⟩ := h.equiv.surjective ω
    induction u using TensorProduct.induction_on with
    | zero => simp only [map_zero, Submodule.coe_zero, mul_zero]
    | tmul b a =>
      rw [h.equiv_tmul, algebraFormPullback_eq_map k E L f rfl,
        Submodule.coe_smul_of_tower, ← pullbackDR_degree, mul_smul_comm,
        ← map_mul, traceDR_smul_pullback, traceDR_smul_pullback, mul_smul_comm]
    | add x y hx hy => simp only [map_add, Submodule.coe_add, mul_add, hx, hy]
  · intro x y hx hy
    simp only [mul_add, map_add, hx, hy]

end GlobalTheory.CechDR
