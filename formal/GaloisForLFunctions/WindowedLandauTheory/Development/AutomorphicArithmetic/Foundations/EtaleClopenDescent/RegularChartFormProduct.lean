import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GenericChartForms
import GaloisForLFunctions.HTGeometry.ExteriorGradedMul

/-! Regular chart forms are homogeneous and closed under exterior product. -/

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k E : Type} [Field k] [Field E] [Algebra k E]
  {B : Subalgebra k E} {p q : ℕ}

/-- Regular forms of exterior degree `p` lie in the degree-`p` summand. -/
theorem omB_le_degree : omB k E B p ≤ (⋀[E]^p Ω[E⁄k]).restrictScalars k := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨b, -, v, -, rfl⟩
  change b • ExteriorAlgebra.ιMulti E p (fun i => D k E (v i)) ∈ ⋀[E]^p Ω[E⁄k]
  apply Submodule.smul_mem
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
  exact Submodule.subset_span ⟨_, rfl⟩

/-- The product of two regular forms stays regular on the chart. -/
theorem mul_mem_omB {a b : DR k E} (ha : a ∈ omB k E B p) (hb : b ∈ omB k E B q) :
    a * b ∈ omB k E B (p + q) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, v, hv, rfl⟩ := hx
      obtain ⟨c', hc', w, hw, rfl⟩ := hy
      have happ : Fin.append (fun i => D k E (v i)) (fun i => D k E (w i)) =
          fun i => D k E (Fin.append v w i) := by
        funext i
        exact Fin.addCases (fun j => by simp) (fun j => by simp) i
      refine Submodule.subset_span ⟨c * c', B.mul_mem hc hc', Fin.append v w, fun i => ?_, ?_⟩
      · exact Fin.addCases (fun j => by simpa only [Fin.append_left] using hv j)
          (fun j => by simpa only [Fin.append_right] using hw j) i
      · rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_mul_ιMulti, happ]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

/-- Multiplication by a regular function preserves regular forms. -/
theorem smul_mem_omB {c : E} (hc : c ∈ B) {a : DR k E} (ha : a ∈ omB k E B p) :
    c • a ∈ omB k E B p := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hx
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_comm c r x]; exact Submodule.smul_mem _ r hx

end GlobalTheory.PD
