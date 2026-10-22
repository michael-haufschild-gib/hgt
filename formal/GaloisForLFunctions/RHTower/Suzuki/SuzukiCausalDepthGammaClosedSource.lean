import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaBoundaryCancellation
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Closed synthesis of the exact two-leg Suzuki Gamma source

The graph closure of finite, prime-deattenuated source packets is an operator,
not a multivalued relation. Adjacent Gamma-coordinate cancellation gives closed
row equations containing every finite packet; their vertical kernel vanishes.
Thus amplitude non-summability does not obstruct this non-diagonal closed
realization. All finite columns, and hence all finite Gram pairings, are retained.
-/

open Filter Topology
open scoped BigOperators ENNReal InnerProduct
set_option autoImplicit false

noncomputable section

namespace RHTower

private abbrev GammaH := SuzukiCausalDepthGammaTraceL2
private abbrev GammaIndex := SuzukiCausalDepthGammaTraceIndex

/-- The cancelled row is a Hilbert vector although the uncancelled row need not be. -/
def suzukiGammaBoundaryRowVector
    (h a : Set.Ioi (0 : ℝ)) (k : ℕ) : GammaH := by
  refine ⟨Sum.elim (fun pe => (suzukiGammaBoundaryRow h.1 a.1 k pe : ℂ))
    (fun _ => 0), memℓp_gen ?_⟩
  have hs : Summable (fun pe : Nat.Primes × ℕ =>
      ‖(suzukiGammaBoundaryRow h.1 a.1 k pe : ℂ)‖ ^ (2 : ENNReal).toReal) := by
    simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      summable_sq_suzukiGammaBoundaryRow h a k
  refine Summable.sum _ ?_ ?_
  · exact hs
  · simpa [Function.comp_def] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

/-- Each equation is continuous on source times output. -/
def suzukiGammaSourceGraphEquation
    (h a : Set.Ioi (0 : ℝ)) (i : GammaIndex) :
    (GammaH × GammaH) →L[ℂ] ℂ :=
  match i with
  | Sum.inl pe =>
      (lp.evalCLM ℂ (fun _ : GammaIndex => ℂ) 2 (Sum.inl pe)).comp
        (ContinuousLinearMap.snd ℂ GammaH GammaH)
  | Sum.inr k =>
      (suzukiGammaBoundaryCoefficient (k + 1) : ℂ) •
          (lp.evalCLM ℂ (fun _ : GammaIndex => ℂ) 2 (Sum.inr k)).comp
            (ContinuousLinearMap.snd ℂ GammaH GammaH) -
        (suzukiGammaBoundaryCoefficient k : ℂ) •
          (lp.evalCLM ℂ (fun _ : GammaIndex => ℂ) 2 (Sum.inr (k + 1))).comp
            (ContinuousLinearMap.snd ℂ GammaH GammaH) -
        (innerSL ℂ (suzukiGammaBoundaryRowVector h a k)).comp
          (ContinuousLinearMap.fst ℂ GammaH GammaH)

/-- Closed row-equation relation for the deattenuated source. -/
def suzukiGammaSourceEquationGraph
    (h a : Set.Ioi (0 : ℝ)) : Submodule ℂ (GammaH × GammaH) :=
  ⨅ i : GammaIndex, (suzukiGammaSourceGraphEquation h a i).ker

theorem suzukiGammaSourceEquationGraph_isClosed (h a : Set.Ioi (0 : ℝ)) :
    IsClosed (suzukiGammaSourceEquationGraph h a : Set (GammaH × GammaH)) := by
  simp only [suzukiGammaSourceEquationGraph, Submodule.coe_iInf]
  exact isClosed_iInter fun i => (suzukiGammaSourceGraphEquation h a i).isClosed_ker

private theorem gammaBoundary_recurrence_zero (v : GammaH)
    (hvLeft : ∀ pe, v (Sum.inl pe) = 0)
    (hv : ∀ k,
      (suzukiGammaBoundaryCoefficient (k + 1) : ℂ) * v (Sum.inr k) =
        (suzukiGammaBoundaryCoefficient k : ℂ) * v (Sum.inr (k + 1))) :
    v = 0 := by
  let z : ℂ := v (Sum.inr 0) / (suzukiGammaBoundaryCoefficient 0 : ℂ)
  have hc (k : ℕ) : (suzukiGammaBoundaryCoefficient k : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (suzukiGammaBoundaryCoefficient_pos k).ne'
  have hcoord (k : ℕ) :
      v (Sum.inr k) = z * (suzukiGammaBoundaryCoefficient k : ℂ) := by
    induction k with
    | zero => simp [z, hc]
    | succ k ih =>
      apply (mul_left_cancel₀ (hc k))
      rw [← hv k, ih]
      ring
  have hz : z = 0 := by
    by_contra hz
    have hs : Summable (fun k : ℕ => ‖v (Sum.inr k)‖ ^ 2) := by
      exact (HilbertSchmidt.summable_coe_sq v).comp_injective
        Sum.inr_injective
    have hscaled : Summable (fun k : ℕ =>
        ‖z‖ ^ 2 * suzukiGammaBoundaryCoefficient k ^ 2) := by
      refine hs.congr fun k => ?_
      rw [hcoord k, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact not_summable_sq_suzukiGammaBoundaryCoefficient
      ((summable_mul_left_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))).mp hscaled)
  apply lp.ext
  funext i
  cases i with
  | inl pe => simpa using hvLeft pe
  | inr k => simpa [hz] using hcoord k

/-- The closed relation has no vertical ambiguity. -/
theorem suzukiGammaSourceEquationGraph_vertical_zero
    (h a : Set.Ioi (0 : ℝ)) (x : GammaH × GammaH)
    (hx : x ∈ suzukiGammaSourceEquationGraph h a) (hx0 : x.1 = 0) :
    x.2 = 0 := by
  have heq (i : GammaIndex) : suzukiGammaSourceGraphEquation h a i x = 0 :=
    ((Submodule.mem_iInf _).mp hx i)
  apply gammaBoundary_recurrence_zero x.2
  · intro pe
    simpa [suzukiGammaSourceGraphEquation, lp.evalCLM] using heq (Sum.inl pe)
  · intro k
    have hk := heq (Sum.inr k)
    simpa [suzukiGammaSourceGraphEquation, lp.evalCLM, hx0, sub_eq_zero] using hk

/-- Column family on the complete source index; unused feature inputs have zero image. -/
def suzukiGammaTwoLegFullColumn (h a : Set.Ioi (0 : ℝ)) :
    GammaIndex → GammaH :=
  Sum.elim (suzukiGammaTwoLegColumn h a) (fun _ => 0)

theorem suzukiGammaTwoLegFullColumn_mem_equationGraph
    (h a : Set.Ioi (0 : ℝ)) (i : GammaIndex) :
    (lp.single 2 i (1 : ℂ), suzukiGammaTwoLegFullColumn h a i) ∈
      suzukiGammaSourceEquationGraph h a := by
  apply (Submodule.mem_iInf _).mpr
  intro j
  change suzukiGammaSourceGraphEquation h a j
    (lp.single 2 i (1 : ℂ), suzukiGammaTwoLegFullColumn h a i) = 0
  cases j with
  | inl qe =>
    cases i <;> simp [suzukiGammaSourceGraphEquation, lp.evalCLM, suzukiGammaTwoLegFullColumn,
      suzukiGammaTwoLegColumn_inl]
  | inr k =>
    cases i with
    | inl pe =>
      change (suzukiGammaBoundaryCoefficient (k + 1) : ℂ) *
          suzukiGammaTwoLegColumn h a pe (Sum.inr k) -
        (suzukiGammaBoundaryCoefficient k : ℂ) *
          suzukiGammaTwoLegColumn h a pe (Sum.inr (k + 1)) -
        inner ℂ (suzukiGammaBoundaryRowVector h a k)
          (lp.single 2 (Sum.inl pe) (1 : ℂ)) = 0
      rw [lp.inner_single_right]
      rw [suzukiGammaTwoLegColumn_inr, suzukiGammaTwoLegColumn_inr]
      simp only [suzukiGammaBoundaryRowVector, Sum.elim_inl, RCLike.inner_apply,
        Complex.conj_ofReal, mul_one, smul_eq_mul]
      push_cast
      unfold suzukiGammaBoundaryRow
      push_cast
      ring
    | inr l =>
      simp [suzukiGammaSourceGraphEquation, lp.evalCLM, suzukiGammaTwoLegFullColumn,
        lp.inner_single_right, suzukiGammaBoundaryRowVector]

/-- Graph closure of all literal finite source packets. -/
def suzukiGammaTwoLegClosedGraph
    (h a : Set.Ioi (0 : ℝ)) : Submodule ℂ (GammaH × GammaH) :=
  (Submodule.span ℂ (Set.range fun i : GammaIndex =>
    (lp.single 2 i (1 : ℂ), suzukiGammaTwoLegFullColumn h a i))).topologicalClosure

theorem suzukiGammaTwoLegClosedGraph_le_equationGraph
    (h a : Set.Ioi (0 : ℝ)) :
    suzukiGammaTwoLegClosedGraph h a ≤ suzukiGammaSourceEquationGraph h a := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact suzukiGammaTwoLegFullColumn_mem_equationGraph h a i
  · exact suzukiGammaSourceEquationGraph_isClosed h a

/-- Canonical minimal closed synthesis, with the finite packets as a graph core. -/
def suzukiGammaTwoLegClosedSynthesis (h a : Set.Ioi (0 : ℝ)) :
    GammaH →ₗ.[ℂ] GammaH :=
  (suzukiGammaTwoLegClosedGraph h a).toLinearPMap

theorem suzukiGammaTwoLegClosedSynthesis_graph (h a : Set.Ioi (0 : ℝ)) :
    (suzukiGammaTwoLegClosedSynthesis h a).graph = suzukiGammaTwoLegClosedGraph h a := by
  apply Submodule.toLinearPMap_graph_eq
  intro x hx hx0
  exact suzukiGammaSourceEquationGraph_vertical_zero h a x
    (suzukiGammaTwoLegClosedGraph_le_equationGraph h a hx) hx0

/-- Premise-free closedness of the actual deattenuated source synthesis. -/
theorem suzukiGammaTwoLegClosedSynthesis_isClosed (h a : Set.Ioi (0 : ℝ)) :
    (suzukiGammaTwoLegClosedSynthesis h a).IsClosed := by
  rw [LinearPMap.IsClosed, suzukiGammaTwoLegClosedSynthesis_graph]
  exact Submodule.isClosed_topologicalClosure _

theorem suzukiGammaTwoLegClosedSynthesis_single_graph
    (h a : Set.Ioi (0 : ℝ)) (i : GammaIndex) :
    (lp.single 2 i (1 : ℂ), suzukiGammaTwoLegFullColumn h a i) ∈
      (suzukiGammaTwoLegClosedSynthesis h a).graph := by
  rw [suzukiGammaTwoLegClosedSynthesis_graph]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)

/-- No coefficient-space direction is excluded at the level of density. -/
theorem suzukiGammaTwoLegClosedSynthesis_dense_domain (h a : Set.Ioi (0 : ℝ)) :
    Dense ((suzukiGammaTwoLegClosedSynthesis h a).domain : Set GammaH) := by
  intro v
  have hs := lp.hasSum_single (E := fun _ : GammaIndex => ℂ)
    (p := (2 : ENNReal)) (by norm_num) v
  apply mem_closure_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i _
  have hi : lp.single 2 i (1 : ℂ) ∈
      (suzukiGammaTwoLegClosedSynthesis h a).domain :=
    LinearPMap.mem_domain_iff.mpr
      ⟨_, suzukiGammaTwoLegClosedSynthesis_single_graph h a i⟩
  have hv := (suzukiGammaTwoLegClosedSynthesis h a).domain.smul_mem (v i) hi
  simpa [← lp.single_smul] using hv

/-- Every finite complex packet is recovered with its original source coefficients. -/
theorem suzukiGammaTwoLegClosedSynthesis_finite_packet
    (h a : Set.Ioi (0 : ℝ)) (s : Finset (Nat.Primes × ℕ))
    (c : (Nat.Primes × ℕ) → ℂ) :
    ((∑ pe ∈ s, c pe • lp.single 2 (Sum.inl pe) (1 : ℂ)),
      ∑ pe ∈ s, c pe • suzukiGammaTwoLegColumn h a pe) ∈
        (suzukiGammaTwoLegClosedSynthesis h a).graph := by
  have hm : ∀ pe ∈ s,
      c pe • (lp.single 2 (Sum.inl pe) (1 : ℂ), suzukiGammaTwoLegColumn h a pe) ∈
        (suzukiGammaTwoLegClosedSynthesis h a).graph := by
    intro pe _
    exact Submodule.smul_mem _ _ (suzukiGammaTwoLegClosedSynthesis_single_graph h a (Sum.inl pe))
  simpa only [Prod.smul_mk, ← prod_mk_sum] using
    (Submodule.sum_mem _ hm)

/-- The closure preserves the exact deattenuated Gamma Gram kernel. -/
theorem suzukiGammaTwoLegColumn_inner
    (h a : Set.Ioi (0 : ℝ)) (x y : Nat.Primes × ℕ) :
    inner ℂ (suzukiGammaTwoLegColumn h a x) (suzukiGammaTwoLegColumn h a y) =
      ((x.1 : ℝ) * (y.1 : ℝ) * suzukiCausalDepthGammaSchurKernel h.1 a.1 x y : ℝ) := by
  let A := suzukiCausalDepthGammaFeatureOperator h.1 a.1 h.2 a.2
  have hbase : inner ℂ (A (lp.single 2 (Sum.inl x) (1 : ℂ)))
      (A (lp.single 2 (Sum.inl y) (1 : ℂ))) =
        (suzukiCausalDepthGammaSchurKernel h.1 a.1 x y : ℂ) := by
    have hm := suzukiCausalDepthGammaEnergyOperator_sourceBlock h.1 a.1 h.2 a.2 x y
    change (A.adjoint (A (lp.single 2 (Sum.inl y) (1 : ℂ)))) (Sum.inl x) = _ at hm
    rw [← ContinuousLinearMap.adjoint_inner_right, lp.inner_single_left]
    simpa [RCLike.inner_apply] using hm
  change inner ℂ ((x.1 : ℂ) • A (lp.single 2 (Sum.inl x) (1 : ℂ)))
      ((y.1 : ℂ) • A (lp.single 2 (Sum.inl y) (1 : ℂ))) = _
  rw [inner_smul_left, inner_smul_right, hbase]
  simp [mul_assoc]

end RHTower
