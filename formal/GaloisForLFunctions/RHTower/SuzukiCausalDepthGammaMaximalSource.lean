import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaSourceRegularization
import GaloisForLFunctions.RHTower.SuzukiGammaJacobiTailCore

/-!
# The actual two-leg Gamma source has no extra maximal extension

The continuous cancelled row equations characterize exactly the graph closure
of the literal finite source packets. Radial boundary cancellation supplies
admissible approximants, and the Jacobi tail recurrence selects a sequence
converging in the full graph norm.
-/

open Filter Topology
open scoped BigOperators ENNReal InnerProduct
set_option autoImplicit false

noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

private abbrev H := SuzukiCausalDepthGammaTraceL2
private abbrev Index := SuzukiCausalDepthGammaTraceIndex

theorem suzukiGammaSourceEquationGraph_output_inl
    (h a : Set.Ioi (0 : ℝ)) {u v : H}
    (huv : (u, v) ∈ suzukiGammaSourceEquationGraph h a) (pe : Nat.Primes × ℕ) :
    v (Sum.inl pe) = 0 := by
  have he := (Submodule.mem_iInf _).mp huv (Sum.inl pe)
  simpa [suzukiGammaSourceGraphEquation, lp.evalCLM] using he

theorem suzukiGammaSourceEquationGraph_row
    (h a : Set.Ioi (0 : ℝ)) {u v : H}
    (huv : (u, v) ∈ suzukiGammaSourceEquationGraph h a) (k : ℕ) :
    (suzukiGammaBoundaryCoefficient (k + 1) : ℂ) * v (Sum.inr k) -
        (suzukiGammaBoundaryCoefficient k : ℂ) * v (Sum.inr (k + 1)) =
      inner ℂ (suzukiGammaBoundaryRowVector h a k) u := by
  have he := (Submodule.mem_iInf _).mp huv (Sum.inr k)
  simpa [suzukiGammaSourceGraphEquation, lp.evalCLM, sub_eq_zero] using he

private theorem boundaryCoefficient_ne_zero (k : ℕ) :
    (suzukiGammaBoundaryCoefficient k : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (suzukiGammaBoundaryCoefficient_pos k).ne'

theorem suzukiGammaBoundaryCorrectedRow_graph
    (h a : Set.Ioi (0 : ℝ)) {u v : H}
    (huv : (u, v) ∈ suzukiGammaSourceEquationGraph h a) (k : ℕ) :
    inner ℂ (suzukiGammaBoundaryCorrectedRow h a k) u =
      (suzukiGammaBoundaryCoefficient 0 : ℂ) * v (Sum.inr k) -
        (suzukiGammaBoundaryCoefficient k : ℂ) * v (Sum.inr 0) := by
  induction k with
  | zero => simp [suzukiGammaBoundaryCorrectedRow]
  | succ k ih =>
    rw [suzukiGammaBoundaryCorrectedRow, inner_sub_left, inner_smul_left, inner_smul_left]
    simp only [map_div₀, Complex.conj_ofReal]
    rw [ih, ← suzukiGammaSourceEquationGraph_row h a huv k]
    field_simp [boundaryCoefficient_ne_zero k]
    ring

private theorem correctedRow_feature_zero (h a : Set.Ioi (0 : ℝ)) (k l : ℕ) :
    suzukiGammaBoundaryCorrectedRow h a k (Sum.inr l) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [suzukiGammaBoundaryCorrectedRow, ih, suzukiGammaBoundaryRowVector]

private theorem correctedRow_single (h a : Set.Ioi (0 : ℝ)) (k : ℕ) (i : Index) :
    inner ℂ (suzukiGammaBoundaryCorrectedRow h a k) (lp.single 2 i (1 : ℂ)) =
      (suzukiGammaBoundaryCoefficient 0 : ℂ) *
          suzukiGammaTwoLegFullColumn h a i (Sum.inr k) -
        (suzukiGammaBoundaryCoefficient k : ℂ) *
          suzukiGammaTwoLegFullColumn h a i (Sum.inr 0) := by
  rw [lp.inner_single_right]
  cases i with
  | inl pe =>
    rw [suzukiGammaBoundaryCorrectedRow_coordinate]
    simp [RCLike.inner_apply, suzukiGammaTwoLegFullColumn,
      suzukiGammaTwoLegColumn_inr]
  | inr l =>
    rw [correctedRow_feature_zero]
    simp [suzukiGammaTwoLegFullColumn]

private theorem column_tail_shift (h a : Set.Ioi (0 : ℝ)) (k n : ℕ)
    (pe : Nat.Primes × ℕ) :
    (suzukiGammaBoundaryCoefficient (k + n + 1) : ℂ) *
        suzukiGammaTwoLegColumn h a pe (Sum.inr (k + 1)) *
        (suzukiGammaSourceRadius pe ^ n : ℝ) =
      (suzukiGammaBoundaryCoefficient (k + 1) : ℂ) *
        suzukiGammaTwoLegColumn h a pe (Sum.inr (k + n + 1)) := by
  rw [suzukiGammaTwoLegColumn_inr, suzukiGammaTwoLegColumn_inr]
  simp only [suzukiGammaBoundaryCoefficient, suzukiCausalDepthGammaWeightedFeature,
    suzukiCausalDepthGammaFeature, gammaConductorJacobiFeature,
    suzukiCausalDepthGammaSurvivingDegree, suzukiGammaSourceRadius]
  rw [show k + n + 3 = (k + 3) + n by omega, pow_add]
  push_cast
  ring

private theorem functional_eq_of_single
    (F G : H →L[ℂ] ℂ)
    (heq : ∀ i : Index, F (lp.single 2 i (1 : ℂ)) = G (lp.single 2 i (1 : ℂ))) :
    F = G := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro z
  change F (lp.single 2 i z) = G (lp.single 2 i z)
  have hs : (lp.single 2 i z : H) = z • lp.single 2 i (1 : ℂ) := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul, heq]

/-- The regularized output differs from any solution of the cancelled equations
by precisely its normalized Jacobi tail; no tail limit is assumed. -/
theorem suzukiGammaRegularizedSynthesis_tail_error
    (h a : Set.Ioi (0 : ℝ)) {u v : H}
    (huv : (u, v) ∈ suzukiGammaSourceEquationGraph h a) (k n : ℕ) :
    v (Sum.inr (k + 1)) - suzukiGammaRegularizedSynthesis h a n u (Sum.inr (k + 1)) =
      ((suzukiGammaBoundaryCoefficient (k + 1) : ℂ) /
        (suzukiGammaBoundaryCoefficient (k + n + 1) : ℂ)) * v (Sum.inr (k + n + 1)) := by
  let q : ℂ := (suzukiGammaBoundaryCoefficient (k + 1) : ℂ) /
    (suzukiGammaBoundaryCoefficient (k + n + 1) : ℂ)
  let F : H →L[ℂ] ℂ := (suzukiGammaBoundaryCoefficient 0 : ℂ) •
    (lp.evalCLM ℂ (fun _ : Index => ℂ) 2 (Sum.inr (k + 1))).comp
      (suzukiGammaRegularizedSynthesis h a n)
  let G : H →L[ℂ] ℂ := innerSL ℂ (suzukiGammaBoundaryCorrectedRow h a (k + 1)) -
    q • innerSL ℂ (suzukiGammaBoundaryCorrectedRow h a (k + n + 1))
  have hFG : F = G := by
    apply functional_eq_of_single
    intro i
    change (suzukiGammaBoundaryCoefficient 0 : ℂ) *
        suzukiGammaRegularizedSynthesis h a n (lp.single 2 i (1 : ℂ)) (Sum.inr (k + 1)) =
      inner ℂ (suzukiGammaBoundaryCorrectedRow h a (k + 1)) (lp.single 2 i (1 : ℂ)) -
        q * inner ℂ (suzukiGammaBoundaryCorrectedRow h a (k + n + 1)) (lp.single 2 i (1 : ℂ))
    rw [suzukiGammaRegularizedSynthesis_single, correctedRow_single, correctedRow_single]
    cases i with
    | inr l => simp [suzukiGammaTwoLegFullColumn]
    | inl pe =>
      have ht := column_tail_shift h a k n pe
      simp only [suzukiGammaSourcePowerSymbol, Sum.elim_inl,
        suzukiGammaTwoLegFullColumn, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      dsimp only [q]
      field_simp [boundaryCoefficient_ne_zero (k + n + 1)]
      linear_combination -(suzukiGammaBoundaryCoefficient 0 : ℂ) * ht
  have hval := congrArg (fun T : H →L[ℂ] ℂ => T u) hFG
  change (suzukiGammaBoundaryCoefficient 0 : ℂ) *
      suzukiGammaRegularizedSynthesis h a n u (Sum.inr (k + 1)) =
    inner ℂ (suzukiGammaBoundaryCorrectedRow h a (k + 1)) u -
      q * inner ℂ (suzukiGammaBoundaryCorrectedRow h a (k + n + 1)) u at hval
  rw [suzukiGammaBoundaryCorrectedRow_graph h a huv,
    suzukiGammaBoundaryCorrectedRow_graph h a huv] at hval
  dsimp only [q] at hval
  have hc0 := boundaryCoefficient_ne_zero 0
  have hcl := boundaryCoefficient_ne_zero (k + n + 1)
  field_simp [hcl] at hval ⊢
  apply (mul_left_cancel₀ hc0)
  linear_combination -hval

private theorem summable_feature_tail (v : H) :
    Summable (fun j : ℕ => ‖v (Sum.inr (j + 1))‖ ^ 2) := by
  apply (HilbertSchmidt.summable_coe_sq v).comp_injective
  intro j k hjk
  exact Nat.add_right_cancel (Sum.inr.inj hjk)

private theorem norm_sq_feature_split (v : H)
    (hv : ∀ pe : Nat.Primes × ℕ, v (Sum.inl pe) = 0) :
    ‖v‖ ^ 2 = ‖v (Sum.inr 0)‖ ^ 2 + ∑' j : ℕ, ‖v (Sum.inr (j + 1))‖ ^ 2 := by
  have hs := HilbertSchmidt.summable_coe_sq v
  have hr := hs.comp_injective Sum.inr_injective
  have hl : HasSum (fun pe : Nat.Primes × ℕ => ‖v (Sum.inl pe)‖ ^ 2) 0 := by
    simpa only [hv, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      (hasSum_zero : HasSum (fun _ : Nat.Primes × ℕ => (0 : ℝ)) 0)
  have he := (hl.sum hr.hasSum).tsum_eq
  rw [HilbertSchmidt.lp_norm_sq_eq, he, zero_add]
  exact hr.tsum_eq_zero_add

/-- Exact full output error: one continuously controlled boundary coordinate
plus the Jacobi tail energy of the original output. -/
theorem suzukiGammaRegularizedSynthesis_error_norm_sq
    (h a : Set.Ioi (0 : ℝ)) {u v : H}
    (huv : (u, v) ∈ suzukiGammaSourceEquationGraph h a) (n : ℕ) :
    ‖v - suzukiGammaRegularizedSynthesis h a n u‖ ^ 2 =
      ‖v (Sum.inr 0) - suzukiGammaRegularizedSynthesis h a n u (Sum.inr 0)‖ ^ 2 +
        suzukiGammaJacobiTailEnergy (fun j => ‖v (Sum.inr (j + 1))‖ ^ 2) n := by
  have hreg := suzukiGammaTwoLegClosedGraph_le_equationGraph h a
    (suzukiGammaRegularizedSynthesis_mem_closedGraph h a n u)
  have hleft : ∀ pe, (v - suzukiGammaRegularizedSynthesis h a n u) (Sum.inl pe) = 0 := by
    intro pe
    change v (Sum.inl pe) - suzukiGammaRegularizedSynthesis h a n u (Sum.inl pe) = 0
    rw [suzukiGammaSourceEquationGraph_output_inl h a huv,
      suzukiGammaSourceEquationGraph_output_inl h a hreg, sub_self]
  rw [norm_sq_feature_split _ hleft]
  congr 1
  let b : ℕ → ℝ := fun j => ‖v (Sum.inr (j + 1))‖ ^ 2
  have hs := summable_suzukiGammaJacobiTailWeight_mul (summable_feature_tail v)
    (fun j => sq_nonneg _) n
  have he := hs.sum_add_tsum_nat_add n
  have hhead : (∑ j ∈ Finset.range n, suzukiGammaJacobiTailWeight n j * b j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [suzukiGammaJacobiTailWeight, not_le.mpr (Finset.mem_range.mp hj)]
  change (∑ j ∈ Finset.range n, suzukiGammaJacobiTailWeight n j * b j) +
      (∑' j, suzukiGammaJacobiTailWeight n (j + n) * b (j + n)) =
        suzukiGammaJacobiTailEnergy b n at he
  rw [hhead, zero_add] at he
  rw [← he]
  apply tsum_congr
  intro j
  change ‖v (Sum.inr (j + 1)) -
      suzukiGammaRegularizedSynthesis h a n u (Sum.inr (j + 1))‖ ^ 2 = _
  rw [suzukiGammaRegularizedSynthesis_tail_error h a huv]
  rw [norm_mul, norm_div, mul_pow, div_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  simp only [suzukiGammaJacobiTailWeight, Nat.le_add_left, ↓reduceIte,
    Nat.add_sub_cancel_right, b, suzukiGammaBoundaryCoefficient,
    suzukiCausalDepthGammaSurvivingDegree,
    semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom]

private theorem tendsto_zero_of_norm_sq
    {E : Type*} [NormedAddCommGroup E] (f : ℕ → E)
    (hf : Tendsto (fun n => ‖f n‖ ^ 2) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hf
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

/-- A vanishing Jacobi tail energy suffices for convergence of the entire
regularized output, including the exceptional first boundary coordinate. -/
theorem tendsto_suzukiGammaRegularizedSynthesis_of_tailEnergy
    (h a : Set.Ioi (0 : ℝ)) {u v : H}
    (huv : (u, v) ∈ suzukiGammaSourceEquationGraph h a)
    {ν : ℕ → ℕ} (hνtop : Tendsto ν atTop atTop)
    (hE : Tendsto (fun N => suzukiGammaJacobiTailEnergy
      (fun j => ‖v (Sum.inr (j + 1))‖ ^ 2) (ν N)) atTop (𝓝 0)) :
    Tendsto (fun N => suzukiGammaRegularizedSynthesis h a (ν N) u) atTop (𝓝 v) := by
  let b : ℕ → ℝ := fun j => ‖v (Sum.inr (j + 1))‖ ^ 2
  have hu := (tendsto_suzukiGammaSourceRegularization u).comp hνtop
  let e : ℕ → H := fun N => v - suzukiGammaRegularizedSynthesis h a (ν N) u
  have herr (N : ℕ) :
      (u - suzukiGammaSourceRegularization (ν N) u, e N) ∈
        suzukiGammaSourceEquationGraph h a := by
    exact (suzukiGammaSourceEquationGraph h a).sub_mem huv
      (suzukiGammaTwoLegClosedGraph_le_equationGraph h a
        (suzukiGammaRegularizedSynthesis_mem_closedGraph h a (ν N) u))
  have hsplit (N : ℕ) : ‖e N‖ ^ 2 = ‖e N (Sum.inr 0)‖ ^ 2 +
      suzukiGammaJacobiTailEnergy b (ν N) :=
    suzukiGammaRegularizedSynthesis_error_norm_sq h a huv (ν N)
  have htail (N : ℕ) : (∑' j, ‖e N (Sum.inr (j + 1))‖ ^ 2) =
      suzukiGammaJacobiTailEnergy b (ν N) := by
    have hn := norm_sq_feature_split (e N)
      (suzukiGammaSourceEquationGraph_output_inl h a (herr N))
    linarith [hsplit N]
  have he1sq : Tendsto (fun N => ‖e N (Sum.inr 1)‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => sq_nonneg _) _ hE
    intro N
    rw [← htail N]
    exact (summable_feature_tail (e N)).le_tsum 0 (fun j _ => sq_nonneg _)
  have he1 := tendsto_zero_of_norm_sq (fun N => e N (Sum.inr 1)) he1sq
  have hinner : Tendsto (fun N => inner ℂ (suzukiGammaBoundaryRowVector h a 0)
      (u - suzukiGammaSourceRegularization (ν N) u)) atTop (𝓝 0) := by
    have hd : Tendsto (fun N => u - suzukiGammaSourceRegularization (ν N) u)
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, sub_self] using (tendsto_const_nhds (x := u)).sub hu
    have hi := (innerSL ℂ (suzukiGammaBoundaryRowVector h a 0)).continuous.tendsto 0
    simpa only [Function.comp_def, sub_self, map_zero, innerSL_apply_apply] using hi.comp hd
  have he0 : Tendsto (fun N => e N (Sum.inr 0)) atTop (𝓝 0) := by
    have ht := (hinner.add (he1.const_mul (suzukiGammaBoundaryCoefficient 0 : ℂ))).div_const
      (suzukiGammaBoundaryCoefficient 1 : ℂ)
    simp only [mul_zero, add_zero, zero_div] at ht
    apply ht.congr'
    filter_upwards with N
    have hr := suzukiGammaSourceEquationGraph_row h a (herr N) 0
    apply (div_eq_iff (boundaryCoefficient_ne_zero 1)).2
    linear_combination -hr
  have hesq : Tendsto (fun N => ‖e N‖ ^ 2) atTop (𝓝 0) := by
    change Tendsto (fun N => suzukiGammaJacobiTailEnergy b (ν N)) atTop (𝓝 0) at hE
    have ht := he0.norm.pow 2 |>.add hE
    simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_add, ← hsplit] using ht
  have he := tendsto_zero_of_norm_sq e hesq
  have ht := (tendsto_const_nhds (x := v)).sub he
  simpa only [e, sub_sub_cancel, sub_zero] using ht

/-- Every square-summable solution of the actual cancellation equations is
approximated in graph norm by the explicitly regularized original source. -/
theorem suzukiGammaSourceEquationGraph_regularized_approximation
    (h a : Set.Ioi (0 : ℝ)) {u v : H}
    (huv : (u, v) ∈ suzukiGammaSourceEquationGraph h a) :
    ∃ ν : ℕ → ℕ, (∀ N, N ≤ ν N) ∧
      Tendsto (fun N => suzukiGammaSourceRegularization (ν N) u) atTop (𝓝 u) ∧
      Tendsto (fun N => suzukiGammaRegularizedSynthesis h a (ν N) u) atTop (𝓝 v) := by
  let b : ℕ → ℝ := fun j => ‖v (Sum.inr (j + 1))‖ ^ 2
  have hb : Summable b := summable_feature_tail v
  have hb0 : ∀ j, 0 ≤ b j := fun j => sq_nonneg _
  have hex (N : ℕ) : ∃ n ≥ N, suzukiGammaJacobiTailEnergy b n < 1 / ((N : ℝ) + 1) :=
    exists_suzukiGammaJacobiTailEnergy_lt hb hb0 N (by positivity)
  choose ν hν hsmall using hex
  have hνtop : Tendsto ν atTop atTop := tendsto_atTop_mono hν tendsto_id
  have hE : Tendsto (fun N => suzukiGammaJacobiTailEnergy b (ν N)) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => suzukiGammaJacobiTailEnergy_nonneg hb0 (ν N))
      (fun N => (hsmall N).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨ν, hν, (tendsto_suzukiGammaSourceRegularization u).comp hνtop,
    tendsto_suzukiGammaRegularizedSynthesis_of_tailEnergy h a huv hνtop hE⟩

/-- **Minimal equals maximal for the literal two-leg Suzuki Gamma source.**
The continuous cancellation equations impose exactly the finite-packet graph
closure. No source-domain or approximation hypothesis is left open. -/
theorem suzukiGammaTwoLegClosedGraph_eq_equationGraph
    (h a : Set.Ioi (0 : ℝ)) :
    suzukiGammaTwoLegClosedGraph h a = suzukiGammaSourceEquationGraph h a := by
  apply le_antisymm (suzukiGammaTwoLegClosedGraph_le_equationGraph h a)
  rintro ⟨u, v⟩ huv
  obtain ⟨ν, _, hu, hv⟩ :=
    suzukiGammaSourceEquationGraph_regularized_approximation h a huv
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (hu.prodMk_nhds hv)
  exact Filter.Eventually.of_forall fun N =>
    suzukiGammaRegularizedSynthesis_mem_closedGraph h a (ν N) u

/-- The canonical closed synthesis is characterized by the literal cancelled
equations for every input/output pair. -/
theorem suzukiGammaTwoLegClosedSynthesis_graph_eq_equationGraph
    (h a : Set.Ioi (0 : ℝ)) :
    (suzukiGammaTwoLegClosedSynthesis h a).graph = suzukiGammaSourceEquationGraph h a := by
  rw [suzukiGammaTwoLegClosedSynthesis_graph, suzukiGammaTwoLegClosedGraph_eq_equationGraph]

end RHTower
