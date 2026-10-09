import GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTraceClass
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# Exact traces for the balanced companion matrices

The trace-class realization turns the diagonal geometric series of
arXiv:2609.24149, Section 8, into an ordinary operator trace. The finite
zero extensions retain an explicit finite-size correction to that trace.
-/

noncomputable section
open Filter RHTower
open scoped Topology

namespace HTGeometry

local notation "H" => lp (fun _ : ℕ => ℂ) 2

private def e (n : ℕ) : H := lp.single 2 n (1 : ℂ)

private theorem e_norm (n : ℕ) : ‖e n‖ = 1 := by
  rw [e, lp.norm_single (by norm_num), norm_one]

private theorem e_inner (i j : ℕ) :
    inner ℂ (e i) (e j) = if i = j then 1 else 0 := by
  simp [e, lp.inner_single_left, lp.single_apply, Pi.single_apply, RCLike.inner_apply]

private theorem diagonal_inner (d a b : ℂ) (n : ℕ) :
    inner ℂ (e n) (d • e n + a • e (n + 1) +
      (if n = 0 then 0 else b • e (n - 1))) = d := by
  cases n <;> simp [e_inner, e_norm]

private theorem trace_diagonal (A : H →L[ℂ] H) (hA : MemSchattenClass 1 A) :
    ContinuousLinearMap.opTrace A = ∑' n, inner ℂ (e n) (A (e n)) := by
  let b : HilbertBasis ℕ ℂ H := ⟨LinearIsometryEquiv.refl ℂ H⟩
  have hb (n : ℕ) : b n = e n := (b.repr_symm_single n).symm
  obtain ⟨U, V, hU, hV, hUV⟩ := hA.one_isTraceClass
  rw [hUV, ContinuousLinearMap.opTrace_comp_eq_tsum_basis hU hV b]
  exact tsum_congr fun n => by rw [hb]

private theorem base_pow (t : ℝ) (n : ℕ) :
    Real.exp (-Real.exp t * n) = qKrawtchoukEdgeBase t ^ n := by
  rw [qKrawtchoukEdgeBase, ← Real.exp_nat_mul]
  congr 1
  ring

private theorem base_abs_lt_one (t : ℝ) : |qKrawtchoukEdgeBase t| < 1 := by
  rw [qKrawtchoukEdgeBase, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  exact neg_neg_of_pos (Real.exp_pos t)

/-- The ordinary trace of the limiting companion operator is a geometric quotient. -/
theorem alSalamCarlitzJacobiCLM_opTrace (t u : ℝ) :
    ContinuousLinearMap.opTrace (alSalamCarlitzJacobiCLM t u) =
      (((1 - Real.exp u) / (1 - qKrawtchoukEdgeBase t) : ℝ) : ℂ) := by
  rw [trace_diagonal _ (alSalamCarlitzJacobiCLM_memSchattenClass_one t u)]
  have hd (n : ℕ) :
      inner ℂ (e n) (alSalamCarlitzJacobiCLM t u (e n)) =
        (alSalamCarlitzDiagonal t u n : ℂ) := by
    change inner ℂ (e n) (alSalamCarlitzJacobiCLM t u (lp.single 2 n (1 : ℂ))) = _
    rw [alSalamCarlitzJacobiCLM_single]
    exact diagonal_inner _ _ _ n
  simp_rw [hd, ← Complex.ofReal_tsum, alSalamCarlitzDiagonal, base_pow]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (base_abs_lt_one t)]
  rfl

private theorem finite_trace_sum (t u : ℝ) (K : ℕ) :
    ContinuousLinearMap.opTrace (qKrawtchoukCompanionJacobiCLM t u K) =
      ((∑ n ∈ Finset.range (2 * K + 1), qKrawtchoukCompanionFiniteDiagonal t u K n : ℝ) : ℂ) := by
  rw [trace_diagonal _ (qKrawtchoukCompanionJacobiCLM_memSchattenClass_one t u K)]
  have hd (n : ℕ) :
      inner ℂ (e n) (qKrawtchoukCompanionJacobiCLM t u K (e n)) =
        (qKrawtchoukCompanionBlockDiagonal t u K n : ℂ) := by
    change inner ℂ (e n) (qKrawtchoukCompanionJacobiCLM t u K
      (lp.single 2 n (1 : ℂ))) = _
    rw [qKrawtchoukCompanionJacobiCLM_single]
    exact diagonal_inner _ _ _ n
  simp_rw [hd, ← Complex.ofReal_tsum]
  congr 1
  rw [tsum_eq_sum (s := Finset.range (2 * K + 1)) (fun n hn => by
    have h : ¬ n ≤ 2 * K := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    simp [qKrawtchoukCompanionBlockDiagonal, h])]
  exact Finset.sum_congr rfl fun n hn => by
    have h : n ≤ 2 * K := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    simp [qKrawtchoukCompanionBlockDiagonal, h]

/-- Exact finite trace, including the balanced finite-size correction. -/
theorem qKrawtchoukCompanionJacobiCLM_opTrace (t u : ℝ) (K : ℕ) :
    ContinuousLinearMap.opTrace (qKrawtchoukCompanionJacobiCLM t u K) =
      (((1 - Real.exp u) *
          ((qKrawtchoukEdgeBase t ^ (2 * K + 1) - 1) / (qKrawtchoukEdgeBase t - 1)) +
        (2 * (K : ℝ) + 1) * (Real.exp u - 1) * qKrawtchoukEdgeBase t ^ K : ℝ) : ℂ) := by
  rw [finite_trace_sum]
  congr 1
  simp_rw [qKrawtchoukCompanionFiniteDiagonal, alSalamCarlitzDiagonal, base_pow]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    geom_sum_eq (ne_of_lt (lt_of_le_of_lt (le_abs_self _) (base_abs_lt_one t)))]
  simp [mul_assoc]

/-- The traces converge to the explicit geometric quotient. -/
theorem qKrawtchoukCompanionJacobiCLM_opTrace_explicit_tendsto (t u : ℝ) :
    Tendsto (fun K => ContinuousLinearMap.opTrace (qKrawtchoukCompanionJacobiCLM t u K))
      atTop (𝓝 (((1 - Real.exp u) / (1 - qKrawtchoukEdgeBase t) : ℝ) : ℂ)) := by
  rw [← alSalamCarlitzJacobiCLM_opTrace]
  exact qKrawtchoukCompanionJacobiCLM_opTrace_tendsto t u

end HTGeometry
