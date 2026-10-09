import GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionOperatorDecay
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Norm convergence of the actual companion Jacobi operators

The finite and limiting operators act on one fixed sequence space. A
summable series of rank-one matrix entries constructs each operator; real
symmetric coefficients give self-adjointness. The common geometric envelope
and coefficient limits prove convergence in operator norm by dominated
convergence for Banach-valued series. On every coordinate vector the operators
have exactly the companion tridiagonal coefficients of arXiv:2609.24149,
Section 8, with the finite matrices extended by zero.
-/

noncomputable section
open Filter
open scoped Topology BigOperators ComplexConjugate

namespace HTGeometry

local notation "H" => lp (fun _ : ℕ => ℂ) 2

private def coordinate (n : ℕ) : H := lp.single 2 n (1 : ℂ)

private theorem coordinate_norm (n : ℕ) : ‖coordinate n‖ = 1 := by
  rw [coordinate, lp.norm_single (by norm_num), norm_one]

private theorem coordinate_inner (i j : ℕ) :
    inner ℂ (coordinate i) (coordinate j) = if i = j then 1 else 0 := by
  simp [coordinate, lp.inner_single_left, lp.single_apply, Pi.single_apply, RCLike.inner_apply]

private def jacobiTerm (d a : ℝ) (n : ℕ) : H →L[ℂ] H :=
  (d : ℂ) • InnerProductSpace.rankOne ℂ (coordinate n) (coordinate n) +
  (a : ℂ) • InnerProductSpace.rankOne ℂ (coordinate (n + 1)) (coordinate n) +
  (a : ℂ) • InnerProductSpace.rankOne ℂ (coordinate n) (coordinate (n + 1))

private theorem term_norm (d a : ℝ) (n : ℕ) : ‖jacobiTerm d a n‖ ≤ |d| + 2 * |a| := by
  unfold jacobiTerm
  have h := (norm_add_le
    ((d : ℂ) • InnerProductSpace.rankOne ℂ (coordinate n) (coordinate n) +
      (a : ℂ) • InnerProductSpace.rankOne ℂ (coordinate (n + 1)) (coordinate n))
    ((a : ℂ) • InnerProductSpace.rankOne ℂ (coordinate n) (coordinate (n + 1)))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  simpa only [norm_smul, InnerProductSpace.norm_rankOne, coordinate_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, two_mul, add_assoc] using h

private theorem term_selfAdjoint (d a : ℝ) (n : ℕ) : IsSelfAdjoint (jacobiTerm d a n) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp only [jacobiTerm, map_add, map_smulₛₗ, Complex.conj_ofReal,
    InnerProductSpace.adjoint_rankOne]
  abel

private theorem term_single (d a : ℝ) (k n : ℕ) :
    jacobiTerm d a k (coordinate n) =
      (if k = n then (d : ℂ) • coordinate n + (a : ℂ) • coordinate (n + 1) else 0) +
      (if k + 1 = n then (a : ℂ) • coordinate k else 0) := by
  change (d : ℂ) • (inner ℂ (coordinate k) (coordinate n) • coordinate k) +
      (a : ℂ) • (inner ℂ (coordinate k) (coordinate n) • coordinate (k + 1)) +
      (a : ℂ) • (inner ℂ (coordinate (k + 1)) (coordinate n) • coordinate k) = _
  simp only [coordinate_inner]
  by_cases hk : k = n
  · subst k
    simp
  · simp only [hk, if_false, zero_smul, smul_zero, zero_add]
    split_ifs <;> simp

private theorem series_summable (d a : ℕ → ℝ) (E : ℕ → ℝ) (hE : Summable E)
    (h : ∀ n, |d n| + 2 * |a n| ≤ E n) :
    Summable (fun n => jacobiTerm (d n) (a n) n) :=
  hE.of_norm_bounded (fun n => (term_norm _ _ n).trans (h n))

private theorem series_selfAdjoint (d a : ℕ → ℝ) :
    IsSelfAdjoint (∑' n, jacobiTerm (d n) (a n) n) := by
  rw [IsSelfAdjoint, tsum_star]
  exact tsum_congr fun n => (term_selfAdjoint (d n) (a n) n).star_eq

private theorem term_compact (d a : ℝ) (n : ℕ) : IsCompactOperator (jacobiTerm d a n) := by
  have hr (x y : H) : IsCompactOperator (InnerProductSpace.rankOne ℂ x y) := by
    rw [InnerProductSpace.rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℂ x)
  exact (((hr (coordinate n) (coordinate n)).smul (d : ℂ)).add
    ((hr (coordinate (n + 1)) (coordinate n)).smul (a : ℂ))).add
    ((hr (coordinate n) (coordinate (n + 1))).smul (a : ℂ))

private theorem series_compact (d a : ℕ → ℝ)
    (hs : Summable (fun n => jacobiTerm (d n) (a n) n)) :
    IsCompactOperator ((∑' n, jacobiTerm (d n) (a n) n) : H →L[ℂ] H) := by
  apply isCompactOperator_of_tendsto hs.hasSum
  apply Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact isCompactOperator_zero
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn]
      exact (term_compact (d n) (a n) n).add ih

private theorem series_single (d a : ℕ → ℝ)
    (hs : Summable (fun n => jacobiTerm (d n) (a n) n)) (n : ℕ) :
    (∑' k, jacobiTerm (d k) (a k) k) (coordinate n) =
      (d n : ℂ) • coordinate n + (a n : ℂ) • coordinate (n + 1) +
      (if n = 0 then 0 else (a (n - 1) : ℂ) • coordinate (n - 1)) := by
  have hmap : (∑' k, jacobiTerm (d k) (a k) k) (coordinate n) =
      ∑' k, jacobiTerm (d k) (a k) k (coordinate n) :=
    (ContinuousLinearMap.apply ℂ H (coordinate n)).map_tsum hs
  rw [hmap]
  cases n with
  | zero =>
      rw [tsum_eq_single 0 (fun k hk => by simp [term_single, hk])]
      simp [term_single]
  | succ n =>
      rw [tsum_eq_sum (s := {n, n + 1}) (fun k hk => by
        have hkn : k ≠ n ∧ k ≠ n + 1 := by
          simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
        simp [term_single, hkn.1, hkn.2])]
      rw [Finset.sum_pair (by omega : n ≠ n + 1)]
      simp only [term_single, Nat.add_sub_cancel, show n + 1 ≠ 0 by omega,
        if_false, if_true, show n ≠ n + 1 by omega,
        show n + 1 + 1 ≠ n + 1 by omega, zero_add, add_zero]
      abel

/-- The actual bounded Al-Salam--Carlitz Jacobi operator on the common sequence space. -/
def alSalamCarlitzJacobiCLM (t u : ℝ) : H →L[ℂ] H :=
  ∑' n, jacobiTerm (alSalamCarlitzDiagonal t u n) (alSalamCarlitzJacobiBond t u n) n

/-- The actual finite companion matrix, extended by zero on the same sequence space. -/
def qKrawtchoukCompanionJacobiCLM (t u : ℝ) (K : ℕ) : H →L[ℂ] H :=
  ∑' n, jacobiTerm (qKrawtchoukCompanionBlockDiagonal t u K n)
    (qKrawtchoukCompanionBlockBond t u K n) n

/-- The limiting operator is self-adjoint on all of ℓ². -/
theorem alSalamCarlitzJacobiCLM_isSelfAdjoint (t u : ℝ) :
    IsSelfAdjoint (alSalamCarlitzJacobiCLM t u) := series_selfAdjoint _ _

/-- Geometric decay also makes the limiting companion operator compact. -/
theorem alSalamCarlitzJacobiCLM_isCompactOperator (t u : ℝ) :
    IsCompactOperator (alSalamCarlitzJacobiCLM t u) :=
  series_compact _ _ (series_summable _ _ _ (summable_alSalamCarlitzJacobiEnvelope t u)
    (alSalamCarlitzJacobi_coeff_bound t u))

/-- Every extended finite companion matrix is self-adjoint on all of ℓ². -/
theorem qKrawtchoukCompanionJacobiCLM_isSelfAdjoint (t u : ℝ) (K : ℕ) :
    IsSelfAdjoint (qKrawtchoukCompanionJacobiCLM t u K) := series_selfAdjoint _ _

/-- The limiting operator has the exact companion Jacobi action, including coordinate zero. -/
theorem alSalamCarlitzJacobiCLM_single (t u : ℝ) (n : ℕ) :
    alSalamCarlitzJacobiCLM t u (lp.single 2 n (1 : ℂ)) =
      (alSalamCarlitzDiagonal t u n : ℂ) • lp.single 2 n (1 : ℂ) +
      (alSalamCarlitzJacobiBond t u n : ℂ) • lp.single 2 (n + 1) (1 : ℂ) +
      (if n = 0 then 0 else
        (alSalamCarlitzJacobiBond t u (n - 1) : ℂ) • lp.single 2 (n - 1) (1 : ℂ)) :=
  series_single _ _ (series_summable _ _ _ (summable_alSalamCarlitzJacobiEnvelope t u)
    (alSalamCarlitzJacobi_coeff_bound t u)) n

/-- The finite operators realize the actual finite coefficients at every coordinate. -/
theorem qKrawtchoukCompanionJacobiCLM_single (t u : ℝ) (K n : ℕ) :
    qKrawtchoukCompanionJacobiCLM t u K (lp.single 2 n (1 : ℂ)) =
      (qKrawtchoukCompanionBlockDiagonal t u K n : ℂ) • lp.single 2 n (1 : ℂ) +
      (qKrawtchoukCompanionBlockBond t u K n : ℂ) • lp.single 2 (n + 1) (1 : ℂ) +
      (if n = 0 then 0 else
        (qKrawtchoukCompanionBlockBond t u K (n - 1) : ℂ) •
          lp.single 2 (n - 1) (1 : ℂ)) :=
  series_single _ _ (series_summable _ _ _ (summable_alSalamCarlitzJacobiEnvelope t u)
    (qKrawtchoukCompanionBlock_coeff_bound t u K)) n

/-- The extension really vanishes on every coordinate beyond the finite block. -/
theorem qKrawtchoukCompanionJacobiCLM_tail (t u : ℝ) (K n : ℕ) :
    qKrawtchoukCompanionJacobiCLM t u K (lp.single 2 (2 * K + 1 + n) (1 : ℂ)) = 0 := by
  rw [qKrawtchoukCompanionJacobiCLM_single]
  simp only [qKrawtchoukCompanionBlockDiagonal, qKrawtchoukCompanionBlockBond,
    if_neg (show ¬ 2 * K + 1 + n ≤ 2 * K by omega),
    if_neg (show ¬ 2 * K + 1 + n < 2 * K by omega),
    if_neg (show 2 * K + 1 + n ≠ 0 by omega),
    if_neg (show ¬ 2 * K + 1 + n - 1 < 2 * K by omega),
    Complex.ofReal_zero, zero_smul, zero_add]

/-- The balanced finite companion operators converge in operator norm.
This is stronger than convergence on individual vectors. -/
theorem qKrawtchoukCompanionJacobiCLM_tendsto (t u : ℝ) :
    Tendsto (qKrawtchoukCompanionJacobiCLM t u) atTop (𝓝 (alSalamCarlitzJacobiCLM t u)) := by
  apply tendsto_tsum_of_dominated_convergence (summable_alSalamCarlitzJacobiEnvelope t u)
  · intro n
    obtain ⟨hd, ha⟩ := qKrawtchoukCompanionBlock_coeff_tendsto t u n
    have hdc := (Complex.continuous_ofReal.tendsto _).comp hd
    have hac := (Complex.continuous_ofReal.tendsto _).comp ha
    exact ((hdc.smul_const _).add (hac.smul_const _)).add (hac.smul_const _)
  · exact Eventually.of_forall fun K n => (term_norm _ _ n).trans
      (qKrawtchoukCompanionBlock_coeff_bound t u K n)

end HTGeometry
