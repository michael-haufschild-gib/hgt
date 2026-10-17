import GaloisForLFunctions.RHTower.MobiusDivisorPrimeGraphClockRealization
import GaloisForLFunctions.RHTower.CHMDResolventNodalCrossPositivityAndBalancedRayleighExcess

/-!
# Off-Diagonal Prime-Clock Synthesis, Diagonal Vanishing, and Stationary Energy Decomposition

This module bridges the terminal-prime clock synthesis theorem in `SourceGraph`
(`RHTower.exists_cutoff_eventually_criticalPrimeGraphClock_realization` from
`MobiusDivisorPrimeGraphClockRealization.lean`) with the maximal-domain stationary and prime-shift
operator decompositions of `SourceGraph` (`CHMDHarmonicGroundPotentialAndMaximalDomainPrimeShiftForm.lean`,
`CHMDBalancedNodalGraphAndGroundPerturbationResolvent.lean`, and
`CHMDResolventNodalCrossPositivityAndBalancedRayleighExcess.lean`).

## Mathematical Overview

1. **Exact Quadratic Continuity and Bilinear Cauchy–Schwarz Bounds on `SourceGraph` and `MassSpace`**:
   - `abs_sourcePair_le_norm_mul` and `abs_sourceEnergy_le_norm_sq`:
     for all `p, q : SourceGraph`, `|sourcePair p q| ≤ ‖p‖ * ‖q‖` and `|sourceEnergy p| ≤ ‖p‖ ^ 2`.
   - `sourceEnergy_sub_sourceEnergy_eq` and `abs_sourceEnergy_sub_le`:
     `sourceEnergy P - sourceEnergy q = sourceEnergy (P - q) + 2 * sourcePair (P - q) q` and
     `|sourceEnergy P - sourceEnergy q| ≤ ‖P - q‖ ^ 2 + 2 * ‖P - q‖ * ‖q‖`.
   - `inner_clm_fst_sub_eq` and `abs_inner_clm_fst_sub_le`:
     for every continuous linear operator `T : MassSpace →L[ℝ] MassSpace`,
     `|⟪T P.val.fst, P.val.fst⟫_ℝ - ⟪T q.val.fst, q.val.fst⟫_ℝ| ≤ ‖T‖ * (‖P - q‖ ^ 2 + 2 * ‖P - q‖ * ‖q‖)`.
   - `stationaryEnergy_nonneg_and_le_norm_sq`:
     `0 ≤ stationaryEnergy (thetaProduct p.val.fst) ≤ (1 + ‖groundPerturbation‖) * ‖p‖ ^ 2`.

2. **Exact Finite-Packet Diagonal / Off-Diagonal Decompositions and Diagonal Vanishing Bounds**:
   for any finite index set `S : Finset ι` and packet `a : ι → SourceGraph`:
   - `sourceEnergy_sum_eq_diag_add_offDiag`, `inner_clm_sum_fst_eq_diag_add_offDiag`, and
     `stationaryEnergy_sum_eq_diag_add_offDiag`:
     exact splitting of `sourceEnergy (∑ i ∈ S, a i)`, `⟪T (∑ i ∈ S, a i).val.fst, (∑ i ∈ S, a i).val.fst⟫_ℝ`,
     and `stationaryEnergy (thetaProduct (∑ i ∈ S, a i).val.fst)` into their diagonal sums over `i ∈ S`
     and their off-diagonal (`i ≠ j`) sums `offDiagSourcePairSum S a`, `offDiagOperatorSum T S a`,
     and `offDiagStationarySum S a`.
   - `offDiagSourcePairSum_eq_stationary_sub_arch_sub_primeShift` and
     `offDiagSourcePairSum_eq_stationary_add_primeGenerator_add_groundPotential_sub_id`:
     exact operator decompositions of the off-diagonal Doob pairing sum.
   - `abs_sourceEnergy_sum_sub_offDiag_le`, `abs_inner_clm_sum_fst_sub_offDiag_le`, and
     `sum_stationaryEnergy_le_sum_norm_sq`:
     every diagonal sum (`sourceEnergy`, `groundPotentialOperator`, `archDiagonalOperator`,
     `primeShiftOperator`, `primeGenerator`, and `stationaryEnergy`) is bounded by a constant multiple
     of the quadratic diagonal graph cost `∑ i ∈ S, ‖a i‖ ^ 2`.

3. **Purely Off-Diagonal Terminal-Prime Clock Realization of `sourceEnergy` and Operator Forms**:
   - `exists_cutoff_eventually_offDiag_primeClock_realization`:
     by `exists_cutoff_eventually_criticalPrimeGraphClock_realization`, for any `q : SourceGraph`,
     any operator `T : MassSpace →L[ℝ] MassSpace`, any depth threshold `T₀ : ℝ`, and any `0 < ε`,
     there exists a cutoff `k : ℕ` such that for all sufficiently large `N : ℕ`, there exists a finite
     set `S` of distinct primes `p > √N` with `log(N / p) > T₀` such that the diagonal graph cost
     `∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2 < ε` forces all diagonal potential, shift,
     and stationary terms to be `O(ε)`, concentrating `sourceEnergy q` and `⟪T q.val.fst, q.val.fst⟫_ℝ`
     entirely in the distinct-prime (`p ≠ p'`) off-diagonal clock sums.

4. **Pointwise Prime-Ratio Lag Identity and Off-Diagonal Characterization of Above-Threshold Eigenvectors**:
   - `primeClock_log_lag_identity` and `canonicalPrimeGraphClockAtom_fst_mul_ae`:
     for any two primes `p, p'`, the common scale `N` cancels between `log(N / p) - x` and
     `log(N / p') - x`, leaving the scale-free prime-ratio log-lag `log(p' / p)`.
   - `exists_cutoff_eventually_offDiag_primeClock_neg_of_eigenvector_gt_half`,
     `sourceEnergy_nonneg_of_offDiag_primeClock_nonneg`, and
     `eigenvalue_le_one_half_of_offDiag_primeClock_nonneg`:
     any hypothetical eigenvector `resolvent w = μ • w` with `1 / 2 < μ` forces strict negativity
     of `offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N)` at all sufficiently large scales `N`,
     whereas nonnegativity of the off-diagonal prime-clock pairing along arbitrary-precision realizations
     forces `0 ≤ sourceEnergy (rieszLift w)` and `μ ≤ 1 / 2`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace BigOperators
noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

open _root_.RHTower _root_.RHTower.CHMDDoobGraph _root_.RHTower.CHMDClosedJump _root_.RHTower.CHMDPolar

/-! ## Section 1: Exact Quadratic Continuity and Bilinear Cauchy–Schwarz Bounds on `SourceGraph` and `MassSpace` -/

/-- Exact Pythagorean norm decomposition on `SourceGraph`:
`‖p‖ ^ 2 = ‖p.val.fst‖ ^ 2 + ‖p.val.snd‖ ^ 2`. -/
theorem graph_norm_sq (p : SourceGraph) :
    ‖p‖ ^ 2 = ‖p.val.fst‖ ^ 2 + ‖p.val.snd‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, graph_inner, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

theorem norm_fst_sq_le_norm_sq (p : SourceGraph) : ‖p.val.fst‖ ^ 2 ≤ ‖p‖ ^ 2 := by
  rw [graph_norm_sq]
  linarith [sq_nonneg ‖p.val.snd‖]

theorem norm_snd_sq_le_norm_sq (p : SourceGraph) : ‖p.val.snd‖ ^ 2 ≤ ‖p‖ ^ 2 := by
  rw [graph_norm_sq]
  linarith [sq_nonneg ‖p.val.fst‖]

theorem norm_fst_le_norm (p : SourceGraph) : ‖p.val.fst‖ ≤ ‖p‖ := by
  nlinarith [norm_fst_sq_le_norm_sq p, norm_nonneg p.val.fst, norm_nonneg p]

theorem norm_snd_le_norm (p : SourceGraph) : ‖p.val.snd‖ ≤ ‖p‖ := by
  nlinarith [norm_snd_sq_le_norm_sq p, norm_nonneg p.val.snd, norm_nonneg p]

/-- Symmetry of the Doob bilinear form `sourcePair` on `SourceGraph`. -/
theorem sourcePair_symm (p q : SourceGraph) : sourcePair p q = sourcePair q p := by
  change ⟪p.val.snd, q.val.snd⟫_ℝ - ⟪p.val.fst, q.val.fst⟫_ℝ =
    ⟪q.val.snd, p.val.snd⟫_ℝ - ⟪q.val.fst, p.val.fst⟫_ℝ
  rw [real_inner_comm p.val.snd q.val.snd, real_inner_comm p.val.fst q.val.fst]

@[simp]
theorem sourcePair_zero_left (q : SourceGraph) : sourcePair 0 q = 0 := by
  simpa using sourcePair_smul_left 0 q q

@[simp]
theorem sourcePair_zero_right (p : SourceGraph) : sourcePair p 0 = 0 := by
  simpa using sourcePair_smul_right 0 p p

theorem sourcePair_neg_left (p q : SourceGraph) : sourcePair (-p) q = -sourcePair p q := by
  simpa using sourcePair_smul_left (-1) p q

theorem sourcePair_neg_right (p q : SourceGraph) : sourcePair p (-q) = -sourcePair p q := by
  simpa using sourcePair_smul_right (-1) p q

theorem sourcePair_sub_left (p q r : SourceGraph) :
    sourcePair (p - q) r = sourcePair p r - sourcePair q r := by
  rw [sub_eq_add_neg, sourcePair_add_left, sourcePair_neg_left, sub_eq_add_neg]

theorem sourcePair_sub_right (p q r : SourceGraph) :
    sourcePair p (q - r) = sourcePair p q - sourcePair p r := by
  rw [sub_eq_add_neg, sourcePair_add_right, sourcePair_neg_right, sub_eq_add_neg]

/-- **Sharp Bilinear Cauchy–Schwarz Bound for `sourcePair` on `SourceGraph`**:
for all `p, q : SourceGraph`, `|sourcePair p q| ≤ ‖p‖ * ‖q‖`. -/
theorem abs_sourcePair_le_norm_mul (p q : SourceGraph) :
    |sourcePair p q| ≤ ‖p‖ * ‖q‖ := by
  have h1 : |sourcePair p q| ≤ ‖p.val.snd‖ * ‖q.val.snd‖ + ‖p.val.fst‖ * ‖q.val.fst‖ := by
    change |⟪p.val.snd, q.val.snd⟫_ℝ - ⟪p.val.fst, q.val.fst⟫_ℝ| ≤ _
    calc |⟪p.val.snd, q.val.snd⟫_ℝ - ⟪p.val.fst, q.val.fst⟫_ℝ|
        ≤ |⟪p.val.snd, q.val.snd⟫_ℝ| + |⟪p.val.fst, q.val.fst⟫_ℝ| := abs_sub _ _
      _ ≤ ‖p.val.snd‖ * ‖q.val.snd‖ + ‖p.val.fst‖ * ‖q.val.fst‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
  have hlagrange :
      (‖p‖ * ‖q‖) ^ 2 - (‖p.val.snd‖ * ‖q.val.snd‖ + ‖p.val.fst‖ * ‖q.val.fst‖) ^ 2 =
        (‖p.val.fst‖ * ‖q.val.snd‖ - ‖p.val.snd‖ * ‖q.val.fst‖) ^ 2 := by
    rw [mul_pow, graph_norm_sq p, graph_norm_sq q]
    ring
  have hsq : (‖p.val.snd‖ * ‖q.val.snd‖ + ‖p.val.fst‖ * ‖q.val.fst‖) ^ 2 ≤ (‖p‖ * ‖q‖) ^ 2 := by
    linarith [hlagrange, sq_nonneg (‖p.val.fst‖ * ‖q.val.snd‖ - ‖p.val.snd‖ * ‖q.val.fst‖)]
  have h2 : ‖p.val.snd‖ * ‖q.val.snd‖ + ‖p.val.fst‖ * ‖q.val.fst‖ ≤ ‖p‖ * ‖q‖ := by
    nlinarith [hsq, mul_nonneg (norm_nonneg p) (norm_nonneg q),
      add_nonneg (mul_nonneg (norm_nonneg p.val.snd) (norm_nonneg q.val.snd))
        (mul_nonneg (norm_nonneg p.val.fst) (norm_nonneg q.val.fst))]
  exact h1.trans h2

/-- **Sharp Norm Bound for `sourceEnergy` on `SourceGraph`**:
for every `p : SourceGraph`, `|sourceEnergy p| ≤ ‖p‖ ^ 2`. -/
theorem abs_sourceEnergy_le_norm_sq (p : SourceGraph) :
    |sourceEnergy p| ≤ ‖p‖ ^ 2 := by
  have hE : sourceEnergy p = ‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2 := rfl
  rw [hE, graph_norm_sq, abs_le]
  exact ⟨by linarith [sq_nonneg ‖p.val.fst‖, sq_nonneg ‖p.val.snd‖],
    by linarith [sq_nonneg ‖p.val.fst‖, sq_nonneg ‖p.val.snd‖]⟩

/-- Polarization identity for `sourceEnergy (p + q)`. -/
theorem sourceEnergy_add_eq (p q : SourceGraph) :
    sourceEnergy (p + q) = sourceEnergy p + sourceEnergy q + 2 * sourcePair p q := by
  rw [← sourcePair_self (p + q), sourcePair_add_left, sourcePair_add_right,
    sourcePair_add_right, sourcePair_self, sourcePair_self, sourcePair_symm q p]
  ring

/-- Exact quadratic difference identity for `sourceEnergy P - sourceEnergy q`. -/
theorem sourceEnergy_sub_sourceEnergy_eq (P q : SourceGraph) :
    sourceEnergy P - sourceEnergy q =
      sourceEnergy (P - q) + 2 * sourcePair (P - q) q := by
  have h := sourceEnergy_add_eq (P - q) q
  rw [sub_add_cancel] at h
  linarith

/-- **Quantitative Quadratic Continuity Bound for `sourceEnergy` on `SourceGraph`**:
for all `P, q : SourceGraph`,
`|sourceEnergy P - sourceEnergy q| ≤ ‖P - q‖ ^ 2 + 2 * ‖P - q‖ * ‖q‖`. -/
theorem abs_sourceEnergy_sub_le (P q : SourceGraph) :
    |sourceEnergy P - sourceEnergy q| ≤ ‖P - q‖ ^ 2 + 2 * ‖P - q‖ * ‖q‖ := by
  rw [sourceEnergy_sub_sourceEnergy_eq P q]
  calc |sourceEnergy (P - q) + 2 * sourcePair (P - q) q|
      ≤ |sourceEnergy (P - q)| + |2 * sourcePair (P - q) q| := abs_add_le _ _
    _ = |sourceEnergy (P - q)| + 2 * |sourcePair (P - q) q| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ ‖P - q‖ ^ 2 + 2 * (‖P - q‖ * ‖q‖) :=
        add_le_add (abs_sourceEnergy_le_norm_sq (P - q))
          (mul_le_mul_of_nonneg_left (abs_sourcePair_le_norm_mul (P - q) q) (by norm_num))
    _ = ‖P - q‖ ^ 2 + 2 * ‖P - q‖ * ‖q‖ := by ring

/-- Exact quadratic difference identity for any continuous linear operator `T` on `MassSpace`. -/
theorem inner_clm_fst_sub_eq (T : MassSpace →L[ℝ] MassSpace) (P q : SourceGraph) :
    ⟪T P.val.fst, P.val.fst⟫_ℝ - ⟪T q.val.fst, q.val.fst⟫_ℝ =
      ⟪T (P - q).val.fst, (P - q).val.fst⟫_ℝ +
        ⟪T (P - q).val.fst, q.val.fst⟫_ℝ +
        ⟪T q.val.fst, (P - q).val.fst⟫_ℝ := by
  have hP : P.val.fst = (P - q).val.fst + q.val.fst := by
    change P.val.fst = (P.val.fst - q.val.fst) + q.val.fst
    abel
  conv_lhs => rw [hP]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right]
  ring

/-- For any `T : MassSpace →L[ℝ] MassSpace` and `p, q : SourceGraph`,
`|⟪T p.val.fst, q.val.fst⟫_ℝ| ≤ ‖T‖ * ‖p‖ * ‖q‖`. -/
theorem abs_inner_clm_fst_le_norm_mul (T : MassSpace →L[ℝ] MassSpace) (p q : SourceGraph) :
    |⟪T p.val.fst, q.val.fst⟫_ℝ| ≤ ‖T‖ * ‖p‖ * ‖q‖ := by
  calc |⟪T p.val.fst, q.val.fst⟫_ℝ|
      ≤ ‖T p.val.fst‖ * ‖q.val.fst‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖p.val.fst‖) * ‖q.val.fst‖ :=
      mul_le_mul_of_nonneg_right (T.le_opNorm p.val.fst) (norm_nonneg _)
    _ ≤ (‖T‖ * ‖p‖) * ‖q‖ := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left (norm_fst_le_norm p) (norm_nonneg T))
        (norm_fst_le_norm q) (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg p))
    _ = ‖T‖ * ‖p‖ * ‖q‖ := by ring

/-- **Quantitative Quadratic Continuity Bound for Bounded Operator Forms on `SourceGraph`**:
for any `T : MassSpace →L[ℝ] MassSpace` and `P, q : SourceGraph`,
`|⟪T P.val.fst, P.val.fst⟫_ℝ - ⟪T q.val.fst, q.val.fst⟫_ℝ| ≤ ‖T‖ * (‖P - q‖ ^ 2 + 2 * ‖P - q‖ * ‖q‖)`. -/
theorem abs_inner_clm_fst_sub_le (T : MassSpace →L[ℝ] MassSpace) (P q : SourceGraph) :
    |⟪T P.val.fst, P.val.fst⟫_ℝ - ⟪T q.val.fst, q.val.fst⟫_ℝ| ≤
      ‖T‖ * (‖P - q‖ ^ 2 + 2 * ‖P - q‖ * ‖q‖) := by
  rw [inner_clm_fst_sub_eq T P q]
  have h1 := abs_inner_clm_fst_le_norm_mul T (P - q) (P - q)
  have h2 := abs_inner_clm_fst_le_norm_mul T (P - q) q
  have h3 := abs_inner_clm_fst_le_norm_mul T q (P - q)
  have habs1 := abs_add_le
    (⟪T (P - q).val.fst, (P - q).val.fst⟫_ℝ + ⟪T (P - q).val.fst, q.val.fst⟫_ℝ)
    ⟪T q.val.fst, (P - q).val.fst⟫_ℝ
  have habs2 := abs_add_le
    ⟪T (P - q).val.fst, (P - q).val.fst⟫_ℝ
    ⟪T (P - q).val.fst, q.val.fst⟫_ℝ
  linarith [show ‖T‖ * ‖P - q‖ * ‖P - q‖ = ‖T‖ * ‖P - q‖ ^ 2 by ring,
    show ‖T‖ * ‖q‖ * ‖P - q‖ = ‖T‖ * ‖P - q‖ * ‖q‖ by ring]

/-- **Graph-Norm Bound for `stationaryEnergy`**:
for every `p : SourceGraph`,
`0 ≤ stationaryEnergy (thetaProduct p.val.fst)` and
`stationaryEnergy (thetaProduct p.val.fst) ≤ (1 + ‖groundPerturbation‖) * ‖p‖ ^ 2`. -/
theorem stationaryEnergy_nonneg_and_le_norm_sq (p : SourceGraph) :
    0 ≤ stationaryEnergy (thetaProduct p.val.fst) ∧
      stationaryEnergy (thetaProduct p.val.fst) ≤
        (1 + ‖groundPerturbation‖) * ‖p‖ ^ 2 := by
  have hp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
  have hstat_eq : ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv p).val.snd⟫_ℝ =
      stationaryEnergy (thetaProduct p.val.fst) := by
    rw [real_inner_self_eq_norm_sq, stationaryGround_edge_energy, hp]
  have hnn : 0 ≤ stationaryEnergy (thetaProduct p.val.fst) := by
    rw [← hstat_eq, real_inner_self_eq_norm_sq]
    exact sq_nonneg _
  have hdecomp := (inner_snd_eq_stationary_add_primeGenerator_add_groundPotential p p).1
  rw [real_inner_self_eq_norm_sq, hstat_eq] at hdecomp
  have hpert := abs_inner_clm_fst_le_norm_mul groundPerturbation p p
  have hpert_low : -(‖groundPerturbation‖ * ‖p‖ ^ 2) ≤ ⟪groundPerturbation p.val.fst, p.val.fst⟫_ℝ := by
    have h := neg_le_of_abs_le hpert
    linarith [show ‖groundPerturbation‖ * ‖p‖ * ‖p‖ = ‖groundPerturbation‖ * ‖p‖ ^ 2 by ring]
  have hsnd : ‖p.val.snd‖ ^ 2 ≤ ‖p‖ ^ 2 := norm_snd_sq_le_norm_sq p
  exact ⟨hnn, by linarith⟩

/-! ## Section 2: Exact Finite-Packet Diagonal / Off-Diagonal Decompositions and Diagonal Vanishing Bounds -/

theorem fst_sum {ι : Type*} (S : Finset ι) (a : ι → SourceGraph) :
    (∑ i ∈ S, a i).val.fst = ∑ i ∈ S, (a i).val.fst := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, ← ih]
    rfl

theorem snd_sum {ι : Type*} (S : Finset ι) (a : ι → SourceGraph) :
    (∑ i ∈ S, a i).val.snd = ∑ i ∈ S, (a i).val.snd := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, ← ih]
    rfl

theorem fullGroundEquiv_snd_sum {ι : Type*} (S : Finset ι) (a : ι → SourceGraph) :
    (fullGroundEquiv (∑ i ∈ S, a i)).val.snd =
      ∑ i ∈ S, (fullGroundEquiv (a i)).val.snd := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, map_zero]
    rfl
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, map_add, ← ih]
    rfl

theorem sourcePair_sum_left {ι : Type*} (S : Finset ι) (a : ι → SourceGraph) (q : SourceGraph) :
    sourcePair (∑ i ∈ S, a i) q = ∑ i ∈ S, sourcePair (a i) q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, sourcePair_add_left, ih]

theorem sourcePair_sum_right {ι : Type*} (S : Finset ι) (p : SourceGraph) (a : ι → SourceGraph) :
    sourcePair p (∑ j ∈ S, a j) = ∑ j ∈ S, sourcePair p (a j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, sourcePair_add_right, ih]

/-- The off-diagonal (`i ≠ j`) Doob `sourcePair` sum of a finite packet `a : ι → SourceGraph`
indexed by `S : Finset ι`. -/
def offDiagSourcePairSum {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → SourceGraph) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S.erase i, sourcePair (a i) (a j)

/-- The off-diagonal (`i ≠ j`) stationary edge-pairing sum of a finite packet `a : ι → SourceGraph`
indexed by `S : Finset ι`. -/
def offDiagStationarySum {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → SourceGraph) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S.erase i,
    ⟪(fullGroundEquiv (a i)).val.snd, (fullGroundEquiv (a j)).val.snd⟫_ℝ

/-- The off-diagonal (`i ≠ j`) matrix-element sum of a continuous linear operator
`T : MassSpace →L[ℝ] MassSpace` for a finite packet `a : ι → SourceGraph` indexed by `S : Finset ι`. -/
def offDiagOperatorSum {ι : Type*} [DecidableEq ι] (T : MassSpace →L[ℝ] MassSpace)
    (S : Finset ι) (a : ι → SourceGraph) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S.erase i, ⟪T (a i).val.fst, (a j).val.fst⟫_ℝ

/-- **Exact Diagonal + Off-Diagonal Expansion of `sourceEnergy (∑ i ∈ S, a i)`**:
for any finite index set `S : Finset ι` and packet `a : ι → SourceGraph`,
`sourceEnergy (∑ i ∈ S, a i) = (∑ i ∈ S, sourceEnergy (a i)) + offDiagSourcePairSum S a`. -/
theorem sourceEnergy_sum_eq_diag_add_offDiag {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → SourceGraph) :
    sourceEnergy (∑ i ∈ S, a i) =
      (∑ i ∈ S, sourceEnergy (a i)) + offDiagSourcePairSum S a := by
  unfold offDiagSourcePairSum
  rw [← sourcePair_self (∑ i ∈ S, a i), sourcePair_sum_left, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [sourcePair_sum_right, ← Finset.add_sum_erase S (fun j => sourcePair (a i) (a j)) hi,
    sourcePair_self]

/-- **Exact Diagonal + Off-Diagonal Expansion of `⟪T (∑ i ∈ S, a i).val.fst, (∑ i ∈ S, a i).val.fst⟫_ℝ`**:
for any `T : MassSpace →L[ℝ] MassSpace`, finite index set `S : Finset ι`, and packet `a : ι → SourceGraph`,
`⟪T (∑ i ∈ S, a i).val.fst, (∑ i ∈ S, a i).val.fst⟫_ℝ = (∑ i ∈ S, ⟪T (a i).val.fst, (a i).val.fst⟫_ℝ) + offDiagOperatorSum T S a`. -/
theorem inner_clm_sum_fst_eq_diag_add_offDiag {ι : Type*} [DecidableEq ι]
    (T : MassSpace →L[ℝ] MassSpace) (S : Finset ι) (a : ι → SourceGraph) :
    ⟪T (∑ i ∈ S, a i).val.fst, (∑ i ∈ S, a i).val.fst⟫_ℝ =
      (∑ i ∈ S, ⟪T (a i).val.fst, (a i).val.fst⟫_ℝ) + offDiagOperatorSum T S a := by
  unfold offDiagOperatorSum
  rw [fst_sum, map_sum, sum_inner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum, ← Finset.add_sum_erase S (fun j => ⟪T (a i).val.fst, (a j).val.fst⟫_ℝ) hi]

/-- **Exact Diagonal + Off-Diagonal Expansion of `stationaryEnergy` for a Finite Packet**:
for any finite index set `S : Finset ι` and packet `a : ι → SourceGraph`,
`stationaryEnergy (thetaProduct (∑ i ∈ S, a i).val.fst) = (∑ i ∈ S, stationaryEnergy (thetaProduct (a i).val.fst)) + offDiagStationarySum S a`. -/
theorem stationaryEnergy_sum_eq_diag_add_offDiag {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → SourceGraph) :
    stationaryEnergy (thetaProduct (∑ i ∈ S, a i).val.fst) =
      (∑ i ∈ S, stationaryEnergy (thetaProduct (a i).val.fst)) + offDiagStationarySum S a := by
  unfold offDiagStationarySum
  have hstat (p : SourceGraph) :
      stationaryEnergy (thetaProduct p.val.fst) =
        ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv p).val.snd⟫_ℝ := by
    have hp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
    rw [real_inner_self_eq_norm_sq, stationaryGround_edge_energy, hp]
  rw [hstat (∑ i ∈ S, a i), fullGroundEquiv_snd_sum, sum_inner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum,
    ← Finset.add_sum_erase S
      (fun j => ⟪(fullGroundEquiv (a i)).val.snd, (fullGroundEquiv (a j)).val.snd⟫_ℝ) hi,
    ← hstat (a i)]

/-- **Off-Diagonal Stationary + Archimedean + Prime-Shift Decomposition**:
for any finite index set `S : Finset ι` and packet `a : ι → SourceGraph`,
`offDiagSourcePairSum S a = offDiagStationarySum S a - offDiagOperatorSum archDiagonalOperator S a - offDiagOperatorSum primeShiftOperator S a`. -/
theorem offDiagSourcePairSum_eq_stationary_sub_arch_sub_primeShift {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → SourceGraph) :
    offDiagSourcePairSum S a =
      offDiagStationarySum S a -
        offDiagOperatorSum archDiagonalOperator S a -
        offDiagOperatorSum primeShiftOperator S a := by
  unfold offDiagSourcePairSum offDiagStationarySum offDiagOperatorSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sourcePair_eq_stationary_sub_arch_sub_primeShift (a i) (a j),
    inner_archDiagonalOperator]

/-- **Off-Diagonal Stationary + Prime-Generator + Ground-Potential Decomposition**:
for any finite index set `S : Finset ι` and packet `a : ι → SourceGraph`,
`offDiagSourcePairSum S a = offDiagStationarySum S a + offDiagOperatorSum primeGenerator S a + offDiagOperatorSum (groundPotentialOperator - ContinuousLinearMap.id ℝ MassSpace) S a`. -/
theorem offDiagSourcePairSum_eq_stationary_add_primeGenerator_add_groundPotential_sub_id
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → SourceGraph) :
    offDiagSourcePairSum S a =
      offDiagStationarySum S a +
        offDiagOperatorSum primeGenerator S a +
        offDiagOperatorSum (groundPotentialOperator - ContinuousLinearMap.id ℝ MassSpace) S a := by
  unfold offDiagSourcePairSum offDiagStationarySum offDiagOperatorSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := (inner_snd_eq_stationary_add_primeGenerator_add_groundPotential (a i) (a j)).2
  change ⟪(a i).val.snd, (a j).val.snd⟫_ℝ - ⟪(a i).val.fst, (a j).val.fst⟫_ℝ =
    ⟪(fullGroundEquiv (a i)).val.snd, (fullGroundEquiv (a j)).val.snd⟫_ℝ +
      ⟪primeGenerator (a i).val.fst, (a j).val.fst⟫_ℝ +
      ⟪groundPotentialOperator (a i).val.fst - (a i).val.fst, (a j).val.fst⟫_ℝ
  rw [inner_sub_left]
  linarith

/-- **Diagonal `sourceEnergy` Vanishing Bound**:
for any finite packet `a : ι → SourceGraph`, the difference between the full packet energy
`sourceEnergy (∑ i ∈ S, a i)` and its purely off-diagonal interaction `offDiagSourcePairSum S a`
is bounded in absolute value by the quadratic diagonal graph cost `∑ i ∈ S, ‖a i‖ ^ 2`. -/
theorem abs_sourceEnergy_sum_sub_offDiag_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → SourceGraph) :
    |sourceEnergy (∑ i ∈ S, a i) - offDiagSourcePairSum S a| ≤
      ∑ i ∈ S, ‖a i‖ ^ 2 := by
  have h := sourceEnergy_sum_eq_diag_add_offDiag S a
  have hsub : sourceEnergy (∑ i ∈ S, a i) - offDiagSourcePairSum S a =
      ∑ i ∈ S, sourceEnergy (a i) := by linarith
  rw [hsub]
  calc |∑ i ∈ S, sourceEnergy (a i)|
      ≤ ∑ i ∈ S, |sourceEnergy (a i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ‖a i‖ ^ 2 := Finset.sum_le_sum fun i _ => abs_sourceEnergy_le_norm_sq (a i)

/-- **Diagonal Bounded-Operator Vanishing Bound**:
for any `T : MassSpace →L[ℝ] MassSpace` and finite packet `a : ι → SourceGraph`,
`|∑ i ∈ S, ⟪T (a i).val.fst, (a i).val.fst⟫_ℝ| ≤ ‖T‖ * ∑ i ∈ S, ‖a i‖ ^ 2`
and
`|⟪T (∑ i ∈ S, a i).val.fst, (∑ i ∈ S, a i).val.fst⟫_ℝ - offDiagOperatorSum T S a| ≤ ‖T‖ * ∑ i ∈ S, ‖a i‖ ^ 2`. -/
theorem abs_inner_clm_sum_fst_sub_offDiag_le {ι : Type*} [DecidableEq ι]
    (T : MassSpace →L[ℝ] MassSpace) (S : Finset ι) (a : ι → SourceGraph) :
    |∑ i ∈ S, ⟪T (a i).val.fst, (a i).val.fst⟫_ℝ| ≤ ‖T‖ * ∑ i ∈ S, ‖a i‖ ^ 2 ∧
      |⟪T (∑ i ∈ S, a i).val.fst, (∑ i ∈ S, a i).val.fst⟫_ℝ - offDiagOperatorSum T S a| ≤
        ‖T‖ * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  have hdiag : |∑ i ∈ S, ⟪T (a i).val.fst, (a i).val.fst⟫_ℝ| ≤ ‖T‖ * ∑ i ∈ S, ‖a i‖ ^ 2 := by
    calc |∑ i ∈ S, ⟪T (a i).val.fst, (a i).val.fst⟫_ℝ|
        ≤ ∑ i ∈ S, |⟪T (a i).val.fst, (a i).val.fst⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S, ‖T‖ * ‖a i‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := abs_inner_clm_fst_le_norm_mul T (a i) (a i)
        linarith [show ‖T‖ * ‖a i‖ * ‖a i‖ = ‖T‖ * ‖a i‖ ^ 2 by ring]
      _ = ‖T‖ * ∑ i ∈ S, ‖a i‖ ^ 2 := (Finset.mul_sum S (fun i => ‖a i‖ ^ 2) ‖T‖).symm
  have h := inner_clm_sum_fst_eq_diag_add_offDiag T S a
  have hsub : ⟪T (∑ i ∈ S, a i).val.fst, (∑ i ∈ S, a i).val.fst⟫_ℝ - offDiagOperatorSum T S a =
      ∑ i ∈ S, ⟪T (a i).val.fst, (a i).val.fst⟫_ℝ := by linarith
  exact ⟨hdiag, by rwa [hsub]⟩

/-- **Diagonal `stationaryEnergy` Vanishing Bound**:
for any finite packet `a : ι → SourceGraph`,
`0 ≤ ∑ i ∈ S, stationaryEnergy (thetaProduct (a i).val.fst)` and
`(∑ i ∈ S, stationaryEnergy (thetaProduct (a i).val.fst)) ≤ (1 + ‖groundPerturbation‖) * ∑ i ∈ S, ‖a i‖ ^ 2`. -/
theorem sum_stationaryEnergy_le_sum_norm_sq {ι : Type*}
    (S : Finset ι) (a : ι → SourceGraph) :
    0 ≤ (∑ i ∈ S, stationaryEnergy (thetaProduct (a i).val.fst)) ∧
      (∑ i ∈ S, stationaryEnergy (thetaProduct (a i).val.fst)) ≤
        (1 + ‖groundPerturbation‖) * ∑ i ∈ S, ‖a i‖ ^ 2 := by
  refine ⟨Finset.sum_nonneg fun i _ => (stationaryEnergy_nonneg_and_le_norm_sq (a i)).1, ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => (stationaryEnergy_nonneg_and_le_norm_sq (a i)).2

/-! ## Section 3: Purely Off-Diagonal Terminal-Prime Clock Realization of `sourceEnergy`, `stationaryEnergy`, and Operator Forms -/

/-- **Purely Off-Diagonal Terminal-Prime Clock Realization of `sourceEnergy` and Operator Forms**:
for every `q : SourceGraph`, every continuous linear operator `T : MassSpace →L[ℝ] MassSpace`,
every depth threshold `T₀ : ℝ`, and every `0 < ε`, there exists a smooth cutoff index `k : ℕ`
such that for all sufficiently large `N : ℕ`, there exists a finite set `S : Finset ℕ` of
distinct primes `p > √N` with `log(N / p) > T₀` such that for `a_p = canonicalPrimeGraphClockAtom k N p`:
1. `‖(∑ p ∈ S, a_p) - q‖ < ε` and `∑ p ∈ S, ‖a_p‖ ^ 2 < ε`,
2. `|offDiagSourcePairSum S a - sourceEnergy q| ≤ ε + ε ^ 2 + 2 * ε * ‖q‖`,
3. `|offDiagOperatorSum T S a - ⟪T q.val.fst, q.val.fst⟫_ℝ| ≤ ‖T‖ * (ε + ε ^ 2 + 2 * ε * ‖q‖)`,
4. `|∑ p ∈ S, ⟪groundPotentialOperator a_p.val.fst, a_p.val.fst⟫_ℝ| ≤ ‖groundPotentialOperator‖ * ε`,
5. `|∑ p ∈ S, ⟪primeShiftOperator a_p.val.fst, a_p.val.fst⟫_ℝ| ≤ ‖primeShiftOperator‖ * ε`,
6. `∑ p ∈ S, stationaryEnergy (thetaProduct a_p.val.fst) ≤ (1 + ‖groundPerturbation‖) * ε`. -/
theorem exists_cutoff_eventually_offDiag_primeClock_realization
    (q : SourceGraph) (T : MassSpace →L[ℝ] MassSpace) (T₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ Real.sqrt N < p ∧ T₀ < Real.log ((N : ℝ) / p)) ∧
      ‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - q‖ < ε ∧
      (∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2) < ε ∧
      |offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N) - sourceEnergy q| ≤
        ε + ε ^ 2 + 2 * ε * ‖q‖ ∧
      |offDiagOperatorSum T S (canonicalPrimeGraphClockAtom k N) - ⟪T q.val.fst, q.val.fst⟫_ℝ| ≤
        ‖T‖ * (ε + ε ^ 2 + 2 * ε * ‖q‖) ∧
      |∑ p ∈ S,
          ⟪groundPotentialOperator (canonicalPrimeGraphClockAtom k N p).val.fst,
            (canonicalPrimeGraphClockAtom k N p).val.fst⟫_ℝ| ≤
        ‖groundPotentialOperator‖ * ε ∧
      |∑ p ∈ S,
          ⟪primeShiftOperator (canonicalPrimeGraphClockAtom k N p).val.fst,
            (canonicalPrimeGraphClockAtom k N p).val.fst⟫_ℝ| ≤
        ‖primeShiftOperator‖ * ε ∧
      (∑ p ∈ S,
          stationaryEnergy (thetaProduct (canonicalPrimeGraphClockAtom k N p).val.fst)) ≤
        (1 + ‖groundPerturbation‖) * ε := by
  obtain ⟨k, hk⟩ := exists_cutoff_eventually_criticalPrimeGraphClock_realization q T₀ hε
  refine ⟨k, ?_⟩
  filter_upwards [hk] with N hN
  obtain ⟨S, hS, happ, hdiag⟩ := hN
  set a := canonicalPrimeGraphClockAtom k N
  set P := ∑ p ∈ S, a p
  have hP_sq : ‖P - q‖ ^ 2 ≤ ε ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) happ.le 2
  have hP_lin : 2 * ‖P - q‖ * ‖q‖ ≤ 2 * ε * ‖q‖ := by
    nlinarith [happ.le, norm_nonneg q]
  have hE_diff : |sourceEnergy P - sourceEnergy q| ≤ ε ^ 2 + 2 * ε * ‖q‖ :=
    (abs_sourceEnergy_sub_le P q).trans (by linarith)
  have hE_diag : |offDiagSourcePairSum S a - sourceEnergy P| ≤ ε := by
    rw [abs_sub_comm]
    exact (abs_sourceEnergy_sum_sub_offDiag_le S a).trans hdiag.le
  have hE_off : |offDiagSourcePairSum S a - sourceEnergy q| ≤ ε + ε ^ 2 + 2 * ε * ‖q‖ := by
    calc |offDiagSourcePairSum S a - sourceEnergy q|
        = |(offDiagSourcePairSum S a - sourceEnergy P) + (sourceEnergy P - sourceEnergy q)| := by
          congr 1; ring
      _ ≤ |offDiagSourcePairSum S a - sourceEnergy P| + |sourceEnergy P - sourceEnergy q| :=
          abs_add_le _ _
      _ ≤ ε + (ε ^ 2 + 2 * ε * ‖q‖) := add_le_add hE_diag hE_diff
      _ = ε + ε ^ 2 + 2 * ε * ‖q‖ := by ring
  have hT_diff : |⟪T P.val.fst, P.val.fst⟫_ℝ - ⟪T q.val.fst, q.val.fst⟫_ℝ| ≤
      ‖T‖ * (ε ^ 2 + 2 * ε * ‖q‖) :=
    (abs_inner_clm_fst_sub_le T P q).trans
      (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg T))
  have hT_diag : |offDiagOperatorSum T S a - ⟪T P.val.fst, P.val.fst⟫_ℝ| ≤ ‖T‖ * ε := by
    rw [abs_sub_comm]
    exact (abs_inner_clm_sum_fst_sub_offDiag_le T S a).2.trans
      (mul_le_mul_of_nonneg_left hdiag.le (norm_nonneg T))
  have hT_off : |offDiagOperatorSum T S a - ⟪T q.val.fst, q.val.fst⟫_ℝ| ≤
      ‖T‖ * (ε + ε ^ 2 + 2 * ε * ‖q‖) := by
    calc |offDiagOperatorSum T S a - ⟪T q.val.fst, q.val.fst⟫_ℝ|
        = |(offDiagOperatorSum T S a - ⟪T P.val.fst, P.val.fst⟫_ℝ) +
            (⟪T P.val.fst, P.val.fst⟫_ℝ - ⟪T q.val.fst, q.val.fst⟫_ℝ)| := by
          congr 1; ring
      _ ≤ |offDiagOperatorSum T S a - ⟪T P.val.fst, P.val.fst⟫_ℝ| +
            |⟪T P.val.fst, P.val.fst⟫_ℝ - ⟪T q.val.fst, q.val.fst⟫_ℝ| := abs_add_le _ _
      _ ≤ ‖T‖ * ε + ‖T‖ * (ε ^ 2 + 2 * ε * ‖q‖) := add_le_add hT_diag hT_diff
      _ = ‖T‖ * (ε + ε ^ 2 + 2 * ε * ‖q‖) := by ring
  have hgp_diag :
      |∑ p ∈ S, ⟪groundPotentialOperator (a p).val.fst, (a p).val.fst⟫_ℝ| ≤
        ‖groundPotentialOperator‖ * ε :=
    (abs_inner_clm_sum_fst_sub_offDiag_le groundPotentialOperator S a).1.trans
      (mul_le_mul_of_nonneg_left hdiag.le (norm_nonneg _))
  have hps_diag :
      |∑ p ∈ S, ⟪primeShiftOperator (a p).val.fst, (a p).val.fst⟫_ℝ| ≤
        ‖primeShiftOperator‖ * ε :=
    (abs_inner_clm_sum_fst_sub_offDiag_le primeShiftOperator S a).1.trans
      (mul_le_mul_of_nonneg_left hdiag.le (norm_nonneg _))
  have hstat_diag :
      (∑ p ∈ S, stationaryEnergy (thetaProduct (a p).val.fst)) ≤
        (1 + ‖groundPerturbation‖) * ε :=
    (sum_stationaryEnergy_le_sum_norm_sq S a).2.trans
      (mul_le_mul_of_nonneg_left hdiag.le (by positivity))
  exact ⟨S, hS, happ, hdiag, hE_off, hT_off, hgp_diag, hps_diag, hstat_diag⟩

/-! ## Section 4: Pointwise Prime-Ratio Lag Identity and Off-Diagonal Prime-Clock Negativity for Above-Threshold Eigenvectors -/

/-- **Scale-Free Prime-Ratio Log-Lag Cancellation Identity**:
for any `N, p, p' : ℕ` with `0 < N`, `0 < p`, `0 < p'` and any `x : ℝ`, the common scale `N`
cancels identically between the two prime clock arguments `log(N / p) - x` and `log(N / p') - x`,
leaving the pure prime-ratio lag `log(p' / p)`. -/
theorem primeClock_log_lag_identity {N p p' : ℕ} (hN : 0 < N) (hp : 0 < p) (hp' : 0 < p')
    (x : ℝ) :
    (Real.log ((N : ℝ) / p) - x) - (Real.log ((N : ℝ) / p') - x) =
        Real.log ((p' : ℝ) / p) ∧
      Real.log ((N : ℝ) / p) - x =
        (Real.log ((N : ℝ) / p') - x) + Real.log ((p' : ℝ) / p) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hp'0 : (0 : ℝ) < p' := by exact_mod_cast hp'
  have h1 : (Real.log ((N : ℝ) / p) - x) - (Real.log ((N : ℝ) / p') - x) =
      Real.log ((p' : ℝ) / p) := by
    rw [Real.log_div hN0.ne' hp0.ne', Real.log_div hN0.ne' hp'0.ne',
      Real.log_div hp'0.ne' hp0.ne']
    ring
  exact ⟨h1, by linarith⟩

/-- Almost-everywhere vertex formula for `canonicalPrimeGraphClockAtom k N p` in `MassSpace`. -/
theorem canonicalPrimeGraphClockAtom_fst_ae (k N p : ℕ) :
    (canonicalPrimeGraphClockAtom k N p).val.fst =ᵐ[massMeasure]
      fun x => (Real.sqrt N / p) * cutoff k x *
        criticalAbelLogProfile (Real.log ((N : ℝ) / p) - x) := by
  have hbv := GaloisForLFunctions.HTGeometry.boundedVariationOn_of_contDiff_compact
    ((cutoff_contDiff k).of_le (by norm_num)) (cutoff_hasCompactSupport k)
  have hsrc := criticalClockGraph_source (cutoff k) hbv (Real.log ((N : ℝ) / p))
  have hsmul :
      (canonicalPrimeGraphClockAtom k N p).val.fst =
        (Real.sqrt N / p) •
          (criticalClockGraph (cutoff k) hbv (Real.log ((N : ℝ) / p))).val.fst := rfl
  rw [hsmul]
  filter_upwards [Lp.coeFn_smul (Real.sqrt N / p)
    (criticalClockGraph (cutoff k) hbv (Real.log ((N : ℝ) / p))).val.fst, hsrc] with x hx1 hx2
  rw [hx1, Pi.smul_apply, smul_eq_mul, hx2]
  unfold criticalClockCutoff
  ring

/-- **Pointwise Two-Prime Clock Product Formula with Prime-Ratio Lag `log(p' / p)`**:
for any `k, N, p, p' : ℕ` with `0 < N`, `0 < p`, `0 < p'`, for `massMeasure`-almost every `x : ℝ`,
`(canonicalPrimeGraphClockAtom k N p).val.fst x * (canonicalPrimeGraphClockAtom k N p').val.fst x = ((N : ℝ) / ((p : ℝ) * p')) * (cutoff k x) ^ 2 * criticalAbelLogProfile ((Real.log ((N : ℝ) / p') - x) + Real.log ((p' : ℝ) / p)) * criticalAbelLogProfile (Real.log ((N : ℝ) / p') - x)`. -/
theorem canonicalPrimeGraphClockAtom_fst_mul_ae {k N p p' : ℕ}
    (hN : 0 < N) (hp : 0 < p) (hp' : 0 < p') :
    (fun x => (canonicalPrimeGraphClockAtom k N p).val.fst x *
        (canonicalPrimeGraphClockAtom k N p').val.fst x) =ᵐ[massMeasure]
      fun x => ((N : ℝ) / ((p : ℝ) * p')) * (cutoff k x) ^ 2 *
        criticalAbelLogProfile ((Real.log ((N : ℝ) / p') - x) + Real.log ((p' : ℝ) / p)) *
        criticalAbelLogProfile (Real.log ((N : ℝ) / p') - x) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN0
  filter_upwards [canonicalPrimeGraphClockAtom_fst_ae k N p,
    canonicalPrimeGraphClockAtom_fst_ae k N p'] with x hxp hxp'
  rw [hxp, hxp', (primeClock_log_lag_identity hN hp hp' x).2]
  calc (Real.sqrt ↑N / ↑p * cutoff k x *
        criticalAbelLogProfile (Real.log (↑N / ↑p') - x + Real.log (↑p' / ↑p))) *
      (Real.sqrt ↑N / ↑p' * cutoff k x *
        criticalAbelLogProfile (Real.log (↑N / ↑p') - x))
      = ((Real.sqrt ↑N * Real.sqrt ↑N) / ((p : ℝ) * p')) * (cutoff k x) ^ 2 *
        criticalAbelLogProfile (Real.log (↑N / ↑p') - x + Real.log (↑p' / ↑p)) *
        criticalAbelLogProfile (Real.log (↑N / ↑p') - x) := by ring
    _ = ((N : ℝ) / ((p : ℝ) * p')) * (cutoff k x) ^ 2 *
        criticalAbelLogProfile (Real.log (↑N / ↑p') - x + Real.log (↑p' / ↑p)) *
        criticalAbelLogProfile (Real.log (↑N / ↑p') - x) := by rw [hsq]

/-- **Purely Off-Diagonal Prime-Clock Negativity for Any Above-Threshold Eigenvector (`1 / 2 < μ`)**:
for every nonzero eigenvector `resolvent w = μ • w` with `1 / 2 < μ`, setting `q = rieszLift w`
and any depth threshold `T₀ : ℝ`, there exists a smooth cutoff index `k : ℕ` such that for all
sufficiently large `N : ℕ`, there exists a finite set `S : Finset ℕ` of distinct primes `p > √N`
with `log(N / p) > T₀` whose purely off-diagonal prime-clock interaction is strictly negative:
`offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N) < ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 < 0`. -/
theorem exists_cutoff_eventually_offDiag_primeClock_neg_of_eigenvector_gt_half
    {μ : ℝ} (hμ : 1 / 2 < μ) {w : MassSpace} (hw : w ≠ 0) (heig : resolvent w = μ • w)
    (T₀ : ℝ) :
    let q := rieszLift w
    ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 < 0 ∧
      ∃ k : ℕ, ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
        (∀ p ∈ S, p.Prime ∧ Real.sqrt N < p ∧ T₀ < Real.log ((N : ℝ) / p)) ∧
        ‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - q‖ <
          ((2 * μ - 1) / (4 * μ)) * ‖q.val.fst‖ ^ 2 / (2 + 2 * ‖q‖) ∧
        (∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2) <
          ((2 * μ - 1) / (4 * μ)) * ‖q.val.fst‖ ^ 2 / (2 + 2 * ‖q‖) ∧
        offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N) <
          ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 := by
  intro q
  have hμ0 : 0 < μ := by linarith
  have hq_fst : q.val.fst = μ • w := heig
  have hq0 : q.val.fst ≠ 0 := by
    rw [hq_fst]
    exact smul_ne_zero hμ0.ne' hw
  have hq_sq_pos : 0 < ‖q.val.fst‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq0)
  have hE_eq : sourceEnergy q = ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2 := by
    have hE : sourceEnergy q = ‖q.val.snd‖ ^ 2 - ‖q.val.fst‖ ^ 2 := rfl
    rw [hE, norm_snd_sq_rieszLift_of_eigenvector hμ0.ne' heig]
    field_simp [hμ0.ne']
    ring
  have hcoef_neg : (1 - 2 * μ) / (2 * μ) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hhalf_neg : ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hcoef_neg hq_sq_pos
  set δ := ((2 * μ - 1) / (4 * μ)) * ‖q.val.fst‖ ^ 2
  have hδ_pos : 0 < δ :=
    mul_pos (div_pos (by linarith) (by linarith)) hq_sq_pos
  have hden_pos : 0 < 2 + 2 * ‖q‖ := by linarith [norm_nonneg q]
  set ε := min 1 (δ / (2 + 2 * ‖q‖))
  have hε_pos : 0 < ε := lt_min zero_lt_one (div_pos hδ_pos hden_pos)
  have hε_le_one : ε ≤ 1 := min_le_left _ _
  have hε_le_div : ε ≤ δ / (2 + 2 * ‖q‖) := min_le_right _ _
  have hε_bound : ε + ε ^ 2 + 2 * ε * ‖q‖ ≤ δ := by
    have h1 : ε ^ 2 ≤ ε := by nlinarith [hε_pos, hε_le_one]
    have h2 : ε * (2 + 2 * ‖q‖) ≤ δ := (le_div_iff₀ hden_pos).mp hε_le_div
    nlinarith
  obtain ⟨k, hk⟩ := exists_cutoff_eventually_offDiag_primeClock_realization
    q (ContinuousLinearMap.id ℝ MassSpace) T₀ hε_pos
  refine ⟨hhalf_neg, k, ?_⟩
  filter_upwards [hk] with N hN
  obtain ⟨S, hS, happ, hdiag, hE_off, _, _, _, _⟩ := hN
  refine ⟨S, hS, happ.trans_le hε_le_div, hdiag.trans_le hε_le_div, ?_⟩
  have hupper := (abs_le.mp hE_off).2
  have hsum : sourceEnergy q + δ = ((3 * (1 - 2 * μ)) / (4 * μ)) * ‖q.val.fst‖ ^ 2 := by
    rw [hE_eq]
    dsimp [δ]
    field_simp [hμ0.ne']
    ring
  have hstrict : ((3 * (1 - 2 * μ)) / (4 * μ)) * ‖q.val.fst‖ ^ 2 <
      ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 := by
    have hdiff : ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 -
        ((3 * (1 - 2 * μ)) / (4 * μ)) * ‖q.val.fst‖ ^ 2 = δ := by
      dsimp [δ]
      field_simp [hμ0.ne']
      ring
    linarith
  linarith

/-- **Off-Diagonal Prime-Clock Nonnegativity Criterion for `sourceEnergy q ≥ 0` and `μ ≤ 1 / 2`**:
if for every `0 < ε`, there exist `k, N : ℕ` and a finite set `S : Finset ℕ` such that
`‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - q‖ < ε`,
`∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2 < ε`, and
`0 ≤ offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N)`,
then `0 ≤ sourceEnergy q`. When `q = rieszLift w` for a nonzero eigenvector `resolvent w = μ • w`
(`0 < μ`), this forces `μ ≤ 1 / 2`. -/
theorem sourceEnergy_nonneg_of_offDiag_primeClock_nonneg (q : SourceGraph)
    (h : ∀ ε > 0, ∃ k N : ℕ, ∃ S : Finset ℕ,
      ‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - q‖ < ε ∧
      (∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2) < ε ∧
      0 ≤ offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N)) :
    0 ≤ sourceEnergy q := by
  by_contra hneg
  push Not at hneg
  set δ := -sourceEnergy q / 2 with hδ_def
  have hδ : 0 < δ := by linarith
  have hden : 0 < 2 + 2 * ‖q‖ := by linarith [norm_nonneg q]
  set ε := min 1 (δ / (2 + 2 * ‖q‖))
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hδ hden)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε * (2 + 2 * ‖q‖) ≤ δ := (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨k, N, S, happ, hdiag, hnn⟩ := h ε hε
  set a := canonicalPrimeGraphClockAtom k N
  set P := ∑ p ∈ S, a p
  have hP_sq : ‖P - q‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) happ.le 2
  have hP_lin : 2 * ‖P - q‖ * ‖q‖ ≤ 2 * ε * ‖q‖ := by nlinarith [happ.le, norm_nonneg q]
  have hE_diff : |sourceEnergy P - sourceEnergy q| ≤ ε ^ 2 + 2 * ε * ‖q‖ :=
    (abs_sourceEnergy_sub_le P q).trans (by linarith)
  have hE_diag : |offDiagSourcePairSum S a - sourceEnergy P| ≤ ε := by
    rw [abs_sub_comm]
    exact (abs_sourceEnergy_sum_sub_offDiag_le S a).trans hdiag.le
  have hE_off : offDiagSourcePairSum S a - sourceEnergy q ≤ ε + ε ^ 2 + 2 * ε * ‖q‖ := by
    have h1 := (abs_le.mp hE_diag).2
    have h2 := (abs_le.mp hE_diff).2
    linarith
  have hε_bound : ε + ε ^ 2 + 2 * ε * ‖q‖ ≤ δ := by
    have hsq : ε ^ 2 ≤ ε := by nlinarith [hε, hε1]
    nlinarith
  linarith

theorem eigenvalue_le_one_half_of_offDiag_primeClock_nonneg
    {μ : ℝ} (hμ : 0 < μ) {w : MassSpace} (hw : w ≠ 0) (heig : resolvent w = μ • w)
    (h : ∀ ε > 0, ∃ k N : ℕ, ∃ S : Finset ℕ,
      ‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - rieszLift w‖ < ε ∧
      (∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2) < ε ∧
      0 ≤ offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N)) :
    μ ≤ 1 / 2 := by
  have hE := sourceEnergy_nonneg_of_offDiag_primeClock_nonneg (rieszLift w) h
  by_contra hgt
  push Not at hgt
  have hneg := (exists_cutoff_eventually_offDiag_primeClock_neg_of_eigenvector_gt_half
    hgt hw heig 0).1
  have hE_eq : sourceEnergy (rieszLift w) = ((1 - 2 * μ) / μ) * ‖(rieszLift w).val.fst‖ ^ 2 := by
    have h1 : sourceEnergy (rieszLift w) =
        ‖(rieszLift w).val.snd‖ ^ 2 - ‖(rieszLift w).val.fst‖ ^ 2 := rfl
    rw [h1, norm_snd_sq_rieszLift_of_eigenvector hμ.ne' heig]
    field_simp [hμ.ne']
    ring
  have h2 : sourceEnergy (rieszLift w) =
      2 * (((1 - 2 * μ) / (2 * μ)) * ‖(rieszLift w).val.fst‖ ^ 2) := by
    rw [hE_eq]
    field_simp [hμ.ne']
  linarith

end GaloisForLFunctions.BiScaleUncertainty
