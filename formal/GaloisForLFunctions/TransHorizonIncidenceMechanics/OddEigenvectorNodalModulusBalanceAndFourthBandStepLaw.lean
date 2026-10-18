import GaloisForLFunctions.TransHorizonIncidenceMechanics.ThirdBandCompositeStepAndLinearL2EnergyBounds
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FourthBandEnvelopeAndSharpFiveHorizonBoundary
import GaloisForLFunctions.RHTower.CHMDBalancedNodalGraphAndGroundPerturbationResolvent
import GaloisForLFunctions.RHTower.CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure

/-!
# Odd-Eigenvector Nodal-Modulus Balance, Half-Line Cross-Jump Exclusion, and the Fourth-Band $L^2$ Step Law

This module advances **Step 3 (Sub-routes 3A and 3C)** of the CHMD closure programme
(`docs/reports/TransHorizonIncidenceMechanics/CHMD-programme.md`):

1. **Automatic Mass-Balancing of `absGraph` on the Odd Sector (`Sub-route 3A`)**:
   - For every odd graph vector `p : SourceGraph` (`reflectGraph p = -p`), its positive and negative
     nodal lobes carry equal vertex and edge norms (`(1 / 2) * ‖p.val.fst‖ ^ 2` and
     `(1 / 2) * ‖p.val.snd‖ ^ 2 + sourcePair (posGraph p) (negGraph p)`), so
     `balancedNodalGraph p = ((1 / 2) * ‖p.val.fst‖ ^ 2) • absGraph p` (`odd_balancedNodalGraph_eq_smul_absGraph`)
     and `p` is simultaneously orthogonal to `absGraph p` in `MassSpace`, `EdgeSpace`, `SourceGraph`,
     and with respect to `sourcePair` (`odd_absGraph_simultaneous_orthogonality`).

2. **Exact `sourceEnergy (absGraph q)` Bilateral Cross-Jump Identity & `μ = 1/2` Exclusion Criteria**:
   - For any eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
     $$\operatorname{sourceEnergy}(\operatorname{absGraph} q) -
       4\operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q)
       = \frac{1 - 2\mu}{\mu}\|q.\text{fst}\|^2$$
     (`eigenvector_sourceEnergy_absGraph_sub_four_sourcePair_eq`).
   - Consequently, any nonzero eigenvector with $\mu > 1/2$ forces
     $\operatorname{sourceEnergy}(\operatorname{absGraph} q) < 4\operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q) \le 0$
     (`eigenvector_gt_half_sourceEnergy_absGraph_lt`), yielding an exact equivalence for
     `RiemannHypothesis` (`riemannHypothesis_iff_forall_odd_eigenvector_absGraph_energy_ge_four_sourcePair`)
     and the critical-threshold $\mu_{\max} = 1/2$ `oneL`-defect exclusion theorem
     (`riemannHypothesis_of_odd_eigenvector_oneL_defect_le_neg_four_sourcePair`).

3. **Centered $(B - 2)$ Buchstab $L^2$ Step Identity & Four-Band Linear Energy Bound (`Sub-route 3C`)**:
   - Isolating the $q = 1$ quotient ($s_{n,\mu}(n + 1) = -\mu(n + 1)$) in the single-horizon step
     gives the universal centered identity
     $$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu)
       = (B - 2)\mu(n + 1)^2 + 2\mu(n + 1)\sum_{q \in \operatorname{Icc} 2 B} s_{n,\mu}(q(n + 1))$$
     for $B = \lfloor M / (n + 1) \rfloor \ge 1$ (`sieveL2PrefixEnergy_moebiusReal_succ_sub_eq_centered`).
   - Combining this with the sharp $5N$ unit envelope $|s_{n,\mu}(k)| \le 1$ ($2 \le k \le 5n$)
     proves that every downward step with $B(n + 1) \le 5n$ satisfies
     $\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+1}(M; \mu) \le B\mu(n + 1)^2$
     (`sieveL2PrefixEnergy_moebiusReal_sub_succ_le_of_le_five_mul`), yielding the unconditional
     four-band linear upper bound $\mathcal{E}_N(M; \mu) \le 1 + 4(M - N)$ across $4 \le N \le M < 5(N + 1)$
     (`sieveL2PrefixEnergy_moebiusReal_four_band_le`).
-/

open Finset MeasureTheory Set
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open scoped InnerProductSpace BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Automatic Mass-Balancing of `absGraph` on the Odd Sector -/

/-- For every odd graph vector `p : SourceGraph` (`reflectGraph p = -p`), its balanced nodal graph
`balancedNodalGraph p` is a scalar multiple of its modulus graph `absGraph p`:
`balancedNodalGraph p = ((1 / 2) * ‖p.val.fst‖ ^ 2) • absGraph p`.
(Classification: New formulation.) -/
theorem odd_balancedNodalGraph_eq_smul_absGraph {p : SourceGraph} (hp : reflectGraph p = -p) :
    balancedNodalGraph p = ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • absGraph p := by
  obtain ⟨hf_pos, hf_neg⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hp
  unfold balancedNodalGraph
  rw [hf_pos, hf_neg, ← smul_add, posGraph_add_negGraph]

/-- For every odd graph vector `p : SourceGraph` (`reflectGraph p = -p`), `p` and `absGraph p` are
simultaneously orthogonal in `MassSpace`, `EdgeSpace`, `SourceGraph`, and with respect to `sourcePair`.
(Classification: New formulation.) -/
theorem odd_absGraph_simultaneous_orthogonality {p : SourceGraph} (hp : reflectGraph p = -p) :
    ⟪p.val.fst, (absGraph p).val.fst⟫_ℝ = 0 ∧
      ⟪p.val.snd, (absGraph p).val.snd⟫_ℝ = 0 ∧
      ⟪p, absGraph p⟫_ℝ = 0 ∧
      sourcePair p (absGraph p) = 0 := by
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_sub_negGraph p).symm
  have hadd : (absGraph p).val.fst = (posGraph p).val.fst + (negGraph p).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_add_negGraph p).symm
  obtain ⟨hf_pos, hf_neg⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hp
  obtain ⟨hs_pos, hs_neg⟩ := norm_posGraph_and_negGraph_snd_sq_of_odd hp
  have hfst : ⟪p.val.fst, (absGraph p).val.fst⟫_ℝ = 0 := by
    rw [hsub, hadd, inner_sub_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hf_pos, hf_neg,
      real_inner_comm (negGraph p).val.fst (posGraph p).val.fst]
    ring
  have hsnd : ⟪p.val.snd, (absGraph p).val.snd⟫_ℝ = 0 := by
    rw [inner_self_absGraph_snd, hs_pos, hs_neg, sub_self]
  have hgraph : ⟪p, absGraph p⟫_ℝ = 0 := by
    rw [graph_inner, hfst, hsnd, add_zero]
  have hpair : sourcePair p (absGraph p) = 0 := by
    change ⟪p.val.snd, (absGraph p).val.snd⟫_ℝ - ⟪p.val.fst, (absGraph p).val.fst⟫_ℝ = 0
    rw [hsnd, hfst, sub_self]
  exact ⟨hfst, hsnd, hgraph, hpair⟩

/-! ## §2. Exact `sourceEnergy (absGraph q)` Bilateral Cross-Jump Identity & `μ = 1/2` Exclusion Criteria -/

/-- **Exact `sourceEnergy (absGraph q)` and Bilateral Cross-Jump Identity for Any Eigenvector
(`eigenvector_sourceEnergy_absGraph_sub_four_sourcePair_eq`):**
For every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`:
1. `sourceEnergy (absGraph q) - 4 * sourcePair (posGraph q) (negGraph q) = ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2`
2. `sourceEnergy (absGraph q) - 4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + 4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ = ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2`.
(Classification: Candidate new theorem.) -/
theorem eigenvector_sourceEnergy_absGraph_sub_four_sourcePair_eq {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    sourceEnergy (absGraph q) - 4 * sourcePair (posGraph q) (negGraph q) =
        ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2 ∧
      sourceEnergy (absGraph q) -
          4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
          4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ =
        ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2 := by
  intro q
  obtain ⟨h1, h2⟩ := norm_absGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  have hE : sourceEnergy (absGraph q) = ‖(absGraph q).val.snd‖ ^ 2 - ‖(absGraph q).val.fst‖ ^ 2 := rfl
  have hnorm : ‖(absGraph q).val.fst‖ ^ 2 = ‖q.val.fst‖ ^ 2 := norm_absGraph_fst_sq q
  have hid : ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 - ‖q.val.fst‖ ^ 2 =
      ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2 := by
    field_simp [hμ]
    ring
  exact ⟨by linarith, by linarith⟩

/-- Any nonzero eigenvector `resolvent w = μ • w` with `1 / 2 < μ` forces its modulus graph
`absGraph (rieszLift w)` to satisfy
`sourceEnergy (absGraph (rieszLift w)) < 4 * sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) ≤ 0`.
(Classification: Corollary.) -/
theorem eigenvector_gt_half_sourceEnergy_absGraph_lt {μ : ℝ} (hμ : 1 / 2 < μ)
    {w : MassSpace} (hw0 : w ≠ 0) (heig : resolvent w = μ • w) :
    let q := rieszLift w
    sourceEnergy (absGraph q) < 4 * sourcePair (posGraph q) (negGraph q) ∧
      4 * sourcePair (posGraph q) (negGraph q) ≤ 0 := by
  intro q
  have hμ_pos : 0 < μ := by linarith
  have hq_fst : q.val.fst = μ • w := heig
  have hq_pos : 0 < ‖q.val.fst‖ ^ 2 := by
    rw [hq_fst, norm_smul, Real.norm_of_nonneg hμ_pos.le, mul_pow]
    exact mul_pos (sq_pos_of_pos hμ_pos) (sq_pos_of_pos (norm_pos_iff.mpr hw0))
  have hcoeff_neg : (1 - 2 * μ) / μ < 0 :=
    div_neg_of_neg_of_pos (by linarith) hμ_pos
  have hrhs_neg : ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hcoeff_neg hq_pos
  have h1 := (eigenvector_sourceEnergy_absGraph_sub_four_sourcePair_eq hμ_pos.ne' heig).1
  obtain ⟨hstat, hprime, _, _⟩ := stationary_and_primeShift_le_neg_sourcePair_posGraph_negGraph q
  have hdecomp := neg_four_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift q
  exact ⟨by linarith, by linarith⟩

/-- **Modulus-Energy vs. Cross-Jump Equivalence for `RiemannHypothesis`
(`riemannHypothesis_iff_forall_odd_eigenvector_absGraph_energy_ge_four_sourcePair`):**
`RiemannHypothesis` holds if and only if for every odd eigenvector $w \ne 0$ with
$\mu > 1 / 2$ and $q = \operatorname{rieszLift} w$,
$$4\operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q)
  \le \operatorname{sourceEnergy}(\operatorname{absGraph} q).$$
(Classification: Candidate new theorem.) -/
theorem riemannHypothesis_iff_forall_odd_eigenvector_absGraph_energy_ge_four_sourcePair :
    RiemannHypothesis ↔
      ∀ (μ : ℝ) (w : MassSpace),
        1 / 2 < μ → w ≠ 0 → reflectMass w = -w → resolvent w = μ • w →
          4 * sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) ≤
            sourceEnergy (absGraph (rieszLift w)) := by
  rw [riemannHypothesis_iff_no_odd_bound_state]
  constructor
  · intro h μ w hμ hw0 hodd heig
    exact (hw0 (h μ w hμ hodd heig)).elim
  · intro h μ w hμ hodd heig
    by_contra hw0
    have hle := h μ w hμ hw0 hodd heig
    have hlt := (eigenvector_gt_half_sourceEnergy_absGraph_lt hμ hw0 heig).1
    linarith

/-- **Critical-Line $\mu_{\max} = 1/2$ `oneL`-Defect Exclusion Theorem for `RiemannHypothesis`
(`riemannHypothesis_of_odd_eigenvector_oneL_defect_le_neg_four_sourcePair`):**
If for every odd eigenvector $w \ne 0$ with $\mu > 1 / 2$ and $p = \operatorname{rieszLift} w$,
its primitive modulus $u_0 = (\operatorname{primGraph}(\operatorname{absGraph} p)).\text{fst}$ satisfies
$\langle \operatorname{resolvent} u_0, u_0 \rangle_{\mathbb{R}} \le \frac{1}{2}\|u_0\|^2$ and its
`oneL`-defect is dominated by the nodal cross-jump penalty:
$$2\langle (\operatorname{absGraph} p).\text{fst}, \text{oneL}\rangle_{\mathbb{R}}^2
  \le -4\operatorname{sourcePair}(\operatorname{posGraph} p, \operatorname{negGraph} p),$$
then `RiemannHypothesis` holds.
(Classification: Candidate new theorem.) -/
theorem riemannHypothesis_of_odd_eigenvector_oneL_defect_le_neg_four_sourcePair
    (hray : ∀ (μ : ℝ) (w : MassSpace),
      1 / 2 < μ → w ≠ 0 → reflectMass w = -w → resolvent w = μ • w →
        ⟪resolvent (primGraph (absGraph (rieszLift w))).val.fst,
            (primGraph (absGraph (rieszLift w))).val.fst⟫_ℝ ≤
          (1 / 2 : ℝ) * ‖(primGraph (absGraph (rieszLift w))).val.fst‖ ^ 2)
    (hdom : ∀ (μ : ℝ) (w : MassSpace),
      1 / 2 < μ → w ≠ 0 → reflectMass w = -w → resolvent w = μ • w →
        2 * ⟪(absGraph (rieszLift w)).val.fst, oneL⟫_ℝ ^ 2 ≤
          -4 * sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w))) :
    RiemannHypothesis := by
  by_contra hnot
  obtain ⟨μ, w, hμ, hw0, hodd, heig⟩ :=
    not_riemannHypothesis_iff_exists_odd_bound_state.mp hnot
  have hμ_pos : 0 < μ := by linarith
  have hhalf_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have hdom' :
      ((1 - (1 / 2 : ℝ)) / (1 / 2 : ℝ)) * (2 * ⟪(absGraph (rieszLift w)).val.fst, oneL⟫_ℝ ^ 2) ≤
        -4 * sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) := by
    have h1 : (1 - (1 / 2 : ℝ)) / (1 / 2 : ℝ) = 1 := by norm_num
    rw [h1, one_mul]
    exact hdom μ w hμ hw0 hodd heig
  have hle : μ ≤ 1 / 2 :=
    eigenvalue_le_of_oneL_defect_le_neg_four_sourcePair hμ_pos hhalf_pos hw0 heig
      (hray μ w hμ hw0 hodd heig) hdom'
  linarith

/-! ## §3. Centered $(B - 2)$ Buchstab $L^2$ Step Identity & Four-Band Linear Energy Bound -/

/-- Splitting off $q = 1$ from `Finset.Icc 1 B` for $B \ge 1$. -/
private theorem sum_Icc_one_eq_add_Icc_two {B : ℕ} (hB : 1 ≤ B) (f : ℕ → ℝ) :
    (∑ q ∈ Finset.Icc 1 B, f q) = f 1 + ∑ q ∈ Finset.Icc 2 B, f q := by
  have hunion : insert 1 (Finset.Icc 2 B) = Finset.Icc 1 B := by
    ext q
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnotmem : (1 : ℕ) ∉ Finset.Icc 2 B := by
    simp only [Finset.mem_Icc]
    omega
  rw [← hunion, Finset.sum_insert hnotmem]

/-- **Centered $(B - 2)$ Buchstab $L^2$ Step Identity (`sieveL2PrefixEnergy_moebiusReal_succ_sub_eq_centered`):**
For every $n \ge 1$ and $M \ge n + 1$, isolating the $q = 1$ quotient ($s_{n,\mu}(n + 1) = -\mu(n + 1)$)
gives:
$$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu)
  = \bigl(\lfloor M / (n + 1) \rfloor - 2\bigr)\mu(n + 1)^2 +
    2\mu(n + 1) \sum_{q \in \operatorname{Icc} 2 \lfloor M / (n + 1) \rfloor} s_{n,\mu}(q(n + 1)).$$
(Classification: New formulation.) -/
theorem sieveL2PrefixEnergy_moebiusReal_succ_sub_eq_centered {n M : ℕ}
    (hn : 1 ≤ n) (hlo : n + 1 ≤ M) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
      ((M / (n + 1) : ℕ) - 2 : ℝ) * moebiusReal (n + 1) ^ (2 : ℕ) +
        2 * moebiusReal (n + 1) *
          ∑ q ∈ Finset.Icc 2 (M / (n + 1)), sieveSeq n moebiusReal (q * (n + 1)) := by
  have hB : 1 ≤ M / (n + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hcomm :
      (∑ j ∈ Finset.Icc 1 (M / (n + 1)), sieveSeq n moebiusReal ((n + 1) * j)) =
        ∑ q ∈ Finset.Icc 1 (M / (n + 1)), sieveSeq n moebiusReal (q * (n + 1)) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_comm]
  rw [sieveL2PrefixEnergy_succ_sub_eq n M moebiusReal, hcomm,
    sum_Icc_one_eq_add_Icc_two hB (fun q => sieveSeq n moebiusReal (q * (n + 1))),
    one_mul, sieveSeq_moebiusReal_succ_eq_neg hn]
  ring

/-- For any $n, k \in \mathbb{N}$ with $2 \le k \le 5n$, $|\mu(n + 1) \cdot s_{n,\mu}(k)| \le \mu(n + 1)^2$.
(Classification: Corollary.) -/
theorem abs_moebiusReal_mul_sieveSeq_le_sq_of_le_five_mul {n k : ℕ}
    (hk : 2 ≤ k) (hhi : k ≤ 5 * n) :
    |moebiusReal (n + 1) * sieveSeq n moebiusReal k| ≤ moebiusReal (n + 1) ^ (2 : ℕ) := by
  have henv := abs_sieveSeq_moebiusReal_le_one_of_le_five_mul hk hhi
  rcases moebiusReal_eq_or (n + 1) with h | h | h
  · rw [h, neg_one_mul, abs_neg]
    linarith
  · rw [h, zero_mul, abs_zero]
    norm_num
  · rw [h, one_mul, one_pow]
    exact henv

/-- **Universal Five-Horizon Downward Buchstab Step Bound
(`sieveL2PrefixEnergy_moebiusReal_sub_succ_le_of_le_five_mul`):**
For every $n \ge 1$ and $M \ge n + 1$ such that $\lfloor M / (n + 1) \rfloor (n + 1) \le 5n$,
$$\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+1}(M; \mu)
  \le \lfloor M / (n + 1) \rfloor \cdot \mu(n + 1)^2.$$
(Classification: Candidate new theorem.) -/
theorem sieveL2PrefixEnergy_moebiusReal_sub_succ_le_of_le_five_mul {n M : ℕ}
    (hn : 1 ≤ n) (hlo : n + 1 ≤ M) (hhi : (M / (n + 1)) * (n + 1) ≤ 5 * n) :
    sieveL2PrefixEnergy n M moebiusReal - sieveL2PrefixEnergy (n + 1) M moebiusReal ≤
      (M / (n + 1) : ℕ) * moebiusReal (n + 1) ^ (2 : ℕ) := by
  have hB : 1 ≤ M / (n + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hstep := sieveL2PrefixEnergy_moebiusReal_succ_sub_eq_centered hn hlo
  have hsum :
      -(2 * moebiusReal (n + 1) *
          ∑ q ∈ Finset.Icc 2 (M / (n + 1)), sieveSeq n moebiusReal (q * (n + 1))) ≤
        2 * ((M / (n + 1) : ℕ) - 1 : ℝ) * moebiusReal (n + 1) ^ (2 : ℕ) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    have hle :
        (∑ q ∈ Finset.Icc 2 (M / (n + 1)),
            -(2 * moebiusReal (n + 1) * sieveSeq n moebiusReal (q * (n + 1)))) ≤
          ∑ _q ∈ Finset.Icc 2 (M / (n + 1)), 2 * moebiusReal (n + 1) ^ (2 : ℕ) := by
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_mem := Finset.mem_Icc.mp hq
      have hqk_lo : 2 ≤ q * (n + 1) := by nlinarith
      have hqk_hi : q * (n + 1) ≤ 5 * n :=
        (Nat.mul_le_mul_right (n + 1) hq_mem.2).trans hhi
      have habs := abs_moebiusReal_mul_sieveSeq_le_sq_of_le_five_mul hqk_lo hqk_hi
      have hneg : -(moebiusReal (n + 1) * sieveSeq n moebiusReal (q * (n + 1))) ≤
          |moebiusReal (n + 1) * sieveSeq n moebiusReal (q * (n + 1))| :=
        neg_le_abs _
      linarith
    rw [Finset.sum_const, Nat.card_Icc,
      show M / (n + 1) + 1 - 2 = M / (n + 1) - 1 by omega, nsmul_eq_mul,
      Nat.cast_sub hB, Nat.cast_one] at hle
    linarith
  linarith

/-- For every $n \ge 4$ and $n + 1 \le M < 5(n + 1)$, the downward step satisfies
$\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+1}(M; \mu) \le 4\mu(n + 1)^2 \le 4$.
(Classification: Corollary.) -/
theorem sieveL2PrefixEnergy_moebiusReal_sub_succ_le_four_of_lt_five_mul {n M : ℕ}
    (hn : 4 ≤ n) (hlo : n + 1 ≤ M) (hhi : M < 5 * (n + 1)) :
    sieveL2PrefixEnergy n M moebiusReal - sieveL2PrefixEnergy (n + 1) M moebiusReal ≤
        4 * moebiusReal (n + 1) ^ (2 : ℕ) ∧
      4 * moebiusReal (n + 1) ^ (2 : ℕ) ≤ 4 := by
  have hB_le : M / (n + 1) ≤ 4 := by
    have hlt : M / (n + 1) < 5 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hhi
    omega
  have h5n : (M / (n + 1)) * (n + 1) ≤ 5 * n := by
    calc (M / (n + 1)) * (n + 1) ≤ 4 * (n + 1) := Nat.mul_le_mul_right (n + 1) hB_le
      _ ≤ 5 * n := by omega
  have hstep := sieveL2PrefixEnergy_moebiusReal_sub_succ_le_of_le_five_mul (by omega) hlo h5n
  have hB_cast : ((M / (n + 1) : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hB_le
  have hsq_nonneg : 0 ≤ moebiusReal (n + 1) ^ (2 : ℕ) := (moebiusReal_sq_bounds (n + 1)).1
  have hsq_le : moebiusReal (n + 1) ^ (2 : ℕ) ≤ 1 := (moebiusReal_sq_bounds (n + 1)).2
  exact ⟨hstep.trans (mul_le_mul_of_nonneg_right hB_cast hsq_nonneg), by linarith⟩

/-- **Four-Band Linear $L^2$ Energy Bound (`sieveL2PrefixEnergy_moebiusReal_four_band_le`):**
For every $4 \le N \le M < 5(N + 1)$:
$$\mathcal{E}_N(M; \mu) \le 1 + 4(M - N : \mathbb{R}).$$
(Classification: Candidate new theorem.) -/
theorem sieveL2PrefixEnergy_moebiusReal_four_band_le {N M : ℕ}
    (hN : 4 ≤ N) (hNM : N ≤ M) (hM : M < 5 * (N + 1)) :
    sieveL2PrefixEnergy N M moebiusReal ≤ 1 + 4 * (M - N : ℝ) := by
  have hM1 : 1 ≤ M := by omega
  have htele := sieveL2PrefixEnergy_sub_eq_sum_Ico_succ_sub hNM M moebiusReal
  rw [sieveL2PrefixEnergy_moebiusReal_eq_one_of_le hM1 le_rfl] at htele
  have hbound :
      -(∑ n ∈ Finset.Ico N M,
          (sieveL2PrefixEnergy (n + 1) M moebiusReal -
            sieveL2PrefixEnergy n M moebiusReal)) ≤
        ∑ _n ∈ Finset.Ico N M, (4 : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn_mem := Finset.mem_Ico.mp hn
    have hstep := sieveL2PrefixEnergy_moebiusReal_sub_succ_le_four_of_lt_five_mul
      (by omega : 4 ≤ n) (by omega : n + 1 ≤ M) (by omega : M < 5 * (n + 1))
    linarith [hstep.1, hstep.2]
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hNM] at hbound
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
