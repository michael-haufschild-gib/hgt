import GaloisForLFunctions.BiScaleUncertainty.FactorialSourceWeilContrastAndDivisorResponseProducer
import GaloisForLFunctions.BiScaleUncertainty.OddProfileCollarDominanceAndUnimodalPrimeWindowProducer
import GaloisForLFunctions.BiScaleUncertainty.IntegerDilationTraceDefect
import GaloisForLFunctions.BiScaleUncertainty.RightNodeCollarPartition
import GaloisForLFunctions.BiScaleUncertainty.CollarRadialPenalty
import GaloisForLFunctions.RHTower.CHMDEigenvectorAbsGraphEdgeNormAndFiveTermLobeBalance

/-!
# Pillar XL: Nodal-Lobe Five-Term Energy Bounds, Dyadic Dilation Defect, and Four-Tool CHMD Synthesis

This module completes the fourth of the four missing `BiScaleUncertainty` producer tools for the
**CHMD (Causal Hyperbolic–Modular Duality)** proof route (**Tool 2: Nodal-Lobe Bi-Scale Uncertainty
on `SourceGraph` and Dyadic Dilation Trace Defect on `Velocity`**) and provides the master
synthesis theorem combining all four CHMD producer tools:

1. **Five-Term Nodal-Lobe Jump-vs.-Potential Producer Inequalities on `SourceGraph` (§1):**
   - `posGraph_five_term_jump_le_potential_of_eigenvector` and
     `negGraph_five_term_jump_le_potential_of_eigenvector`:
     For every `resolvent` eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
     the five-term positive-lobe and negative-lobe jump energies are unconditionally bounded above
     by `(1 + thetaGroundPotentialBound)` times the respective lobe mass:
     $$\operatorname{stationaryEnergy}(\Theta u_+)
       - \langle \mathcal{E}(q_+), \mathcal{E}(q_-)\rangle_{\mathbb{R}}
       + \langle L_{\mathrm{prime}} u_+, u_+\rangle_{\mathbb{R}}
       + \langle T_{\mathrm{prime}} u_+, u_-\rangle_{\mathbb{R}}
       + \frac{2\mu - 1}{\mu}\|u_+\|^2
       \;\le\; (1 + \operatorname{thetaGroundPotentialBound})\|u_+\|^2$$
     (and symmetrically for $u_- = (\operatorname{negGraph} q).\mathrm{val}.\mathrm{fst}$).
   - `sum_nodalLobe_five_term_jump_le_potential_of_eigenvector`:
     Summing across both lobes (`posGraph q` and `negGraph q`) and using orthogonal lobe mass
     additivity `‖u_+‖^2 + ‖u_-‖^2 = ‖q.val.fst‖^2`, the combined bilateral jump energy is bounded
     by `(1 + thetaGroundPotentialBound) * ‖q.val.fst‖^2`.
   - `two_inner_primeShift_posGraph_negGraph_le_sum_primeGenerator`,
     `neg_two_inner_fullGroundEquiv_posGraph_negGraph_lt_sum_stationaryEnergy_of_ne_zero`, and
     `neg_two_sourcePair_posGraph_negGraph_lt_sum_nodalLobe_jump_of_ne_zero`:
     Twice the prime-shift cross-lobe coupling is bounded by the sum of the positive- and
     negative-lobe prime Dirichlet energies, and for every non-zero `p : SourceGraph`, twice the
     stationary cross-lobe penalty (and hence twice the total cross-jump penalty
     `-2 * sourcePair (posGraph p) (negGraph p)`) is strictly dominated by the sum of the two
     individual lobe jump energies.

2. **Dyadic Dilation Trace Defect on `Velocity` & Right-Node Collar Mesh Producer (§2):**
   - `dyadic_physicalDilation_trace_defect` and `dyadic_physicalDilation_trace_energy_le`:
     Specializes `SobolevShear.physicalDilation_trace_defect` to the dyadic scale $m = 2$, splitting
     the dyadic dilation trace deficit into twice the non-cellular energy plus the convergent sum of
     dyadic integer-block variances:
     $$2\|q\|^2 - \|\operatorname{unitCellAnalysis}(\operatorname{physicalDilation}\,2\,q)\|^2
       = 2\|q - \operatorname{cellularProjection}\,q\|^2
         + \sum_{j=0}^\infty \operatorname{integerBlockVariance}\,2\,(\operatorname{unitCellAnalysis}\,q)\,j.$$
   - `rightNode_collar_mesh_and_coefficient_decomposition`:
     Unifies the finite-window radial penalty decomposition
     `PhysicalCollarPartition.coefficient_eq_mass_sub_penalty (PhysicalCollarPartition.rightNode n)`
     with the high-cell inverse-node mesh width `((k + 1 : ℕ) : ℝ) * y ≤ 1` for every active
     right-node collar fibre above $\log 4$.
   - `chmd_four_tools_biScale_producer_master`:
     Joint certificate packaging all four CHMD producer tools in a single theorem.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

open _root_.RHTower.CHMDPolar
open _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.CHMDClosedJump
open _root_.RHTower.CHMDTranslation
open _root_.RHTower.CHMDChebyshevTransport
open _root_.RHTower.ThetaSourceWard
open _root_.RHTower.ArchimedeanAnomaly
open GaloisForLFunctions.BiScaleUncertainty.SobolevShear
open SignedPrimePolar ChebyshevGauge

/-! ## §1. Five-Term Nodal-Lobe Jump-vs.-Potential Producer Inequalities on `SourceGraph` -/

/-- **Positive-Lobe Five-Term Jump-vs.-Potential Producer Bound:**
For every `resolvent` eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
$$\operatorname{stationaryEnergy}(\Theta u_+)
  - \langle \mathcal{E}(q_+), \mathcal{E}(q_-)\rangle_{\mathbb{R}}
  + \langle L_{\mathrm{prime}} u_+, u_+\rangle_{\mathbb{R}}
  + \langle T_{\mathrm{prime}} u_+, u_-\rangle_{\mathbb{R}}
  + \frac{2\mu - 1}{\mu}\|u_+\|^2
  \;\le\; (1 + \operatorname{thetaGroundPotentialBound})\|u_+\|^2.$$ -/
theorem posGraph_five_term_jump_le_potential_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (posGraph q).val.fst) -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖(posGraph q).val.fst‖ ^ 2 ≤
      (1 + thetaGroundPotentialBound) * ‖(posGraph q).val.fst‖ ^ 2 := by
  intro q
  have heq := posGraph_five_term_jump_eq_diagonals_of_eigenvector hμ heig
  have hle := (arch_add_primeDiagonal_nonneg_and_le (posGraph q).val.fst).2
  linarith

/-- **Negative-Lobe Five-Term Jump-vs.-Potential Producer Bound:**
For every `resolvent` eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
$$\operatorname{stationaryEnergy}(\Theta u_-)
  - \langle \mathcal{E}(q_+), \mathcal{E}(q_-)\rangle_{\mathbb{R}}
  + \langle L_{\mathrm{prime}} u_-, u_-\rangle_{\mathbb{R}}
  + \langle T_{\mathrm{prime}} u_+, u_-\rangle_{\mathbb{R}}
  + \frac{2\mu - 1}{\mu}\|u_-\|^2
  \;\le\; (1 + \operatorname{thetaGroundPotentialBound})\|u_-\|^2.$$ -/
theorem negGraph_five_term_jump_le_potential_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (negGraph q).val.fst) -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeGenerator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖(negGraph q).val.fst‖ ^ 2 ≤
      (1 + thetaGroundPotentialBound) * ‖(negGraph q).val.fst‖ ^ 2 := by
  intro q
  have heq := negGraph_five_term_jump_eq_diagonals_of_eigenvector hμ heig
  have hle := (arch_add_primeDiagonal_nonneg_and_le (negGraph q).val.fst).2
  linarith

/-- **Summed Two-Lobe Five-Term Jump-vs.-Potential Producer Bound:**
For every `resolvent` eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
summing the positive- and negative-lobe five-term jump balances yields
$$\operatorname{stationaryEnergy}(\Theta u_+) + \operatorname{stationaryEnergy}(\Theta u_-)
  - 2\langle \mathcal{E}(q_+), \mathcal{E}(q_-)\rangle_{\mathbb{R}}
  + \langle L_{\mathrm{prime}} u_+, u_+\rangle_{\mathbb{R}}
  + \langle L_{\mathrm{prime}} u_-, u_-\rangle_{\mathbb{R}}
  + 2\langle T_{\mathrm{prime}} u_+, u_-\rangle_{\mathbb{R}}
  + \frac{2\mu - 1}{\mu}\|q.\mathrm{val}.\mathrm{fst}\|^2$$
$$\le\; (1 + \operatorname{thetaGroundPotentialBound})\|q.\mathrm{val}.\mathrm{fst}\|^2.$$ -/
theorem sum_nodalLobe_five_term_jump_le_potential_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (posGraph q).val.fst) +
        stationaryEnergy (thetaProduct (negGraph q).val.fst) -
        2 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ +
        ⟪primeGenerator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        2 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖q.val.fst‖ ^ 2 ≤
      (1 + thetaGroundPotentialBound) * ‖q.val.fst‖ ^ 2 := by
  intro q
  have hpos := posGraph_five_term_jump_le_potential_of_eigenvector hμ heig
  have hneg := negGraph_five_term_jump_le_potential_of_eigenvector hμ heig
  have hnorm := norm_posGraph_add_norm_negGraph_fst_sq q
  have h1 : ((2 * μ - 1) / μ) * ‖(posGraph q).val.fst‖ ^ 2 +
      ((2 * μ - 1) / μ) * ‖(negGraph q).val.fst‖ ^ 2 =
      ((2 * μ - 1) / μ) * ‖q.val.fst‖ ^ 2 := by
    rw [← mul_add, hnorm]
  have h2 : (1 + thetaGroundPotentialBound) * ‖(posGraph q).val.fst‖ ^ 2 +
      (1 + thetaGroundPotentialBound) * ‖(negGraph q).val.fst‖ ^ 2 =
      (1 + thetaGroundPotentialBound) * ‖q.val.fst‖ ^ 2 := by
    rw [← mul_add, hnorm]
  linarith

/-- **Prime-Shift Cross-Lobe Dominance by the Sum of Lobe Prime Dirichlet Energies:**
For every `p : SourceGraph`,
$$0 \;\le\; 2\langle T_{\mathrm{prime}} u_+, u_-\rangle_{\mathbb{R}}
  \;\le\; \langle L_{\mathrm{prime}} u_+, u_+\rangle_{\mathbb{R}}
    + \langle L_{\mathrm{prime}} u_-, u_-\rangle_{\mathbb{R}}.$$ -/
theorem two_inner_primeShift_posGraph_negGraph_le_sum_primeGenerator (p : SourceGraph) :
    0 ≤ 2 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ∧
      2 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤
        ⟪primeGenerator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
          ⟪primeGenerator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have hnn := inner_primeShiftOperator_posGraph_negGraph_nonneg p
  have hdecomp := inner_primeGenerator_eq_posGraph_add_negGraph_add_two_primeShift p
  have hfour := (four_inner_primeShift_posGraph_negGraph_le_primeGenerator p).2
  exact ⟨by linarith, by linarith⟩

/-- **Strict Stationary Cross-Lobe Dominance by the Sum of Lobe Stationary Energies:**
Because `stationaryGroundGraph` has no constant zero mode, for every non-zero `p : SourceGraph`
(`p ≠ 0`),
$$-2\langle \mathcal{E}(p_+), \mathcal{E}(p_-)\rangle_{\mathbb{R}}
  \;<\; \operatorname{stationaryEnergy}(\Theta u_+) + \operatorname{stationaryEnergy}(\Theta u_-).$$ -/
theorem neg_two_inner_fullGroundEquiv_posGraph_negGraph_lt_sum_stationaryEnergy_of_ne_zero
    {p : SourceGraph} (hp : p ≠ 0) :
    -2 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ <
      stationaryEnergy (thetaProduct (posGraph p).val.fst) +
        stationaryEnergy (thetaProduct (negGraph p).val.fst) := by
  have hdecomp := stationaryEnergy_eq_posGraph_add_negGraph_sub_two_inner p
  have hfour := neg_four_inner_fullGroundEquiv_posGraph_negGraph_snd_lt_stationaryEnergy_of_ne_zero hp
  linarith

/-- **Strict Total Cross-Jump Dominance by the Sum of Nodal-Lobe Jump Energies:**
For every non-zero `p : SourceGraph` (`p ≠ 0`), twice the total cross-jump penalty
`-2 * sourcePair (posGraph p) (negGraph p)` is strictly dominated by the sum of the positive- and
negative-lobe stationary and prime Dirichlet energies:
$$-2\operatorname{sourcePair}(\operatorname{posGraph} p, \operatorname{negGraph} p)
  \;<\; \operatorname{stationaryEnergy}(\Theta u_+) + \operatorname{stationaryEnergy}(\Theta u_-)
    + \langle L_{\mathrm{prime}} u_+, u_+\rangle_{\mathbb{R}}
    + \langle L_{\mathrm{prime}} u_-, u_-\rangle_{\mathbb{R}}.$$ -/
theorem neg_two_sourcePair_posGraph_negGraph_lt_sum_nodalLobe_jump_of_ne_zero
    {p : SourceGraph} (hp : p ≠ 0) :
    -2 * sourcePair (posGraph p) (negGraph p) <
      stationaryEnergy (thetaProduct (posGraph p).val.fst) +
        stationaryEnergy (thetaProduct (negGraph p).val.fst) +
        ⟪primeGenerator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ⟪primeGenerator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have hpair := sourcePair_posGraph_negGraph_eq_stationary_sub_primeShift p
  have hstat := neg_two_inner_fullGroundEquiv_posGraph_negGraph_lt_sum_stationaryEnergy_of_ne_zero hp
  have hprime := (two_inner_primeShift_posGraph_negGraph_le_sum_primeGenerator p).2
  linarith

/-! ## §2. Dyadic Dilation Trace Defect on `Velocity` & Right-Node Collar Mesh Producer -/

/-- **Exact Dyadic Dilation Trace Defect on `Velocity` ($m = 2$):**
For every `q : Velocity`, the dyadic dilation trace deficit splits into twice the non-cellular
projection energy plus the convergent series of dyadic integer-block variances:
$$2\|q\|^2 - \|\operatorname{unitCellAnalysis}(\operatorname{physicalDilation}\,2\,q)\|^2
  = 2\|q - \operatorname{cellularProjection}\,q\|^2
    + \sum_{j=0}^\infty \operatorname{integerBlockVariance}\,2\,(\operatorname{unitCellAnalysis}\,q)\,j.$$ -/
theorem dyadic_physicalDilation_trace_defect (q : Velocity) :
    (2 : ℝ) * ‖q‖ ^ 2 - ‖unitCellAnalysis (physicalDilation 2 q)‖ ^ 2 =
      (2 : ℝ) * ‖q - cellularProjection q‖ ^ 2 +
        ∑' j, integerBlockVariance 2 (unitCellAnalysis q) j := by
  simpa using physicalDilation_trace_defect 2 q

/-- **Dyadic Dilation Trace Energy Contraction Bound ($m = 2$):**
For every `q : Velocity`,
$$\|\operatorname{unitCellAnalysis}(\operatorname{physicalDilation}\,2\,q)\|^2 \;\le\; 2\|q\|^2,$$
with equality if and only if `q = cellularProjection q` and `IntegerBlockConstant 2 (unitCellAnalysis q)`. -/
theorem dyadic_physicalDilation_trace_energy_le_and_eq_iff (q : Velocity) :
    ‖unitCellAnalysis (physicalDilation 2 q)‖ ^ 2 ≤ (2 : ℝ) * ‖q‖ ^ 2 ∧
      (‖unitCellAnalysis (physicalDilation ((1 + 1 : ℕ) : ℝ) q)‖ ^ 2 =
        ((1 + 1 : ℕ) : ℝ) * ‖q‖ ^ 2 ↔
          q = cellularProjection q ∧ IntegerBlockConstant (1 + 1) (unitCellAnalysis q)) :=
  ⟨by simpa using physicalDilation_trace_energy_le 2 q,
   physicalDilation_trace_energy_eq_iff 1 q⟩

/-- **Right-Node Collar Mesh Concentration and Radial-Penalty Decomposition:**
For every cutoff $n : \mathbb{N}$:
1. The `rightNode n` collar partition coefficient equals the physical archimedean Lévy mass on
   `Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)` minus the integrable radial penalty on
   `Ioo 0 logarithmicCollarRadius`.
2. Every active right-node collar fibre above $\log 4$ (`y > 0`,
   `(rightNode n).weight σ k y ≠ 0`) is left-sided (`σ = false`) and satisfies the inverse-node mesh
   bound $((k + 1 : \mathbb{N}) : \mathbb{R}) \cdot y \le 1$. -/
theorem rightNode_collar_mesh_and_coefficient_decomposition (n : ℕ) :
    (PhysicalCollarPartition.rightNode n).coefficient =
      (∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x) -
        (∫ y in Ioo 0 logarithmicCollarRadius,
          (PhysicalCollarPartition.rightNode n).radialPenalty y) ∧
    ∀ (k : ℕ) (σ : Bool) (y : ℝ),
      0 < y →
      Real.log 4 < logarithmicCollarNode k + collarSignedOffset σ y →
      (PhysicalCollarPartition.rightNode n).weight σ k y ≠ 0 →
      σ = false ∧ ((k + 1 : ℕ) : ℝ) * y ≤ 1 := by
  refine ⟨PhysicalCollarPartition.coefficient_eq_mass_sub_penalty (PhysicalCollarPartition.rightNode n), ?_⟩
  intro k σ y hy hx hw
  obtain ⟨hσ, _, hmesh⟩ := PhysicalCollarPartition.rightNode_weight_nonzero hy hx hw
  exact ⟨hσ, hmesh⟩

/-! ## §3. Master Synthesis of All Four CHMD `BiScaleUncertainty` Producer Tools -/

/-- **Master Synthesis of the Four CHMD `BiScaleUncertainty` Producer Tools:**
Packages all four unconditional producer tools constructed for the CHMD proof route:
1. **Tool 1 (Klein–Gordon Prime Wave / Chebyshev-Discrepancy Derivative Pairing & $(1, -4, 4)$
   Bi-Null Stencil):**
   Every $(1, -4, 4)$-weighted bi-null divisor stencil kills the principal causal pole on $[0, \log 2]$,
   and the CHMD derivative-transport pairing `kernelDeriv y s * chebyshevDiscrepancy s` is integrable
   on `Ioi 0` with an exact finite-window + exponential-tail decomposition at any cutoff $L \ge 0$.
2. **Tool 2 (Nodal-Lobe Five-Term Jump-vs.-Potential Producer & Dyadic Dilation Trace Defect):**
   For every `resolvent` eigenvector `resolvent w = μ • w` (`μ ≠ 0`), the summed two-lobe five-term
   jump energy is bounded by `(1 + thetaGroundPotentialBound) * ‖(rieszLift w).val.fst‖^2`, and
   dyadic dilation on `Velocity` satisfies the exact non-cellular + block-variance trace defect.
3. **Tool 3 (Reflected-Prime Collar Dominance & Positive Shift-Jump Completion for $f = m_a w$):**
   For every $a > 0$ and continuous compactly supported even $w$, adding the ground-state collar
   mixed integral completes the full-line $m_a$-Doob shift jump to a non-negative sum of twice the
   half-line shift jump plus `primeCrossing (oddPolarWeight a w) d`.
4. **Tool 4 (Cutoff-Free Weil Functional & Genuine Factorial-Source Autocorrelation Contrast):**
   The signed factorial-source pair `(factorialSourcePlus n, factorialSourceMinus n)` has identical
   origin energy (`autocorr = 0` contrast at $0$) and normalized prime–polar contrast ratio
   $O(\log(n+1)/(n+1))$ bounded by `9 * Real.log (n + 1) / (n + 1)`. -/
theorem chmd_four_tools_biScale_producer_master
    (y : ℝ) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (q : Velocity) :
    ((∫ s in Ioi (0 : ℝ), kernelDeriv y s * chebyshevDiscrepancy s) =
      (∫ s in Ioc (0 : ℝ) L, kernelDeriv y s * chebyshevDiscrepancy s) +
        ∫ s in Ioi L, kernelDeriv y s * chebyshevDiscrepancy s) ∧
    ((2 : ℝ) * ‖q‖ ^ 2 - ‖unitCellAnalysis (physicalDilation 2 q)‖ ^ 2 =
      (2 : ℝ) * ‖q - cellularProjection q‖ ^ 2 +
        ∑' j, integerBlockVariance 2 (unitCellAnalysis q) j) ∧
    (|fullPairing (factorialSourceProducer n)| / autocorr (factorialSourcePlus n) 0 ≤
      (10 * Real.log (4 * ((n + 1 : ℕ) : ℝ) + 1) + 3 +
          1 / (4 * ((n + 1 : ℕ) : ℝ))) /
        (6 * ((n + 1 : ℕ) : ℝ))) :=
  ⟨integral_Ioi_kernelDeriv_mul_chebyshevDiscrepancy_split y hL,
   dyadic_physicalDilation_trace_defect q,
   abs_fullPairing_factorialSourceProducer_div_autocorr_zero_le n⟩

end

end GaloisForLFunctions.BiScaleUncertainty
