import GaloisForLFunctions.BiScaleUncertainty.StationaryResolventMarkovPositivityAndNodalDefectProducer
import GaloisForLFunctions.BiScaleUncertainty.ProducerConsumerDualityAndNymanBeurlingBridge
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicLorentzBoostAndMinkowskiLightCone
import GaloisForLFunctions.TransHorizonIncidenceMechanics.OddEigenvectorNodalModulusBalanceAndFourthBandStepLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SupportRadiusCollarCutoffAndAllScaleObstacleBBridge
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PronicCausalQuadratureInteriorSawtoothAndFermiGramBridge

/-!
# Markov Nodal-Defect Coercivity, Pure `absGraph` Five-Term Balance, & Second-Order Pronic Gram Synthesis (`NodalDefectMarkovSubinvarianceAndCenteringPronicGramBridge`)

This module synthesizes deep structural results from `BiScaleUncertainty`, `BezoutValuationIncidence`,
and `TransHorizonIncidenceMechanics` across Obstacles 1–6 and Pillars 1–5 of the Trans-Horizon
Incidence Mechanics programme (`docs/reports/hard-obstacles-summary-1810.md`):

## 1. Beurling–Deny Markov Sub-Invariance, `nodalDefectGraph` Coercivity, & Pure `absGraph` Five-Term Balance (§1)

- **Exact Modulus Invariance of Local Diagonal Quadratic Forms (`absGraph_diagonal_quadratic_invariance`):**
  Because `posGraph p` and `negGraph p` have disjoint supports in `MassSpace`, all four local
  diagonal quadratic forms (`‖thetaToVolume ·‖^2`, `archDiagonalOperator`, `primeDiagonalOperator`,
  and `groundPotentialOperator`) are identically invariant under `p ↦ absGraph p`.
- **Pure `absGraph` Five-Term Nonnegative Jump-vs.-Diagonal Balance & Potential Bound
  (`absGraph_five_term_jump_eq_diagonals_of_eigenvector`,
  `absGraph_five_term_jump_le_potential_bound_of_eigenvector`,
  `inv_cosh_le_inv_cosh_add_theta_div_cosh`):**
  For any eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`, the five-term
  nonnegative jump sum of `absGraph q` equals the local diagonal energy of `q` itself:
  $$\operatorname{stationaryEnergy}(\Theta(\operatorname{absGraph} q))
    + \langle \mathcal{L}_{\mathrm{prime}}(\operatorname{absGraph} q), \operatorname{absGraph} q\rangle_{\mathbb{R}}
    - 4\langle \operatorname{posGraph} q, \operatorname{negGraph} q\rangle_{\mathrm{stat}}
    + 4\langle S_{\mathrm{prime}}(\operatorname{posGraph} q), \operatorname{negGraph} q\rangle_{\mathbb{R}}
    + \frac{2\mu - 1}{\mu}\|q.\text{fst}\|^2$$
  $$= c_{\infty}\|\operatorname{thetaToVolume} q.\text{fst}\|^2
    + \langle V_{\mathrm{prime}} q.\text{fst}, q.\text{fst}\rangle_{\mathbb{R}}
    = \|q.\text{fst}\|^2 - \langle V_{\mathrm{ground}} q.\text{fst}, q.\text{fst}\rangle_{\mathbb{R}}
    \le (1 + B_{\mathrm{ground}})\|q.\text{fst}\|^2,$$
  accompanied by the pointwise collar-vs.-far-field decay decomposition
  $1 / \cosh(x/2) \le 1 / \cosh(R/2) + (1 / \Theta(R))(\Theta(x) / \cosh(x/2))$.
- **Spectral-to-Nodal-Defect Coercivity & Pointwise Lobe Sub-Invariance
  (`eigenvector_nodalDefectGraph_ground_energy_ge_spectral_excess_sq`):**
  Combining the `stationaryGroundGraph` Cauchy–Schwarz inequality for `nodalDefectGraph μ q`
  (`inner_fullGroundEquiv_nodalDefectGraph_of_eigenvector`) with the bilateral cross-jump identity
  `-4 * sourcePair (posGraph q) (negGraph q) = ((2 * μ - 1) / μ) * ‖q.val.fst‖ ^ 2 - sourceEnergy (absGraph q)`
  proves that for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`),
  $$\left(\frac{2\mu - 1}{\mu}\|q.\text{fst}\|^2 - \operatorname{sourceEnergy}(\operatorname{absGraph} q)\right)^2
    \le 4\Bigl(\|(\operatorname{nodalDefectGraph}\,\mu\,q).\text{fst}\|^2
      + \operatorname{stationaryEnergy}(\Theta(\operatorname{nodalDefectGraph}\,\mu\,q))\Bigr)
      \Bigl(\|q.\text{fst}\|^2 + \operatorname{stationaryEnergy}(\Theta(\operatorname{absGraph} q))\Bigr),$$
  while for $0 < \mu \le 1$, `(nodalDefectGraph μ q).val.fst ≥ 0` a.e. and both lobes are pointwise
  sub-invariant under `stationaryResolvent ∘ stationaryCollarPotential μ`.

## 2. Rank-1 Von Mangoldt + Centering-Discrepancy Pronic Gram Synthesis, All-Depth Conditional Tail, & Second-Order $O(1/((H+1)(H+2)))$ Mean Approximation (§2)

- **Universal Difference Law Between Mean-Centered and Uncentered Pronic Gram Forms
  (`sieveMeanCenteredPronicGramForm_sub_sievePronicDiscrepancyGramForm_eq`):**
  Combining `sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered` and
  `sieveMeanCenteredPronicGramForm_eq_energyCentered_add_sq` eliminates
  `sieveEnergyCenteredPronicGramForm N c` and expresses the difference between the mean-centered and
  uncentered pronic Gram forms as an exact difference of squares between the centering-discrepancy
  functional $\sum_{e=2}^N (\varphi(e)/2 - \Lambda(e)) Y_{N,c}(e)$ and the von Mangoldt functional
  $\sum_{e=2}^N \Lambda(e) Y_{N,c}(e)$.
- **Exact Four-Part Orthogonal Decomposition of `pmPowerDampedRamanujanGramQuadratic`
  (`pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_variance`,
  `pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_head_add_tail`):**
  Specializing to `pmCofactorDivisorWeight ε Q` proves that the uncentered Route PM pronic Gram form
  decomposes into the squared von Mangoldt energy mean plus the energy-centered variance, which in
  turn splits orthogonally at any horizon $H \in \mathbb{N}$ into `naturalCutoffHeadEnergy`,
  $(H + 1)(\operatorname{naturalCutoffHeadMean})^2$, and `naturalCutoffTailVariance`.
- **Second-Order $O(1/((H+1)(H+2)))$ Finite-Horizon Approximation for `pmPowerDampedRamanujanEnergyMean`
  (`exists_second_order_pmPowerDampedRamanujanEnergyMean_bound`):**
  Subtracting the first-order totient drift cancels the $O(1/(H+1))$ finite-horizon pronic truncation
  error and approximates `pmPowerDampedRamanujanEnergyMean ε Q` to second order
  $2B / ((H + 1)(H + 2))$.

## 3. Boosted Light-Cone Dyadic Producer–Consumer Duality & Pronic Vasyunin Tail Gram (§3)

- **Boosted Null-Cone Equivalence & Dyadic-Window Producer–Consumer Lévy Bound
  (`boosted_dyadic_window_producer_consumer_duality_le_levy`):**
  Combines the Hyperbolic Minkowski Light-Cone equivalence
  (`autocorr_eq_zero_iff_coshMultiplier_eq_sinhMultiplier`) with
  `dyadic_window_producer_consumer_duality_le_levy`, showing that for any rapidity $\alpha \in \mathbb{R}$,
  coincidence of the $\cosh(\alpha\cdot)$- and $\sinh(\alpha\cdot)$-boosted autocorrelations at the
  dyadic grid nodes $\log(N+k)$ ($0 \le k < N$) implies the producer–consumer Lévy bound against any
  collar producer $W$ on $[\log N, \log(2N)]$.
- **Pronic-Indexed Global-Minus-Head Vasyunin–Fermi Tail Gram & Single-Cell Tail Energy
  (`fermiTailGram_eq_global_sub_sum_pronicSeq`,
  `integral_normSq_singleCellFermiCombinator_tail_eq_global_sub_pronicSeq`):**
  Connects `VasyuninReciprocityAndExactTailGramProducer` directly to the BVI pronic weight
  `pronicSeq n = n * (n + 1)` with zero finite-$K$ truncation artifact.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDClosedJump RHTower.CHMDPolar RHTower.Sieve
open RHTower.ThetaSourceWard RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open scoped InnerProductSpace BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Beurling–Deny Markov Sub-Invariance, `nodalDefectGraph` Coercivity, & Pure `absGraph` Five-Term Balance -/

/-- **Exact Modulus Invariance of Local Diagonal Quadratic Forms on `SourceGraph`
(`absGraph_diagonal_quadratic_invariance`):**
Because `posGraph p` and `negGraph p` have disjoint supports in `MassSpace`, all four local diagonal
quadratic forms (`‖thetaToVolume ·‖^2`, `archDiagonalOperator`, `primeDiagonalOperator`, and
`groundPotentialOperator`) take the exact same value on `absGraph p` as on `p`. -/
theorem absGraph_diagonal_quadratic_invariance (p : SourceGraph) :
    ‖thetaToVolume (absGraph p).val.fst‖ ^ (2 : ℕ) = ‖thetaToVolume p.val.fst‖ ^ (2 : ℕ) ∧
      ⟪archDiagonalOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ =
        ⟪archDiagonalOperator p.val.fst, p.val.fst⟫_ℝ ∧
      ⟪primeDiagonalOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ =
        ⟪primeDiagonalOperator p.val.fst, p.val.fst⟫_ℝ ∧
      ⟪groundPotentialOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ =
        ⟪groundPotentialOperator p.val.fst, p.val.fst⟫_ℝ := by
  have hadd : (absGraph p).val.fst = (posGraph p).val.fst + (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_add_negGraph p).symm
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p).symm
  have htheta : ‖thetaToVolume (absGraph p).val.fst‖ ^ (2 : ℕ) =
      ‖thetaToVolume p.val.fst‖ ^ (2 : ℕ) := by
    rw [hadd, hsub, map_add, map_sub, norm_add_sq_real, norm_sub_sq_real,
      inner_thetaToVolume_posGraph_negGraph]
    ring
  have harch : ⟪archDiagonalOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ =
      ⟪archDiagonalOperator p.val.fst, p.val.fst⟫_ℝ := by
    rw [inner_archDiagonalOperator_self, inner_archDiagonalOperator_self, htheta]
  have hprime : ⟪primeDiagonalOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ =
      ⟪primeDiagonalOperator p.val.fst, p.val.fst⟫_ℝ := by
    rw [hadd, hsub, map_add, map_sub,
      inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right,
      primeDiagonalOperator_symmetric (negGraph p).val.fst (posGraph p).val.fst,
      real_inner_comm (primeDiagonalOperator (posGraph p).val.fst) (negGraph p).val.fst,
      inner_primeDiagonalOperator_posGraph_negGraph]
    ring
  have hground : ⟪groundPotentialOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ =
      ⟪groundPotentialOperator p.val.fst, p.val.fst⟫_ℝ := by
    rw [hadd, hsub, map_add, map_sub,
      inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right,
      groundPotentialOperator_symmetric (negGraph p).val.fst (posGraph p).val.fst,
      real_inner_comm (groundPotentialOperator (posGraph p).val.fst) (negGraph p).val.fst,
      inner_groundPotentialOperator_posGraph_negGraph]
    ring
  exact ⟨htheta, harch, hprime, hground⟩

/-- **Pure `absGraph` Five-Term Nonnegative Jump-vs.-Diagonal Balance for Any Eigenvector
(`absGraph_five_term_jump_eq_diagonals_of_eigenvector`):**
For every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`, the five-term
nonnegative jump sum of `absGraph q` equals both `archGroundConstant * ‖thetaToVolume q.val.fst‖ ^ 2 + ⟪primeDiagonalOperator q.val.fst, q.val.fst⟫_ℝ`
and `‖q.val.fst‖ ^ 2 - ⟪groundPotentialOperator q.val.fst, q.val.fst⟫_ℝ`. -/
theorem absGraph_five_term_jump_eq_diagonals_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (absGraph q).val.fst) +
        ⟪primeGenerator (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ -
        4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖q.val.fst‖ ^ (2 : ℕ) =
      archGroundConstant * ‖thetaToVolume q.val.fst‖ ^ (2 : ℕ) +
        ⟪primeDiagonalOperator q.val.fst, q.val.fst⟫_ℝ ∧
    stationaryEnergy (thetaProduct (absGraph q).val.fst) +
        ⟪primeGenerator (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ -
        4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖q.val.fst‖ ^ (2 : ℕ) =
      ‖q.val.fst‖ ^ (2 : ℕ) - ⟪groundPotentialOperator q.val.fst, q.val.fst⟫_ℝ := by
  intro q
  have h1 := (eigenvector_sourceEnergy_absGraph_sub_four_sourcePair_eq hμ heig).2
  have h2 := sourceEnergy_eq_stationary_add_primeGenerator_sub_diagonals (absGraph q)
  obtain ⟨htheta, _, hprime, _⟩ := absGraph_diagonal_quadratic_invariance q
  have h3 := arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential q.val.fst
  have hid : ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ (2 : ℕ) +
      ((2 * μ - 1) / μ) * ‖q.val.fst‖ ^ (2 : ℕ) = 0 := by
    field_simp [hμ]
    ring
  rw [htheta, hprime] at h2
  exact ⟨by linarith, by linarith⟩

/-- **Uniform Potential Upper Bound on the Pure `absGraph` Five-Term Jump Sum
(`absGraph_five_term_jump_le_potential_bound_of_eigenvector`):**
For every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`, the five-term
nonnegative `absGraph q` jump sum is bounded above by
`(1 + thetaGroundPotentialBound) * ‖q.val.fst‖ ^ 2`. -/
theorem absGraph_five_term_jump_le_potential_bound_of_eigenvector {μ : ℝ}
    (hμ : μ ≠ 0) {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (absGraph q).val.fst) +
        ⟪primeGenerator (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ -
        4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖q.val.fst‖ ^ (2 : ℕ) ≤
      (1 + thetaGroundPotentialBound) * ‖q.val.fst‖ ^ (2 : ℕ) := by
  intro q
  have h1 := (absGraph_five_term_jump_eq_diagonals_of_eigenvector hμ heig).1
  have h2 := (arch_add_primeDiagonal_nonneg_and_le q.val.fst).2
  linarith

/-- **Pointwise Collar-vs.-Far-Field Decomposition of `1 / Real.cosh (x / 2)`
(`inv_cosh_le_inv_cosh_add_theta_div_cosh`):**
Because `riemannKernelReal` is even (`riemannKernelReal_abs`) and strictly antitone on `[0, ∞)`
(`strictAntiOn_riemannKernelReal_Ici`), for every `0 ≤ R` and `x : ℝ`:
`1 / Real.cosh (x / 2) ≤ 1 / Real.cosh (R / 2) + (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2))`. -/
theorem inv_cosh_le_inv_cosh_add_theta_div_cosh {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    1 / Real.cosh (x / 2) ≤
      1 / Real.cosh (R / 2) +
        (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2)) := by
  have hθR : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hθx : 0 < riemannKernelReal x := riemannKernelReal_pos x
  have hchx : 0 < Real.cosh (x / 2) := Real.cosh_pos (x / 2)
  have hchR : 0 < Real.cosh (R / 2) := Real.cosh_pos (R / 2)
  by_cases hx : |x| ≤ R
  · have hle : riemannKernelReal R ≤ riemannKernelReal x := by
      rw [← riemannKernelReal_abs x]
      exact strictAntiOn_riemannKernelReal_Ici.antitoneOn
        (mem_Ici.mpr (abs_nonneg x)) (mem_Ici.mpr hR) hx
    have h1 : 1 ≤ riemannKernelReal x / riemannKernelReal R := (one_le_div hθR).mpr hle
    have h2 : 1 / Real.cosh (x / 2) ≤
        (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2)) := by
      calc 1 / Real.cosh (x / 2)
          = 1 * (1 / Real.cosh (x / 2)) := by ring
        _ ≤ (riemannKernelReal x / riemannKernelReal R) * (1 / Real.cosh (x / 2)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2)) := by ring
    have h3 : 0 ≤ 1 / Real.cosh (R / 2) := by positivity
    linarith
  · push Not at hx
    have hcosh : Real.cosh (R / 2) ≤ Real.cosh (x / 2) := by
      rw [Real.cosh_le_cosh, abs_div, abs_div, abs_of_nonneg hR, abs_two]
      exact div_le_div_of_nonneg_right hx.le (by norm_num)
    have h1 : 1 / Real.cosh (x / 2) ≤ 1 / Real.cosh (R / 2) :=
      one_div_le_one_div_of_le hchR hcosh
    have h2 : 0 ≤ (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2)) := by
      positivity
    linarith

/-- **Spectral-to-Nodal-Defect Coercivity & Markov Lobe Sub-Invariance
(`eigenvector_nodalDefectGraph_ground_energy_ge_spectral_excess_sq`):**
For every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`:
The squared spectral-modulus excess `(sourceEnergy (absGraph q) - ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2) ^ 2`
equals `16 * sourcePair (posGraph q) (negGraph q) ^ 2` and is bounded above by
`4 * (‖(nodalDefectGraph μ q).val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (nodalDefectGraph μ q).val.fst)) * (‖q.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (absGraph q).val.fst))`. -/
theorem eigenvector_nodalDefectGraph_ground_energy_ge_spectral_excess_sq
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    (sourceEnergy (absGraph q) - ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ (2 : ℕ)) ^ (2 : ℕ) =
        16 * sourcePair (posGraph q) (negGraph q) ^ (2 : ℕ) ∧
      (sourceEnergy (absGraph q) - ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        4 * (‖(nodalDefectGraph μ q).val.fst‖ ^ (2 : ℕ) +
            stationaryEnergy (thetaProduct (nodalDefectGraph μ q).val.fst)) *
          (‖q.val.fst‖ ^ (2 : ℕ) + stationaryEnergy (thetaProduct (absGraph q).val.fst)) := by
  intro q
  have hbal :
      sourceEnergy (absGraph q) - 4 * sourcePair (posGraph q) (negGraph q) =
        ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ (2 : ℕ) :=
    (eigenvector_sourceEnergy_absGraph_sub_four_sourcePair_eq hμ heig).1
  have hcs :
      4 * sourcePair (posGraph q) (negGraph q) ^ (2 : ℕ) ≤
        (‖(nodalDefectGraph μ q).val.fst‖ ^ (2 : ℕ) +
            stationaryEnergy (thetaProduct (nodalDefectGraph μ q).val.fst)) *
          (‖q.val.fst‖ ^ (2 : ℕ) + stationaryEnergy (thetaProduct (absGraph q).val.fst)) :=
    (inner_fullGroundEquiv_nodalDefectGraph_of_eigenvector hμ heig).2.2.2.2
  have h4 : sourceEnergy (absGraph q) - ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ (2 : ℕ) =
      4 * sourcePair (posGraph q) (negGraph q) := by
    rw [← hbal]
    ring
  have hsq : (sourceEnergy (absGraph q) - ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ (2 : ℕ)) ^ (2 : ℕ) =
      4 * (4 * sourcePair (posGraph q) (negGraph q) ^ (2 : ℕ)) := by
    rw [h4]
    ring
  refine ⟨by rw [h4]; ring, ?_⟩
  rw [hsq, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcs (by norm_num)

/-! ## §2. Rank-1 Von Mangoldt + Centering-Discrepancy Pronic Gram Synthesis, All-Depth Conditional Tail, & Second-Order Mean Approximation -/

/-- **Universal Difference Law Between Mean-Centered and Uncentered Pronic Gram Forms
(`sieveMeanCenteredPronicGramForm_sub_sievePronicDiscrepancyGramForm_eq`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`, eliminating `sieveEnergyCenteredPronicGramForm N c`
between `sieveMeanCenteredPronicGramForm_eq_energyCentered_add_sq` and
`sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered` expresses the difference
`sieveMeanCenteredPronicGramForm N c - sievePronicDiscrepancyGramForm N c` as the exact difference
of squares between the centering-discrepancy functional and the von Mangoldt functional. -/
theorem sieveMeanCenteredPronicGramForm_sub_sievePronicDiscrepancyGramForm_eq
    (N : ℕ) (c : ℕ → ℝ) :
    sieveMeanCenteredPronicGramForm N c - sievePronicDiscrepancyGramForm N c =
      (∑ e ∈ Finset.Icc 2 N, sieveCenteringDiscrepancy e * selbergMultiplesCoord N c e) ^ (2 : ℕ) -
        (∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e) ^ (2 : ℕ) := by
  have h1 := sieveMeanCenteredPronicGramForm_eq_energyCentered_add_sq N c
  have h2 := sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered N c
  linarith

/-- **Exact Rank-1 Von Mangoldt + Energy-Variance Decomposition of `pmPowerDampedRamanujanGramQuadratic`
(`pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_variance`):**
For every `ε > 0` and natural cutoff `Q : ℕ`, the uncentered Route PM pronic Gram quadratic form
`pmPowerDampedRamanujanGramQuadratic ε Q` decomposes into the squared von Mangoldt energy mean
`pmPowerDampedRamanujanEnergyMean ε Q ^ 2` plus the nonnegative energy-centered variance
`pmPowerDampedRamanujanEnergyVariance ε Q`. -/
theorem pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_variance
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    pmPowerDampedRamanujanGramQuadratic ε Q =
        pmPowerDampedRamanujanEnergyMean ε Q ^ (2 : ℕ) +
          pmPowerDampedRamanujanEnergyVariance ε Q ∧
      pmPowerDampedRamanujanEnergyMean ε Q ^ (2 : ℕ) ≤
        pmPowerDampedRamanujanGramQuadratic ε Q := by
  have hgram := sievePronicDiscrepancyGramForm_pmCofactorDivisorWeight_eq ε Q
  have hvar := sieveEnergyCenteredPronicGramForm_pmCofactorDivisorWeight_eq hε Q
  have hmean := vonMangoldt_sum_pmCofactorDivisorWeight_eq ε Q
  have hdecomp :=
    sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered (Q + 1)
      (pmCofactorDivisorWeight ε Q)
  have hnn := sieveEnergyCenteredPronicGramForm_nonneg (Q + 1) (pmCofactorDivisorWeight ε Q)
  have hmean_sq :
      (∑ e ∈ Finset.Icc 2 (Q + 1),
          vonMangoldt e * selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) e) ^ (2 : ℕ) =
        pmPowerDampedRamanujanEnergyMean ε Q ^ (2 : ℕ) := by
    rw [← hmean]
    ring
  rw [hgram, hvar, hmean_sq] at hdecomp
  rw [hvar] at hnn
  exact ⟨hdecomp, by linarith⟩

/-- **Four-Part All-Depth Orthogonal Decomposition of `pmPowerDampedRamanujanGramQuadratic`
(`pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_head_add_tail`):**
For every `ε > 0`, cutoff `Q : ℕ`, and splitting horizon `H : ℕ`,
`pmPowerDampedRamanujanGramQuadratic ε Q` decomposes orthogonally into:
1. the squared von Mangoldt mean `pmPowerDampedRamanujanEnergyMean ε Q ^ 2`,
2. the finite prefix energy `naturalCutoffHeadEnergy ε Q H`,
3. the forced conditional tail-mean energy `((H : ℝ) + 1) * (naturalCutoffHeadMean ε Q H) ^ 2`, and
4. the conditional-mean-centered tail variance `naturalCutoffTailVariance ε Q H ≥ 0`. -/
theorem pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_head_add_tail
    {ε : ℝ} (hε : 0 < ε) (Q H : ℕ) :
    pmPowerDampedRamanujanGramQuadratic ε Q =
      pmPowerDampedRamanujanEnergyMean ε Q ^ (2 : ℕ) +
        naturalCutoffHeadEnergy ε Q H +
        ((H : ℝ) + 1) * (naturalCutoffHeadMean ε Q H) ^ (2 : ℕ) +
        naturalCutoffTailVariance ε Q H := by
  have h1 := (pmPowerDampedRamanujanGramQuadratic_eq_mean_sq_add_variance hε Q).1
  have h2 := pmPowerDampedRamanujanEnergyVariance_eq_head_add_tail hε Q H
  linarith

/-- **Second-Order $O(1 / ((H + 1)(H + 2)))$ Finite-Horizon Approximation for `pmPowerDampedRamanujanEnergyMean`
(`exists_second_order_pmPowerDampedRamanujanEnergyMean_bound`):**
For every `ε > 0` and cutoff `Q : ℕ`, there exists an explicit finite constant `B ≥ 0` (independent
of `H`) such that for every finite horizon `H : ℕ`:
`|(∑_{M=1}^H (pmPowerDampedRamanujanCumulativePrefix ε Q M).re / pronicSeq M) - pmPowerDampedRamanujanEnergyMean ε Q - ((1 / 2) * ∑_{e=2}^{Q+1} e.totient * (pmPowerDampedRamanujanWeight ε e).re) / (H + 1)| ≤ 2 * B / ((H + 1) * (H + 2))`. -/
theorem exists_second_order_pmPowerDampedRamanujanEnergyMean_bound
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ H : ℕ,
      |(∑ M ∈ Finset.Icc 1 H,
          (pmPowerDampedRamanujanCumulativePrefix ε Q M).re / (pronicSeq M : ℝ)) -
        pmPowerDampedRamanujanEnergyMean ε Q -
        ((1 / 2 : ℝ) * ∑ e ∈ Finset.Icc 2 (Q + 1),
          (e.totient : ℝ) * (pmPowerDampedRamanujanWeight ε e).re) /
          ((H : ℝ) + 1)| ≤
        2 * B / (((H : ℝ) + 1) * ((H : ℝ) + 2)) := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_second_order_sievePrefixDiscrepancy_vonMangoldt_bound (Q + 1)
      (pmCofactorDivisorWeight ε Q)
  refine ⟨B, hB0, fun H => ?_⟩
  have h1 := hB H
  have hpref :
      (∑ M ∈ Finset.Icc 1 H,
          sievePrefixDiscrepancy (Q + 1) M (pmCofactorDivisorWeight ε Q) / (pronicSeq M : ℝ)) =
        ∑ M ∈ Finset.Icc 1 H,
          (pmPowerDampedRamanujanCumulativePrefix ε Q M).re / (pronicSeq M : ℝ) := by
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [sievePrefixDiscrepancy_pmCofactorDivisorWeight_eq hε Q M]
  have hvm :
      (∑ e ∈ Finset.Icc 2 (Q + 1),
          vonMangoldt e * selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) e) =
        -pmPowerDampedRamanujanEnergyMean ε Q := by
    linarith [vonMangoldt_sum_pmCofactorDivisorWeight_eq ε Q]
  have htot :
      (∑ e ∈ Finset.Icc 2 (Q + 1),
          (e.totient : ℝ) * selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) e) =
        ∑ e ∈ Finset.Icc 2 (Q + 1),
          (e.totient : ℝ) * (pmPowerDampedRamanujanWeight ε e).re := by
    refine Finset.sum_congr rfl fun e he => ?_
    have he_mem : e ∈ Finset.Icc 1 (Q + 1) := by
      rw [Finset.mem_Icc] at he ⊢
      omega
    rw [selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε he_mem]
  rw [hpref, hvm, htot, ← sub_eq_add_neg] at h1
  exact h1

/-! ## §3. Boosted Light-Cone Dyadic Producer–Consumer Duality & Pronic Vasyunin Tail Gram -/

/-- **Boosted Null-Cone Equivalence & Dyadic-Window Producer–Consumer Lévy Bound
(`boosted_dyadic_window_producer_consumer_duality_le_levy`):**
For any `f ∈ C²_c(ℝ)`, rapidity `α : ℝ`, and `N ≥ 1`:
1. The dyadic-window node-vanishing condition `∀ k ∈ range N, autocorr f (log(N + k)) = 0` is
   equivalent (`↔`) to coincidence of the `cosh`- and `sinh`-boosted autocorrelations at all `N`
   dyadic nodes:
   `∀ k ∈ range N, autocorr (coshMultiplier α f) (log(N + k)) = autocorr (sinhMultiplier α f) (log(N + k))`.
2. Whenever these boosted autocorrelations coincide on the dyadic grid nodes, every continuous collar
   producer `W` on `[log N, log(2N)]` satisfies the producer–consumer Lévy duality inequality:
   `(∫ x in log N..log(2N), autocorr f x * cosh(x / 2) + ∫ x in log N..log(2N), (autocorr f 0 - autocorr f x) * W x - (∫ x in log N..log(2N), W x) * autocorr f 0)² ≤ 2 * autocorr f 0 * biScaleLevyEnergy f * ∫ x in log N..log(2N), (cosh(x / 2) - W x)²`. -/
theorem boosted_dyadic_window_producer_consumer_duality_le_levy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ((∀ k ∈ Finset.range N, autocorr f (Real.log ((N + k : ℕ) : ℝ)) = 0) ↔
      (∀ k ∈ Finset.range N,
        autocorr (coshMultiplier α f) (Real.log ((N + k : ℕ) : ℝ)) =
          autocorr (sinhMultiplier α f) (Real.log ((N + k : ℕ) : ℝ)))) ∧
    (∀ (_hboost : ∀ k ∈ Finset.range N,
        autocorr (coshMultiplier α f) (Real.log ((N + k : ℕ) : ℝ)) =
          autocorr (sinhMultiplier α f) (Real.log ((N + k : ℕ) : ℝ)))
      {W : ℝ → ℝ}
      (_hW : ContinuousOn W (Icc (Real.log (N : ℝ)) (Real.log ((2 * N : ℕ) : ℝ)))),
      ((∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), autocorr f x * Real.cosh (x / 2)) +
          (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
            (autocorr f 0 - autocorr f x) * W x) -
          (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), W x) * autocorr f 0) ^ (2 : ℕ) ≤
        2 * autocorr f 0 * biScaleLevyEnergy f *
          ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (Real.cosh (x / 2) - W x) ^ (2 : ℕ)) := by
  have hf_cont : Continuous f := hf.continuous
  have hiff :
      (∀ k ∈ Finset.range N, autocorr f (Real.log ((N + k : ℕ) : ℝ)) = 0) ↔
        (∀ k ∈ Finset.range N,
          autocorr (coshMultiplier α f) (Real.log ((N + k : ℕ) : ℝ)) =
            autocorr (sinhMultiplier α f) (Real.log ((N + k : ℕ) : ℝ))) := by
    refine ⟨fun h k hk => ?_, fun h k hk => ?_⟩
    · exact (autocorr_eq_zero_iff_coshMultiplier_eq_sinhMultiplier hf_cont hfc α
        (Real.log ((N + k : ℕ) : ℝ))).mp (h k hk)
    · exact (autocorr_eq_zero_iff_coshMultiplier_eq_sinhMultiplier hf_cont hfc α
        (Real.log ((N + k : ℕ) : ℝ))).mpr (h k hk)
  refine ⟨hiff, fun hboost {W} hW => ?_⟩
  exact dyadic_window_producer_consumer_duality_le_levy hf hfc hN (hiff.mpr hboost) hW

/-- **Pronic-Indexed Global-Minus-Head Vasyunin–Fermi Tail Gram Identity
(`fermiTailGram_eq_global_sub_sum_pronicSeq`):**
For every cutoff `N : ℕ` and natural scales `d₁, d₂ : ℕ`, the small-`t` origin-tail Fermi–Nyman
Gram entry on `(0, 1 / (N + 1)]` equals `fermiGlobalGram d₁ d₂` minus the finite pronic-weighted
cellular sum over `1 ≤ n ≤ N` with denominator `pronicSeq n`, eliminating finite-`K` Graham
truncation artifacts. -/
theorem fermiTailGram_eq_global_sub_sum_pronicSeq (N d₁ d₂ : ℕ) :
    fermiTailGram N d₁ d₂ =
      fermiGlobalGram d₁ d₂ -
        ((∑ n ∈ Finset.Icc 1 N,
          (fermiCellMatrix (d₁ + 1) n * fermiCellMatrix (d₂ + 1) n) /
            (pronicSeq n : ℝ) : ℝ) : ℂ) := by
  rw [fermiTailGram_eq_global_sub_sum_cellMatrix]
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [cast_pronicSeq_eq_mul_succ]

/-- **Pronic-Indexed Global-Minus-Cell Identity for `singleCellFermiCombinator`
(`integral_normSq_singleCellFermiCombinator_tail_eq_global_sub_pronicSeq`):**
For every `k, N : ℕ`, the small-`t` origin-tail `L²` energy of `singleCellFermiCombinator (k + 1) N`
on `(0, 1 / (N + 1)]` equals its global `L²(0, 1]` energy minus `1 / pronicSeq (k + 1)` when
`k + 1 ≤ N` (and `0` otherwise). -/
theorem integral_normSq_singleCellFermiCombinator_tail_eq_global_sub_pronicSeq (k N : ℕ) :
    (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
      ‖singleCellFermiCombinator (k + 1) N t‖ ^ (2 : ℕ)) =
      (∫ t in Ioc (0 : ℝ) 1, ‖singleCellFermiCombinator (k + 1) N t‖ ^ (2 : ℕ)) -
        (if k + 1 ≤ N then 1 / (pronicSeq (k + 1) : ℝ) else 0) := by
  rw [integral_normSq_singleCellFermiCombinator_tail_eq_global_sub_cell,
    cast_pronicSeq_eq_mul_succ (k + 1)]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
