import GaloisForLFunctions.TransHorizonIncidenceMechanics.QuotientSpectralGapAndOddChainCoercivity
import GaloisForLFunctions.TransHorizonIncidenceMechanics.OddEigenvectorNodalModulusBalanceAndFourthBandStepLaw

/-!
# Equal-Lobe `oneL` Projection, Cross-Free `absGraph` vs. `4 · posGraph` Energy Law, and Strict Prime-Shift Closure (`OddEigenvectorHalfMassLobeAndStrictPrimeShiftClosure`)

This module advances **Step 3 (Sub-route 3A: Nodal-Lobe Balance & Cross-Lobe `oneL`-Defect)** and
**Step 5 (CHMD Spine Receivers)** of the CHMD closure programme
(`docs/reports/TransHorizonIncidenceMechanics/CHMD-programme.md`).

## Classical Baseline & New Mathematical Content

1. **Equal-Lobe `oneL` Projection & Cross-Lobe Rank-1 Reformulation of the Nodal Defect (§1):**
   - *Classical baseline:* A primitive vector $p \in \operatorname{SourceGraph}$ satisfies
     $\langle p.\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}} = 0$, while its positive and negative
     parts $\operatorname{posGraph} p$ and $\operatorname{negGraph} p$ need not vanish on $\text{oneL}$.
   - *New formulation & theorem:* Because $p.\text{val.fst} = (\operatorname{posGraph} p).\text{val.fst} - (\operatorname{negGraph} p).\text{val.fst}$,
     primitivity of $p$ forces its two nodal lobes to have **identical** ground-state projections:
     $$\langle (\operatorname{posGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}
       = \langle (\operatorname{negGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}},$$
     $$\langle (\operatorname{absGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}
       = 2\langle (\operatorname{posGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}.$$
     Consequently, the primitive `oneL`-defect $2\langle (\operatorname{absGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}^2$
     is **not** a diagonal single-lobe penalty, but an exact **cross-lobe rank-1 pairing**:
     $$2\langle (\operatorname{absGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}^2
       = 8\langle (\operatorname{posGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}
         \langle (\operatorname{negGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}},$$
     putting it on the exact same bilinear cross-lobe footing as
     $4\langle \operatorname{primeShiftOperator}(\operatorname{posGraph} p).\text{val.fst}, (\operatorname{negGraph} p).\text{val.fst}\rangle_{\mathbb{R}}$.
     (Classification: **Candidate new theorem**.)

2. **Exact Cross-Free `absGraph` vs. `4 · posGraph` Energy Law & Three-Term Lobe Balance (§2):**
   - *Classical baseline:* Polarization of `sourceEnergy (posGraph q + negGraph q)` introduces the
     cross-term $2\operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q)$.
   - *New formulation & theorem:* Combining the bilateral cross-jump identity
     $\operatorname{sourceEnergy}(\operatorname{absGraph} q) - 4\operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q) = \frac{1 - 2\mu}{\mu}\|q.\text{val.fst}\|^2$
     with the half-mass lobe identity
     $\operatorname{sourceEnergy}(\operatorname{posGraph} q) = \frac{1 - 2\mu}{2\mu}\|q.\text{val.fst}\|^2 + \operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q)$
     eliminates $\operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q)$
     identically, yielding the cross-free law:
     $$\operatorname{sourceEnergy}(\operatorname{absGraph} q) - 4\,\operatorname{sourceEnergy}(\operatorname{posGraph} q)
       = \frac{2\mu - 1}{\mu}\|q.\text{val.fst}\|^2,$$
     $$\operatorname{sourceEnergy}(\operatorname{absGraph} q)
       = 4\|(\operatorname{posGraph} q).\text{val.snd}\|^2 - \frac{1}{\mu}\|q.\text{val.fst}\|^2.$$
     Furthermore, on the odd sector, the three-term non-negative lobe decomposition simplifies to
     $$\|(\operatorname{posGraph} q).\text{val.snd}\|^2
       - \langle (\operatorname{fullGroundEquiv}(\operatorname{posGraph} q)).\text{val.snd}, (\operatorname{fullGroundEquiv}(\operatorname{negGraph} q)).\text{val.snd}\rangle_{\mathbb{R}}
       + \langle \operatorname{primeShiftOperator}(\operatorname{posGraph} q).\text{val.fst}, (\operatorname{negGraph} q).\text{val.fst}\rangle_{\mathbb{R}}
       = \frac{1 - \mu}{2\mu}\|q.\text{val.fst}\|^2.$$
     (Classification: **Candidate new theorem**.)

3. **Strict Prime-Shift Cross-Dominance Exclusion (`μ < 1/2`) and Cross-Free `RiemannHypothesis` Equivalence (§3):**
   - *New formulation & theorem:* Whenever the cross-lobe rank-1 `oneL` pairing
     $2\langle (\operatorname{posGraph} q).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}\langle (\operatorname{negGraph} q).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}$
     is dominated by the prime-shift cross-lobe pairing
     $\langle \operatorname{primeShiftOperator}(\operatorname{posGraph} q).\text{val.fst}, (\operatorname{negGraph} q).\text{val.fst}\rangle_{\mathbb{R}}$
     alone (under critical-threshold contraction $\mu_{\max} = 1/2$ on $\operatorname{primGraph}(\operatorname{absGraph} q)$),
     strict positivity of the stationary Beurling–Deny cross-jump forces the **strict** bound
     $\mu < 1/2$ (`odd_eigenvector_eigenvalue_lt_half_of_cross_lobe_oneL_le_primeShift`).
     Moreover, `RiemannHypothesis` is unconditionally equivalent to the cross-free lobe scaling
     inequality $\operatorname{sourceEnergy}(\operatorname{absGraph} q) \le 4\,\operatorname{sourceEnergy}(\operatorname{posGraph} q)$
     for all odd eigenvectors (`riemannHypothesis_iff_forall_odd_eigenvector_absGraph_le_four_posGraph`).
     (Classification: **Candidate new theorem**.)
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDClosedJump RHTower.CHMDPolar
open scoped InnerProductSpace BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Equal-Lobe `oneL` Projection & Cross-Lobe Rank-1 Reformulation of the Nodal Defect -/

/-- **Equal-Lobe `oneL` Projection for Primitive Graph Vectors
(`inner_posGraph_oneL_eq_inner_negGraph_oneL`):**
For every primitive graph vector `p : SourceGraph` (`⟪p.val.fst, oneL⟫_ℝ = 0`), its positive and
negative nodal lobes have identical inner products with the ground state `oneL`, and
`⟪(absGraph p).val.fst, oneL⟫_ℝ` equals twice the single-lobe `oneL` inner product.
(Classification: Candidate new theorem.) -/
theorem inner_posGraph_oneL_eq_inner_negGraph_oneL {p : SourceGraph}
    (hprim : ⟪p.val.fst, oneL⟫_ℝ = 0) :
    ⟪(posGraph p).val.fst, oneL⟫_ℝ = ⟪(negGraph p).val.fst, oneL⟫_ℝ ∧
      ⟪(absGraph p).val.fst, oneL⟫_ℝ = 2 * ⟪(posGraph p).val.fst, oneL⟫_ℝ ∧
      ⟪(absGraph p).val.fst, oneL⟫_ℝ = 2 * ⟪(negGraph p).val.fst, oneL⟫_ℝ := by
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst := by
    have h := posGraph_sub_negGraph p
    exact congrArg (fun q : SourceGraph => q.val.fst) h.symm
  have hadd : (absGraph p).val.fst = (posGraph p).val.fst + (negGraph p).val.fst := by
    have h := posGraph_add_negGraph p
    exact congrArg (fun q : SourceGraph => q.val.fst) h.symm
  have h1 : ⟪(posGraph p).val.fst, oneL⟫_ℝ - ⟪(negGraph p).val.fst, oneL⟫_ℝ = 0 := by
    rw [← inner_sub_left, ← hsub, hprim]
  have h2 : ⟪(absGraph p).val.fst, oneL⟫_ℝ =
      ⟪(posGraph p).val.fst, oneL⟫_ℝ + ⟪(negGraph p).val.fst, oneL⟫_ℝ := by
    rw [hadd, inner_add_left]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **Cross-Lobe Rank-1 Identity for the `absGraph` Ground Defect
(`oneL_defect_absGraph_eq_eight_posGraph_negGraph`):**
For every primitive graph vector `p : SourceGraph` (`⟪p.val.fst, oneL⟫_ℝ = 0`),
$$2\langle (\operatorname{absGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}^2
  = 8\langle (\operatorname{posGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}
    \langle (\operatorname{negGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}
  = 8\langle (\operatorname{posGraph} p).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}^2.$$
(Classification: Candidate new theorem.) -/
theorem oneL_defect_absGraph_eq_eight_posGraph_negGraph {p : SourceGraph}
    (hprim : ⟪p.val.fst, oneL⟫_ℝ = 0) :
    2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ (2 : ℕ) =
        8 * (⟪(posGraph p).val.fst, oneL⟫_ℝ * ⟪(negGraph p).val.fst, oneL⟫_ℝ) ∧
      2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ (2 : ℕ) =
        8 * ⟪(posGraph p).val.fst, oneL⟫_ℝ ^ (2 : ℕ) := by
  obtain ⟨heq, hpos, _⟩ := inner_posGraph_oneL_eq_inner_negGraph_oneL hprim
  constructor
  · rw [hpos, ← heq]
    ring
  · rw [hpos]
    ring

/-- Every odd graph vector `p : SourceGraph` (`reflectGraph p = -p`) satisfies the equal-lobe and
cross-lobe rank-1 `oneL` identities unconditionally.
(Classification: Corollary.) -/
theorem odd_oneL_defect_absGraph_eq_eight_posGraph_negGraph {p : SourceGraph}
    (hodd : reflectGraph p = -p) :
    ⟪(posGraph p).val.fst, oneL⟫_ℝ = ⟪(negGraph p).val.fst, oneL⟫_ℝ ∧
      2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ (2 : ℕ) =
        8 * (⟪(posGraph p).val.fst, oneL⟫_ℝ * ⟪(negGraph p).val.fst, oneL⟫_ℝ) := by
  have hodd_fst : reflectMass p.val.fst = -p.val.fst := by
    rw [← reflectGraph_fst, hodd]
    rfl
  have hprim : ⟪p.val.fst, oneL⟫_ℝ = 0 := inner_oneL_eq_zero_of_odd hodd_fst
  exact ⟨(inner_posGraph_oneL_eq_inner_negGraph_oneL hprim).1,
    (oneL_defect_absGraph_eq_eight_posGraph_negGraph hprim).1⟩

/-! ## §2. Exact Cross-Free `absGraph` vs. `4 · posGraph` Energy Law & Three-Term Lobe Balance -/

/-- **Exact Cross-Free `absGraph` vs. `4 · posGraph` Energy Law for Odd Eigenvectors
(`odd_eigenvector_sourceEnergy_absGraph_sub_four_posGraph_eq`):**
For every odd eigenvector `resolvent w = μ • w` (`μ ≠ 0`, `reflectMass w = -w`) with
`q = rieszLift w`, the cross-lobe pairing `sourcePair (posGraph q) (negGraph q)` cancels
identically between `sourceEnergy (absGraph q)` and `4 * sourceEnergy (posGraph q)`:
$$\operatorname{sourceEnergy}(\operatorname{absGraph} q) - 4\,\operatorname{sourceEnergy}(\operatorname{posGraph} q)
  = \frac{2\mu - 1}{\mu}\|q.\text{val.fst}\|^2,$$
$$\operatorname{sourceEnergy}(\operatorname{absGraph} q) - 4\,\operatorname{sourceEnergy}(\operatorname{negGraph} q)
  = \frac{2\mu - 1}{\mu}\|q.\text{val.fst}\|^2.$$
(Classification: Candidate new theorem.) -/
theorem odd_eigenvector_sourceEnergy_absGraph_sub_four_posGraph_eq {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (hodd : reflectMass w = -w) (heig : resolvent w = μ • w) :
    let q := rieszLift w
    sourceEnergy (absGraph q) - 4 * sourceEnergy (posGraph q) =
        ((2 * μ - 1) / μ) * ‖q.val.fst‖ ^ (2 : ℕ) ∧
      sourceEnergy (absGraph q) - 4 * sourceEnergy (negGraph q) =
        ((2 * μ - 1) / μ) * ‖q.val.fst‖ ^ (2 : ℕ) := by
  dsimp only
  have hbil1 := (eigenvector_sourceEnergy_absGraph_sub_four_sourcePair_eq hμ heig).1
  obtain ⟨_, hpos, hneg, _, _⟩ := odd_eigenvector_lobe_energy_and_snd_sq hμ hodd heig
  have halg : ((1 - 2 * μ) / μ) * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ) -
      4 * (((1 - 2 * μ) / (2 * μ)) * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ)) =
      ((2 * μ - 1) / μ) * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ) := by
    field_simp [hμ]; ring
  have h1 : sourceEnergy (absGraph (rieszLift w)) - 4 * sourceEnergy (posGraph (rieszLift w)) =
      ((2 * μ - 1) / μ) * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ) := by
    linear_combination hbil1 - 4 * hpos - halg
  have heq_lobe : sourceEnergy (posGraph (rieszLift w)) =
      sourceEnergy (negGraph (rieszLift w)) := hpos.trans hneg.symm
  have h2 : sourceEnergy (absGraph (rieszLift w)) - 4 * sourceEnergy (negGraph (rieszLift w)) =
      ((2 * μ - 1) / μ) * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ) := by
    rw [← heq_lobe]
    exact h1
  exact ⟨h1, h2⟩

/-- **Exact Edge-Norm Formula for `sourceEnergy (absGraph q)` of an Odd Eigenvector
(`odd_eigenvector_sourceEnergy_absGraph_eq_four_posGraph_snd_sub`):**
For every odd eigenvector `resolvent w = μ • w` (`μ ≠ 0`, `reflectMass w = -w`) with
`q = rieszLift w`:
$$\operatorname{sourceEnergy}(\operatorname{absGraph} q)
  = 4\|(\operatorname{posGraph} q).\text{val.snd}\|^2 - \frac{1}{\mu}\|q.\text{val.fst}\|^2.$$
(Classification: Candidate new theorem.) -/
theorem odd_eigenvector_sourceEnergy_absGraph_eq_four_posGraph_snd_sub {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (hodd : reflectMass w = -w) (heig : resolvent w = μ • w) :
    let q := rieszLift w
    sourceEnergy (absGraph q) =
      4 * ‖(posGraph q).val.snd‖ ^ (2 : ℕ) - (1 / μ) * ‖q.val.fst‖ ^ (2 : ℕ) := by
  dsimp only
  have hbil1 := (eigenvector_sourceEnergy_absGraph_sub_four_sourcePair_eq hμ heig).1
  obtain ⟨_, _, _, hsnd, _⟩ := odd_eigenvector_lobe_energy_and_snd_sq hμ hodd heig
  have halg : 4 * (((1 - μ) / (2 * μ)) * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ)) -
      (1 / μ) * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ) =
      ((1 - 2 * μ) / μ) * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ) := by
    field_simp [hμ]; ring
  linear_combination hbil1 - 4 * hsnd - halg

/-- **Half-Mass Three-Term Non-Negative Lobe Balance for Odd Eigenvectors
(`odd_eigenvector_three_term_lobe_balance`):**
For every odd eigenvector `resolvent w = μ • w` (`μ ≠ 0`, `reflectMass w = -w`) with
`q = rieszLift w`, the three non-negative nodal quantities — the lobe edge norm-squared, the
stationary cross-jump penalty, and the prime-shift cross-jump pairing — sum to
$\frac{1 - \mu}{2\mu}\|q.\text{val.fst}\|^2$:
$$\|(\operatorname{posGraph} q).\text{val.snd}\|^2
  - \langle (\operatorname{fullGroundEquiv}(\operatorname{posGraph} q)).\text{val.snd}, (\operatorname{fullGroundEquiv}(\operatorname{negGraph} q)).\text{val.snd}\rangle_{\mathbb{R}}
  + \langle \operatorname{primeShiftOperator}(\operatorname{posGraph} q).\text{val.fst}, (\operatorname{negGraph} q).\text{val.fst}\rangle_{\mathbb{R}}
  = \frac{1 - \mu}{2\mu}\|q.\text{val.fst}\|^2.$$
(Classification: Candidate new theorem.) -/
theorem odd_eigenvector_three_term_lobe_balance {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (hodd : reflectMass w = -w) (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ‖(posGraph q).val.snd‖ ^ (2 : ℕ) -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ =
      ((1 - μ) / (2 * μ)) * ‖q.val.fst‖ ^ (2 : ℕ) := by
  dsimp only
  have h3 := posGraph_three_term_nonneg_decomposition_of_eigenvector hμ heig
  dsimp only at h3
  obtain ⟨hrefl, _, _, _, _⟩ := odd_eigenvector_lobe_energy_and_snd_sq hμ hodd heig
  obtain ⟨hf_pos, _⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hrefl
  have halg : ((1 - μ) / μ) * (1 / 2 * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ)) =
      ((1 - μ) / (2 * μ)) * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ) := by ring
  rw [hf_pos, halg] at h3
  exact h3

/-- **Strict Negativity of Individual Nodal-Lobe Energies for Above-Threshold Odd Eigenvectors
(`odd_eigenvector_gt_half_lobe_energy_neg`):**
For every nonzero odd eigenvector `resolvent w = μ • w` with $\mu > 1/2$ and $q = \operatorname{rieszLift} w$,
each one-signed nodal lobe $\operatorname{posGraph} q$ and $\operatorname{negGraph} q$ has strictly
negative `sourceEnergy`:
$$\operatorname{sourceEnergy}(\operatorname{posGraph} q)
  = \operatorname{sourceEnergy}(\operatorname{negGraph} q)
  \le \frac{1 - 2\mu}{2\mu}\|q.\text{val.fst}\|^2 < 0.$$
(Classification: Corollary.) -/
theorem odd_eigenvector_gt_half_lobe_energy_neg {μ : ℝ} (hμ : 1 / 2 < μ)
    {w : MassSpace} (hw0 : w ≠ 0) (hodd : reflectMass w = -w) (heig : resolvent w = μ • w) :
    let q := rieszLift w
    sourceEnergy (posGraph q) = sourceEnergy (negGraph q) ∧
      sourceEnergy (posGraph q) ≤ ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ (2 : ℕ) ∧
      ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ (2 : ℕ) < 0 := by
  intro q
  have hμ0 : 0 < μ := by linarith
  obtain ⟨_, hpos, hneg, _, _⟩ := odd_eigenvector_lobe_energy_and_snd_sq hμ0.ne' hodd heig
  have hsp_nonpos : sourcePair (posGraph q) (negGraph q) ≤ 0 :=
    sourcePair_posGraph_negGraph_nonpos q
  have hfst : q.val.fst = μ • w := heig
  have hq0 : q.val.fst ≠ 0 := by
    rw [hfst]; exact smul_ne_zero hμ0.ne' hw0
  have hq_sq_pos : 0 < ‖q.val.fst‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hq0)
  have hneg_term : ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ (2 : ℕ) < 0 :=
    mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) (by linarith)) hq_sq_pos
  exact ⟨hpos.trans hneg.symm, by linarith, hneg_term⟩

/-! ## §3. Strict Prime-Shift Cross-Dominance Exclusion (`μ < 1/2`) and Cross-Free `RiemannHypothesis` Equivalence -/

/-- **Strict Eigenvalue Exclusion (`μ < 1/2`) from Cross-Lobe Prime-Shift Dominance
(`odd_eigenvector_eigenvalue_lt_half_of_cross_lobe_oneL_le_primeShift`):**
For any nonzero odd eigenvector `resolvent w = μ • w` (`0 < μ`, `w ≠ 0`, `reflectMass w = -w`) with
`q = rieszLift w`, if `u_0 = (primGraph (absGraph q)).val.fst` satisfies the critical-line Rayleigh
bound `⟪resolvent u_0, u_0⟫_ℝ ≤ (1 / 2) * ‖u_0‖ ^ 2` and the cross-lobe `oneL` pairing is dominated
by the cross-lobe prime-shift pairing alone:
$$2\langle (\operatorname{posGraph} q).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}
    \langle (\operatorname{negGraph} q).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}
  \le \langle \operatorname{primeShiftOperator}(\operatorname{posGraph} q).\text{val.fst},
    (\operatorname{negGraph} q).\text{val.fst}\rangle_{\mathbb{R}},$$
then strict positivity of the stationary cross-jump across the nodal interface forces the **strict**
eigenvalue bound $\mu < 1/2$.
(Classification: Candidate new theorem.) -/
theorem odd_eigenvector_eigenvalue_lt_half_of_cross_lobe_oneL_le_primeShift
    {μ : ℝ} (hμ : 0 < μ) {w : MassSpace} (hw0 : w ≠ 0)
    (hodd : reflectMass w = -w) (heig : resolvent w = μ • w)
    (hray : ⟪resolvent (primGraph (absGraph (rieszLift w))).val.fst,
        (primGraph (absGraph (rieszLift w))).val.fst⟫_ℝ ≤
      (1 / 2 : ℝ) * ‖(primGraph (absGraph (rieszLift w))).val.fst‖ ^ (2 : ℕ))
    (hdom : 2 * (⟪(posGraph (rieszLift w)).val.fst, oneL⟫_ℝ *
        ⟪(negGraph (rieszLift w)).val.fst, oneL⟫_ℝ) ≤
      ⟪primeShiftOperator (posGraph (rieszLift w)).val.fst,
        (negGraph (rieszLift w)).val.fst⟫_ℝ) :
    μ < 1 / 2 := by
  have hprim_w : ⟪w, oneL⟫_ℝ = 0 := inner_oneL_eq_zero_of_odd hodd
  obtain ⟨hrefl, _, _, _, _⟩ := odd_eigenvector_lobe_energy_and_snd_sq hμ.ne' hodd heig
  have hdefect := (odd_oneL_defect_absGraph_eq_eight_posGraph_negGraph hrefl).2
  have hdom' : ((1 - (1 / 2 : ℝ)) / (1 / 2 : ℝ)) *
      (2 * ⟪(absGraph (rieszLift w)).val.fst, oneL⟫_ℝ ^ (2 : ℕ)) ≤
      4 * ⟪primeShiftOperator (posGraph (rieszLift w)).val.fst,
        (negGraph (rieszLift w)).val.fst⟫_ℝ := by
    rw [hdefect]
    linarith
  exact eigenvalue_lt_of_primitive_oneL_defect_le_four_primeShift
    hμ (by norm_num : (0 : ℝ) < 1 / 2) hw0 hprim_w heig hray hdom'

/-- **Cross-Lobe Prime-Shift Sufficiency Criterion for `RiemannHypothesis`
(`riemannHypothesis_of_odd_eigenvector_cross_lobe_oneL_le_primeShift`):**
If for every nonzero odd eigenvector `resolvent w = μ • w` with $\mu \in (1/2, 1)$ and
`q = rieszLift w`, `u_0 = (primGraph (absGraph q)).val.fst` satisfies
`⟪resolvent u_0, u_0⟫_ℝ ≤ (1 / 2) * ‖u_0‖ ^ 2` and
$2\langle (\operatorname{posGraph} q).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}}\langle (\operatorname{negGraph} q).\text{val.fst}, \text{oneL}\rangle_{\mathbb{R}} \le \langle \operatorname{primeShiftOperator}(\operatorname{posGraph} q).\text{val.fst}, (\operatorname{negGraph} q).\text{val.fst}\rangle_{\mathbb{R}}$,
then `RiemannHypothesis` holds.
(Classification: Corollary.) -/
theorem riemannHypothesis_of_odd_eigenvector_cross_lobe_oneL_le_primeShift
    (h : ∀ (μ : ℝ) (w : MassSpace),
      μ ∈ Set.Ioo (1 / 2 : ℝ) 1 → w ≠ 0 → reflectMass w = -w → resolvent w = μ • w →
      ⟪resolvent (primGraph (absGraph (rieszLift w))).val.fst,
          (primGraph (absGraph (rieszLift w))).val.fst⟫_ℝ ≤
        (1 / 2 : ℝ) * ‖(primGraph (absGraph (rieszLift w))).val.fst‖ ^ (2 : ℕ) ∧
      2 * (⟪(posGraph (rieszLift w)).val.fst, oneL⟫_ℝ *
          ⟪(negGraph (rieszLift w)).val.fst, oneL⟫_ℝ) ≤
        ⟪primeShiftOperator (posGraph (rieszLift w)).val.fst,
          (negGraph (rieszLift w)).val.fst⟫_ℝ) :
    RiemannHypothesis := by
  by_contra hnot
  obtain ⟨μ, w, hμ, hw0, hodd, heig⟩ :=
    not_riemannHypothesis_iff_exists_odd_eigenvector_mem_Ioo_half_one.mp hnot
  obtain ⟨hray, hdom⟩ := h μ w hμ hw0 hodd heig
  have hlt := odd_eigenvector_eigenvalue_lt_half_of_cross_lobe_oneL_le_primeShift
    (by linarith [hμ.1]) hw0 hodd heig hray hdom
  linarith [hμ.1]

/-- **Unconditional Cross-Free `absGraph ≤ 4 · posGraph` Equivalence for `RiemannHypothesis`
(`riemannHypothesis_iff_forall_odd_eigenvector_absGraph_le_four_posGraph`):**
`RiemannHypothesis` holds if and only if for every nonzero odd eigenvector `resolvent w = μ • w`
(`0 < μ`, `reflectMass w = -w`) with `q = rieszLift w`:
$$\operatorname{sourceEnergy}(\operatorname{absGraph} q)
  \le 4\,\operatorname{sourceEnergy}(\operatorname{posGraph} q).$$
(Classification: Candidate new theorem.) -/
theorem riemannHypothesis_iff_forall_odd_eigenvector_absGraph_le_four_posGraph :
    RiemannHypothesis ↔
      ∀ (μ : ℝ) (w : MassSpace),
        0 < μ → w ≠ 0 → reflectMass w = -w → resolvent w = μ • w →
        sourceEnergy (absGraph (rieszLift w)) ≤ 4 * sourceEnergy (posGraph (rieszLift w)) := by
  constructor
  · intro hrh μ w hμ hw0 hodd heig
    have hle_half : μ ≤ 1 / 2 := by
      by_contra hgt
      push Not at hgt
      have hlt_one : μ < 1 := odd_eigenvector_eigenvalue_lt_one hw0 hodd heig
      exact not_riemannHypothesis_iff_exists_odd_eigenvector_mem_Ioo_half_one.mpr
        ⟨μ, w, ⟨hgt, hlt_one⟩, hw0, hodd, heig⟩ hrh
    have hid := (odd_eigenvector_sourceEnergy_absGraph_sub_four_posGraph_eq hμ.ne' hodd heig).1
    have hnonpos : ((2 * μ - 1) / μ) * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (by linarith) hμ.le)
        (sq_nonneg _)
    linarith
  · intro h
    by_contra hnot
    obtain ⟨μ, w, hμ, hw0, hodd, heig⟩ :=
      not_riemannHypothesis_iff_exists_odd_eigenvector_mem_Ioo_half_one.mp hnot
    have hμ0 : 0 < μ := by linarith [hμ.1]
    have hle := h μ w hμ0 hw0 hodd heig
    have hid := (odd_eigenvector_sourceEnergy_absGraph_sub_four_posGraph_eq hμ0.ne' hodd heig).1
    have hfst : (rieszLift w).val.fst = μ • w := heig
    have hq0 : (rieszLift w).val.fst ≠ 0 := by
      rw [hfst]; exact smul_ne_zero hμ0.ne' hw0
    have hpos : 0 < ((2 * μ - 1) / μ) * ‖(rieszLift w).val.fst‖ ^ (2 : ℕ) :=
      mul_pos (div_pos (by linarith [hμ.1]) hμ0) (sq_pos_of_pos (norm_pos_iff.mpr hq0))
    linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
