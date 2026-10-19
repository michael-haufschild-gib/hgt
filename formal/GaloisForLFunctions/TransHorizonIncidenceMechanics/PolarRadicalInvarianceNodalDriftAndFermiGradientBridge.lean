import GaloisForLFunctions.TransHorizonIncidenceMechanics.CollectiveLowPrimeChebyshevTransportAndSinhAbsorption
import GaloisForLFunctions.TransHorizonIncidenceMechanics.OddEigenvectorHalfMassLobeAndStrictPrimeShiftClosure
import GaloisForLFunctions.RHTower.CHMDUniversalRieszResolventAndCardinalKernelEquations
import GaloisForLFunctions.RHTower.CHMDOddBoundStateSignObstructionAndParityQuarterBound
import GaloisForLFunctions.RHTower.CHMDResolventNodalCrossPositivityAndBalancedRayleighExcess
import GaloisForLFunctions.RHTower.CHMDStationaryStrictContractionAndSecondResolventIdentity
import GaloisForLFunctions.BiScaleUncertainty.EulerPoissonChiralDriftAndPrimeShiftRigidity
import GaloisForLFunctions.BezoutValuationIncidence.AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization
import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusGradientCoercivityAndRenormalizedDefect

/-!
# Cross-Shift Polar Radical Invariance, Odd Nodal Chiral-Drift Tightening, & Second-Octave Fermi–Gradient Reciprocity (`PolarRadicalInvarianceNodalDriftAndFermiGradientBridge`)

This module synthesizes existing structural results from across the Lean corpus
(`RHTower`, `BiScaleUncertainty`, and `BezoutValuationIncidence`) into three unified pillars for
**Trans-Horizon Incidence Mechanics**:

## 1. Cross-Shift Radical Invariance of `oddPolarVectorAt`, Universal `oddPrimitivePart` Annihilation, & Pole-Moment Closure of `convex_doob_chain_sinh_absorption_le_one` (§1)

- **Cross-Shift Radical Invariance & Pole-Moment Identity (`sourcePair_oddPolarVectorAt_eq_of_admissible`):**
  By `oddPolarVectorAt_sub_mem_signedRadical_and_resolvent_eq_half` and
  `sourcePair_oddPolarVectorAt_eq_inner_tanhL` (`CHMDUniversalRieszResolventAndCardinalKernelEquations`),
  the difference $\Psi_a - \Psi_b$ of any two normalized odd polar ground vectors lies in
  $\operatorname{signedRadical}$, and for every $q \in \operatorname{SourceGraph}$,
  $$\operatorname{sourcePair}(\Psi_a, q) = \operatorname{sourcePair}(\Psi_b, q)
    = \langle q.\text{val}.\text{fst}, \operatorname{tanhL}\rangle_{\mathbb{R}}.$$
- **Universal Cross-Shift Annihilation of `oddPrimitivePart` (`sourcePair_oddPolarVectorAt_oddPrimitivePart_eq_zero`):**
  For **any** two nonzero admissible shifts $a, b$ (even when $a \ne b$), the odd polar reduction
  $\operatorname{oddPrimitivePart}\,b\,hb\,q = q - 2\langle q.\text{val}.\text{fst}, \operatorname{tanhL}\rangle_{\mathbb{R}}\,\Psi_b$
  (`CHMDOddBoundStateSignObstructionAndParityQuarterBound`) is `sourcePair`-orthogonal to $\Psi_a$:
  $$\operatorname{sourcePair}(\Psi_a, \operatorname{oddPrimitivePart}\,b\,hb\,q) = 0,$$
  and for every primitive (in particular, every odd) graph vector $q$,
  $$\operatorname{sourceEnergy}(q) = \operatorname{weilForm}(q) + 2\,\operatorname{sourcePair}(\Psi_a, q)^2$$
  (`primitive_sourceEnergy_eq_weilForm_add_two_sourcePair_oddPolarVectorAt_sq`,
  `odd_sourceEnergy_eq_weilForm_add_two_sourcePair_oddPolarVectorAt_sq`).
- **Cross-Shift & Pole-Moment Closure of the Unit-Coefficient `sinh` Absorption Law
  (`convex_doob_chain_sinh_absorption_cross_shift_and_tanhL`):**
  Strengthening `convex_doob_chain_sinh_absorption_le_one`
  (`CollectiveLowPrimeChebyshevTransportAndSinhAbsorption`), the residual polar pairing
  $\theta\,\operatorname{sourcePair}(\Psi_a, p)$ is invariant under replacing $a$ by any fixed
  reference shift $b$ and equals the shift-independent pole moment
  $\theta\,\langle p.\text{val}.\text{fst}, \operatorname{tanhL}\rangle_{\mathbb{R}}$.

## 2. Odd-Eigenvector Primitive Modulus Resolvent Excess, Stationary `absGraph` Cauchy–Schwarz, & Nodal Chiral-Drift Tightening (§2)

- **Exact Cross-Lobe Primitive Modulus Rayleigh Excess (`primitive_eigenvector_resolvent_primGraph_absGraph_excess_eq_cross_lobe`, `odd_eigenvector_primGraph_absGraph_rayleigh_excess_and_cross_pos`):**
  Combining `inner_resolvent_primGraph_fst`, `inner_resolvent_absGraph_of_eigenvector`, and
  `neg_sq_mul_sourcePair_le_inner_resolvent_posGraph_negGraph`
  (`CHMDResolventNodalCrossPositivityAndBalancedRayleighExcess`) with the cross-lobe rank-1
  `oneL` identity (`oneL_defect_absGraph_eq_eight_posGraph_negGraph` from
  `OddEigenvectorHalfMassLobeAndStrictPrimeShiftClosure`), every primitive eigenvector
  $\operatorname{resolvent} v = \nu \cdot v$ ($q = \operatorname{rieszLift} v$) satisfies:
  $$\langle \operatorname{resolvent}(\operatorname{primGraph}(\operatorname{absGraph} q)).\text{fst},
      (\operatorname{primGraph}(\operatorname{absGraph} q)).\text{fst}\rangle_{\mathbb{R}}
    - \nu\,\|\operatorname{primGraph}(\operatorname{absGraph} q).\text{fst}\|^2$$
  $$= 4\Bigl(\langle \operatorname{resolvent}(\operatorname{posGraph} q).\text{fst}, (\operatorname{negGraph} q).\text{fst}\rangle_{\mathbb{R}}
    - 2(1 - \nu)\langle (\operatorname{posGraph} q).\text{fst}, \text{oneL}\rangle_{\mathbb{R}}
      \langle (\operatorname{negGraph} q).\text{fst}, \text{oneL}\rangle_{\mathbb{R}}\Bigr),$$
  with $0 < -\nu^2 \operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q)
  \le \langle \operatorname{resolvent}(\operatorname{posGraph} q).\text{fst}, (\operatorname{negGraph} q).\text{fst}\rangle_{\mathbb{R}}$
  whenever $\nu > 0$ and $v \ne 0$.
- **Single-Lobe Edge-Norm Form of the Stationary `absGraph` Cauchy–Schwarz Bound
  (`odd_eigenvector_stationaryResolvent_absGraph_via_posGraph_snd`):**
  Combining `eigenvector_norm_pow_four_le_stationaryResolvent_absGraph_mul`
  (`CHMDStationaryStrictContractionAndSecondResolventIdentity`) with
  `odd_eigenvector_sourceEnergy_absGraph_eq_four_posGraph_snd_sub` eliminates the bilateral
  cross-jump $4\operatorname{sourcePair}(\operatorname{posGraph} q, \operatorname{negGraph} q)$ in
  favor of $4\|(\operatorname{posGraph} q).\text{val}.\text{snd}\|^2 - \frac{1 - \mu}{\mu}\|q.\text{val}.\text{fst}\|^2$.
- **Unconditional Nodal Chiral-Drift Tightening on the Odd Sector
  (`odd_posGraph_and_negGraph_primeShift_sq_add_quarter_absGraph_drift_sq_le`):**
  Combining `inner_oddPrimeDriftOperator_self_eq_zero_of_odd` and
  `posGraph_and_negGraph_primeShift_sq_add_quarter_absGraph_drift_sq_le`
  (`EulerPoissonChiralDriftAndPrimeShiftRigidity`), every odd graph vector $q$ (`reflectGraph q = -q`)
  satisfies on **both** nodal lobes:
  $$\langle \operatorname{primeShiftOperator}(\operatorname{posGraph} q).\text{fst}, (\operatorname{posGraph} q).\text{fst}\rangle_{\mathbb{R}}^2
    + \frac{1}{4}\langle \operatorname{oddPrimeDriftOperator} q.\text{fst}, (\operatorname{absGraph} q).\text{fst}\rangle_{\mathbb{R}}^2
    \le \langle \operatorname{primeDiagonalOperator}(\operatorname{posGraph} q).\text{fst}, (\operatorname{posGraph} q).\text{fst}\rangle_{\mathbb{R}}^2.$$

## 3. Second-Octave Odd-Cell Fermi Curvature–Gradient Reciprocity & Squarefree Energy Lower Bound (§3)

- **Second-Octave Odd-Cell Fermi Curvature–Gradient Identity
  (`fermiCellResponse_second_diff_add_addDiff_eq_neg_two_moebiusReal_second_octave`):**
  Combining `fermiCellResponse_second_diff_across_odd_eq_two_half_sub_addDiff`
  (`AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization`) with `sieveSeq_moebiusReal_first_octave`,
  for every $N \in \mathbb{N}$ and every $m \in [N, 2N - 1]$ (so $2m + 1 \in [2N + 1, 4N - 1]$ lies
  in the second trans-horizon octave while its half-scale parent $m + 1 \in [N + 1, 2N]$ lies in the
  first trans-horizon octave), the second-order difference of `fermiCellResponse N moebiusReal`
  centered at $2m + 1$ plus the BVI forward gradient `addDiff (sieveSeq N moebiusReal) (2 * m + 1)`
  equals $-2\,\mu(m + 1)$.
- **Second-Octave Squarefree Energy Lower Bound (`two_mul_sum_moebiusReal_sq_le_sum_second_octave_fermi_and_gradient_sq`, `two_mul_oddSquarefreeWindow_card_le_sum_second_octave_fermi_and_gradient_sq`):**
  By Cauchy–Schwarz $(A + B)^2 \le 2(A^2 + B^2)$, summing over $m \in \operatorname{Ico} N (2N)$
  bounds the combined second-octave Fermi curvature and BVI forward gradient energy below by twice
  the first-octave squarefree count, and in particular by $2 \cdot \#(\operatorname{oddSquarefreeWindow} N)$
  (`CofinalMobiusGradientCoercivityAndRenormalizedDefect`).
-/

open MeasureTheory Set Filter Topology Complex Finset
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDClosedJump RHTower.CHMDPolar RHTower.Sieve
open RHTower.ThetaSourceWard RHTower.PhiDivisorEnergy RHTower.CHMDPrimeCuts RHTower.CHMDPrimeChainSource
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open scoped InnerProductSpace BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Cross-Shift Radical Invariance of `oddPolarVectorAt`, Universal `oddPrimitivePart` Annihilation, & Pole-Moment Closure -/

/-- **Cross-Shift Radical Invariance & Pole-Moment Identity for `oddPolarVectorAt`:**
For any two nonzero admissible shifts `a, b` and any `q : SourceGraph`,
`sourcePair (oddPolarVectorAt a ha) q` equals `sourcePair (oddPolarVectorAt b hb) q` and coincides
with the shift-independent pole moment `⟪q.val.fst, tanhL⟫_ℝ`. -/
theorem sourcePair_oddPolarVectorAt_eq_of_admissible {a b : ℝ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (hb : 1 < 2 * Real.exp (-2 * |b|))
    (q : SourceGraph) :
    sourcePair (oddPolarVectorAt a ha) q = sourcePair (oddPolarVectorAt b hb) q ∧
      sourcePair (oddPolarVectorAt a ha) q = ⟪q.val.fst, tanhL⟫_ℝ := by
  have ha_eq := sourcePair_oddPolarVectorAt_eq_inner_tanhL ha0 ha q
  have hb_eq := sourcePair_oddPolarVectorAt_eq_inner_tanhL hb0 hb q
  have hcomm : ⟪tanhL, q.val.fst⟫_ℝ = ⟪q.val.fst, tanhL⟫_ℝ := real_inner_comm q.val.fst tanhL
  exact ⟨ha_eq.trans hb_eq.symm, ha_eq.trans hcomm⟩

/-- **Universal Cross-Shift Annihilation of `oddPrimitivePart`:**
For any two nonzero admissible shifts `a, b` (even when `a ≠ b`) and any `q : SourceGraph`, the
polar-reduced vector `oddPrimitivePart b hb q` is `sourcePair`-orthogonal to `oddPolarVectorAt a ha`. -/
theorem sourcePair_oddPolarVectorAt_oddPrimitivePart_eq_zero {a b : ℝ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (hb : 1 < 2 * Real.exp (-2 * |b|))
    (q : SourceGraph) :
    sourcePair (oddPolarVectorAt a ha) (oddPrimitivePart b hb q) = 0 := by
  rw [(sourcePair_oddPolarVectorAt_eq_of_admissible ha0 hb0 ha hb (oddPrimitivePart b hb q)).2,
    inner_oddPrimitivePart_tanhL hb0 hb q]

/-- **Orthogonal `weilForm` + Polar-Square Decomposition of `sourceEnergy` for Primitive Vectors:**
For every nonzero admissible shift `a` and every primitive graph vector `q : SourceGraph`
(`⟪q.val.fst, oneL⟫_ℝ = 0`), `sourceEnergy q` equals `weilForm q` plus twice the squared polar
pairing `2 * sourcePair (oddPolarVectorAt a ha) q ^ 2`. -/
theorem primitive_sourceEnergy_eq_weilForm_add_two_sourcePair_oddPolarVectorAt_sq
    {a : ℝ} (ha0 : a ≠ 0) (ha : 1 < 2 * Real.exp (-2 * |a|))
    {q : SourceGraph} (hprim : ⟪q.val.fst, oneL⟫_ℝ = 0) :
    sourceEnergy q =
      weilForm q + 2 * sourcePair (oddPolarVectorAt a ha) q ^ (2 : ℕ) := by
  have h1 := sourceEnergy_eq_oddPrimitivePart_add_sq ha0 ha q
  have h2 := weilForm_eq_sourceEnergy_oddPrimitivePart ha0 ha q hprim
  have h3 := (sourcePair_oddPolarVectorAt_eq_of_admissible ha0 ha0 ha ha q).2
  rw [h1, ← h2, h3]

/-- **Orthogonal `weilForm` + Polar-Square Decomposition of `sourceEnergy` on the Odd Sector:**
For every nonzero admissible shift `a` and every odd graph vector `q : SourceGraph`
(`reflectGraph q = -q`), `sourceEnergy q = weilForm q + 2 * sourcePair (oddPolarVectorAt a ha) q ^ 2`. -/
theorem odd_sourceEnergy_eq_weilForm_add_two_sourcePair_oddPolarVectorAt_sq
    {a : ℝ} (ha0 : a ≠ 0) (ha : 1 < 2 * Real.exp (-2 * |a|))
    {q : SourceGraph} (hodd : reflectGraph q = -q) :
    sourceEnergy q =
      weilForm q + 2 * sourcePair (oddPolarVectorAt a ha) q ^ (2 : ℕ) := by
  have hodd_fst : reflectMass q.val.fst = -q.val.fst := by
    rw [← reflectGraph_fst, hodd]
    rfl
  exact primitive_sourceEnergy_eq_weilForm_add_two_sourcePair_oddPolarVectorAt_sq ha0 ha
    (inner_oneL_eq_zero_of_odd hodd_fst)

/-- Cross-shift and pole-moment forms of the conditional sinh absorption bound.
The same assumed coefficient `θ` is retained; the identity does not prove `θ ≤ 1`. -/
theorem convex_doob_chain_sinh_absorption_cross_shift_and_tanhL
    {a b R M θ : ℝ} (ha0 : 0 < a) (hb0 : b ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (hb : 1 < 2 * Real.exp (-2 * |b|))
    (hM0 : 0 ≤ M) (hM : ∀ u ∈ Icc (a - R) (a + R), ‖deriv riemannKernelReal u‖ ≤ M)
    (hθ : coshSinhPolarRatio a M R ≤ θ)
    {p : SourceGraph} {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x)
    (hsupp : ∀ u, R ≤ u → w u = 0)
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv (oddProfileTest a (fun y => w y ^ 2))) :
    phiDoobArchJumpEnergy (oddPolarWeight a w) +
        2 * sameSide (oddPolarWeight a w) +
        (∑' q : ChainIndex, chainIntegral (oddPolarWeight a w) q) ≤
      markovEnergy (fun x => (oddProfileTest a w x : ℂ)) +
        θ * sourcePair (oddPolarVectorAt b hb) p ∧
    phiDoobArchJumpEnergy (oddPolarWeight a w) +
        2 * sameSide (oddPolarWeight a w) +
        (∑' q : ChainIndex, chainIntegral (oddPolarWeight a w) q) ≤
      markovEnergy (fun x => (oddProfileTest a w x : ℂ)) +
        θ * ⟪p.val.fst, tanhL⟫_ℝ := by
  have habs := convex_doob_chain_sinh_absorption_le_one ha0 ha hM0 hM hθ hw hwc heven hsupp hp
  obtain ⟨hshift, htanh⟩ := sourcePair_oddPolarVectorAt_eq_of_admissible ha0.ne' hb0 ha hb p
  constructor
  · rw [← hshift]; exact habs
  · rw [← htanh]; exact habs

/-! ## §2. Odd-Eigenvector Primitive Modulus Resolvent Excess, Stationary `absGraph` Cauchy–Schwarz, & Nodal Chiral-Drift Tightening -/

/-- **Exact Cross-Lobe Primitive Modulus Rayleigh Excess for Any Primitive Eigenvector:**
For every primitive eigenvector `resolvent v = ν • v` (`⟪v, oneL⟫_ℝ = 0`) with `q = rieszLift v`,
`⟪resolvent (primGraph (absGraph q)).val.fst, (primGraph (absGraph q)).val.fst⟫_ℝ - ν * ‖(primGraph (absGraph q)).val.fst‖ ^ 2`
equals `4 * (⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ - 2 * (1 - ν) * (⟪(posGraph q).val.fst, oneL⟫_ℝ * ⟪(negGraph q).val.fst, oneL⟫_ℝ))`. -/
theorem primitive_eigenvector_resolvent_primGraph_absGraph_excess_eq_cross_lobe
    {ν : ℝ} {v : MassSpace} (hprim : ⟪v, oneL⟫_ℝ = 0) (heig : resolvent v = ν • v) :
    let q := rieszLift v
    ⟪resolvent (primGraph (absGraph q)).val.fst, (primGraph (absGraph q)).val.fst⟫_ℝ -
        ν * ‖(primGraph (absGraph q)).val.fst‖ ^ (2 : ℕ) =
      4 * (⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ -
        2 * (1 - ν) * (⟪(posGraph q).val.fst, oneL⟫_ℝ * ⟪(negGraph q).val.fst, oneL⟫_ℝ)) := by
  intro q
  have hq_prim : ⟪q.val.fst, oneL⟫_ℝ = 0 := by
    change ⟪resolvent v, oneL⟫_ℝ = 0
    rw [heig, real_inner_smul_left, hprim, mul_zero]
  have h1 := inner_resolvent_primGraph_fst (absGraph q)
  have h2 := norm_primGraph_fst_sq (absGraph q)
  have h3 := inner_resolvent_absGraph_of_eigenvector heig
  change ⟪resolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ =
    ν * ‖q.val.fst‖ ^ 2 + 4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ at h3
  have hnorm : ‖(absGraph q).val.fst‖ ^ 2 = ‖q.val.fst‖ ^ 2 := norm_absGraph_fst_sq q
  have honeL := (oneL_defect_absGraph_eq_eight_posGraph_negGraph hq_prim).1
  rw [hnorm, honeL] at h2
  rw [honeL] at h1
  linear_combination -h1 - ν * h2 + h3

/-- **Odd-Eigenvector Cross-Resolvent Positivity & Primitive Modulus Rayleigh Excess:**
For every nonzero odd eigenvector `resolvent v = ν • v` (`0 < ν`, `v ≠ 0`, `reflectMass v = -v`)
with `q = rieszLift v`, `-ν ^ 2 * sourcePair (posGraph q) (negGraph q)` is strictly positive,
bounds `⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ` from below, and governs the
primitive modulus Rayleigh excess in cross-lobe form. -/
theorem odd_eigenvector_primGraph_absGraph_rayleigh_excess_and_cross_pos
    {ν : ℝ} (hν : 0 < ν) {v : MassSpace} (hv0 : v ≠ 0) (hodd : reflectMass v = -v)
    (heig : resolvent v = ν • v) :
    let q := rieszLift v
    0 < -ν ^ (2 : ℕ) * sourcePair (posGraph q) (negGraph q) ∧
      -ν ^ (2 : ℕ) * sourcePair (posGraph q) (negGraph q) ≤
        ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ∧
      ⟪resolvent (primGraph (absGraph q)).val.fst, (primGraph (absGraph q)).val.fst⟫_ℝ -
          ν * ‖(primGraph (absGraph q)).val.fst‖ ^ (2 : ℕ) =
        4 * (⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ -
          2 * (1 - ν) * (⟪(posGraph q).val.fst, oneL⟫_ℝ * ⟪(negGraph q).val.fst, oneL⟫_ℝ)) := by
  intro q
  have hprim : ⟪v, oneL⟫_ℝ = 0 := inner_oneL_eq_zero_of_odd hodd
  obtain ⟨hpos1, _⟩ := inner_resolvent_posGraph_negGraph_pos_of_primitive_eigenvector hν hv0 hprim heig
  have hle := (neg_sq_mul_sourcePair_le_inner_resolvent_posGraph_negGraph hν heig).2
  have hex := primitive_eigenvector_resolvent_primGraph_absGraph_excess_eq_cross_lobe hprim heig
  exact ⟨hpos1, hle, hex⟩

/-- **Single-Lobe Edge-Norm Form of the Zero-Mode-Free `stationaryResolvent (absGraph q)` Cauchy–Schwarz Inequality:**
For every odd eigenvector `resolvent u = μ • u` (`μ ≠ 0`, `reflectMass u = -u`) with
`q = rieszLift u`, the cross-jump term `((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 + 4 * sourcePair (posGraph q) (negGraph q)`
in `eigenvector_norm_pow_four_le_stationaryResolvent_absGraph_mul` equals
`4 * ‖(posGraph q).val.snd‖ ^ 2 - ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`. -/
theorem odd_eigenvector_stationaryResolvent_absGraph_via_posGraph_snd
    {μ : ℝ} (hμ : μ ≠ 0) {u : MassSpace} (hodd : reflectMass u = -u)
    (heig : resolvent u = μ • u) :
    let q := rieszLift u
    ‖q.val.fst‖ ^ (4 : ℕ) ≤
      ⟪stationaryResolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ *
        (4 * ‖(posGraph q).val.snd‖ ^ (2 : ℕ) - ((1 - μ) / μ) * ‖q.val.fst‖ ^ (2 : ℕ) +
          archGroundConstant * ‖thetaToVolume q.val.fst‖ ^ (2 : ℕ) +
          ⟪primeShiftOperator (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ) := by
  intro q
  have hcs := eigenvector_norm_pow_four_le_stationaryResolvent_absGraph_mul hμ heig
  have hbil := (eigenvector_sourceEnergy_absGraph_sub_four_sourcePair_eq hμ heig).1
  have hsnd := odd_eigenvector_sourceEnergy_absGraph_eq_four_posGraph_snd_sub hμ hodd heig
  change sourceEnergy (absGraph q) - 4 * sourcePair (posGraph q) (negGraph q) =
    ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2 at hbil
  change sourceEnergy (absGraph q) =
    4 * ‖(posGraph q).val.snd‖ ^ 2 - (1 / μ) * ‖q.val.fst‖ ^ 2 at hsnd
  have halg : ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 + 4 * sourcePair (posGraph q) (negGraph q) =
      4 * ‖(posGraph q).val.snd‖ ^ 2 - ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 := by
    have h1 : ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 - ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2 =
        ‖q.val.fst‖ ^ 2 := by
      field_simp [hμ]; ring
    have h2 : (1 / μ) * ‖q.val.fst‖ ^ 2 - ‖q.val.fst‖ ^ 2 =
        ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 := by
      field_simp [hμ]
    linarith
  change ‖q.val.fst‖ ^ 4 ≤
    ⟪stationaryResolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ *
      (((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 + 4 * sourcePair (posGraph q) (negGraph q) +
        archGroundConstant * ‖thetaToVolume q.val.fst‖ ^ 2 +
        ⟪primeShiftOperator (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ) at hcs
  rw [halg] at hcs
  exact hcs

/-- **Unconditional Nodal Chiral-Drift Tightening of the Pythagorean Prime-Shift Bound on the Odd Sector:**
For every odd graph vector `q : SourceGraph` (`reflectGraph q = -q`), both nodal lobes `posGraph q`
and `negGraph q` have their `primeShiftOperator` quadratic forms tightened by
`(1 / 4) * ⟪oddPrimeDriftOperator q.val.fst, (absGraph q).val.fst⟫_ℝ ^ 2`. -/
theorem odd_posGraph_and_negGraph_primeShift_sq_add_quarter_absGraph_drift_sq_le
    {q : SourceGraph} (hodd : reflectGraph q = -q) :
    ⟪primeShiftOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ ^ (2 : ℕ) +
        (1 / 4 : ℝ) * ⟪oddPrimeDriftOperator q.val.fst, (absGraph q).val.fst⟫_ℝ ^ (2 : ℕ) ≤
      ⟪primeDiagonalOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ ^ (2 : ℕ) ∧
    ⟪primeShiftOperator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ^ (2 : ℕ) +
        (1 / 4 : ℝ) * ⟪oddPrimeDriftOperator q.val.fst, (absGraph q).val.fst⟫_ℝ ^ (2 : ℕ) ≤
      ⟪primeDiagonalOperator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ^ (2 : ℕ) := by
  have hodd_fst : reflectMass q.val.fst = -q.val.fst := by
    rw [← reflectGraph_fst, hodd]
    rfl
  exact posGraph_and_negGraph_primeShift_sq_add_quarter_absGraph_drift_sq_le
    (inner_oddPrimeDriftOperator_self_eq_zero_of_odd hodd_fst)

/-! ## §3. Second-Octave Odd-Cell Fermi Curvature–Gradient Reciprocity & Squarefree Energy Lower Bound -/

/-- **Second-Octave Odd-Cell Fermi Curvature–Gradient Reciprocity:**
For every `N, m : ℕ` with `N ≤ m` and `m + 1 ≤ 2 * N` (so `2 * m + 1 ∈ [2 * N + 1, 4 * N - 1]` lies
in the second trans-horizon octave while its half-scale parent `m + 1 ∈ [N + 1, 2 * N]` lies in the
first trans-horizon octave), the second-order difference of `fermiCellResponse N moebiusReal`
centered at `2 * m + 1` plus `addDiff (sieveSeq N moebiusReal) (2 * m + 1)` equals
`-2 * moebiusReal (m + 1)`. -/
theorem fermiCellResponse_second_diff_add_addDiff_eq_neg_two_moebiusReal_second_octave
    {N m : ℕ} (hlo : N ≤ m) (hhi : m + 1 ≤ 2 * N) :
    ((fermiCellResponse N moebiusReal (2 * m + 2) -
        fermiCellResponse N moebiusReal (2 * m + 1)) -
      (fermiCellResponse N moebiusReal (2 * m + 1) -
        fermiCellResponse N moebiusReal (2 * m))) +
      addDiff (sieveSeq N moebiusReal) (2 * m + 1) =
      -2 * moebiusReal (m + 1) := by
  have h1 := fermiCellResponse_second_diff_across_odd_eq_two_half_sub_addDiff N moebiusReal m
  have h2 := sieveSeq_moebiusReal_first_octave (by omega : N + 1 ≤ m + 1) hhi
  linarith

/-- **Pointwise Second-Octave Fermi Curvature + BVI Gradient Energy Lower Bound:**
For every `N, m : ℕ` with `N ≤ m` and `m + 1 ≤ 2 * N`, twice the squared Möbius parent
`2 * moebiusReal (m + 1) ^ 2` is bounded above by the sum of the squared second-order Fermi cell
difference centered at `2 * m + 1` and the squared BVI forward gradient
`addDiff (sieveSeq N moebiusReal) (2 * m + 1) ^ 2`. -/
theorem two_mul_moebiusReal_sq_le_fermi_second_diff_sq_add_addDiff_sq_second_octave
    {N m : ℕ} (hlo : N ≤ m) (hhi : m + 1 ≤ 2 * N) :
    2 * moebiusReal (m + 1) ^ (2 : ℕ) ≤
      ((fermiCellResponse N moebiusReal (2 * m + 2) -
          fermiCellResponse N moebiusReal (2 * m + 1)) -
        (fermiCellResponse N moebiusReal (2 * m + 1) -
          fermiCellResponse N moebiusReal (2 * m))) ^ (2 : ℕ) +
      addDiff (sieveSeq N moebiusReal) (2 * m + 1) ^ (2 : ℕ) := by
  set A := (fermiCellResponse N moebiusReal (2 * m + 2) -
      fermiCellResponse N moebiusReal (2 * m + 1)) -
    (fermiCellResponse N moebiusReal (2 * m + 1) -
      fermiCellResponse N moebiusReal (2 * m))
  set B := addDiff (sieveSeq N moebiusReal) (2 * m + 1)
  have hsum : A + B = -2 * moebiusReal (m + 1) :=
    fermiCellResponse_second_diff_add_addDiff_eq_neg_two_moebiusReal_second_octave hlo hhi
  have hsq : (A + B) ^ (2 : ℕ) = 4 * moebiusReal (m + 1) ^ (2 : ℕ) := by
    rw [hsum]
    ring
  have hcs : 0 ≤ (A - B) ^ (2 : ℕ) := sq_nonneg (A - B)
  nlinarith

/-- **Second-Octave Summed Fermi Curvature + BVI Gradient Energy Lower Bound:**
For every `N : ℕ`, summing over `m ∈ Finset.Ico N (2 * N)` bounds the combined second-octave Fermi
curvature and odd-cell BVI forward gradient energy below by twice the first-octave squarefree sum
`2 * ∑_{m ∈ Ico N (2N)} moebiusReal (m + 1) ^ 2`. -/
theorem two_mul_sum_moebiusReal_sq_le_sum_second_octave_fermi_and_gradient_sq
    (N : ℕ) :
    2 * (∑ m ∈ Finset.Ico N (2 * N), moebiusReal (m + 1) ^ (2 : ℕ)) ≤
      ∑ m ∈ Finset.Ico N (2 * N),
        (((fermiCellResponse N moebiusReal (2 * m + 2) -
            fermiCellResponse N moebiusReal (2 * m + 1)) -
          (fermiCellResponse N moebiusReal (2 * m + 1) -
            fermiCellResponse N moebiusReal (2 * m))) ^ (2 : ℕ) +
        addDiff (sieveSeq N moebiusReal) (2 * m + 1) ^ (2 : ℕ)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  exact two_mul_moebiusReal_sq_le_fermi_second_diff_sq_add_addDiff_sq_second_octave
    hlo (by omega)

/-- **Second-Octave Fermi Curvature + BVI Gradient Dominance of `oddSquarefreeWindow N`:**
For every `N : ℕ`, the combined second-octave Fermi curvature and odd-cell BVI forward gradient
energy across `m ∈ Finset.Ico N (2 * N)` is at least `2 * ((oddSquarefreeWindow N).card : ℝ)`. -/
theorem two_mul_oddSquarefreeWindow_card_le_sum_second_octave_fermi_and_gradient_sq
    (N : ℕ) :
    2 * ((oddSquarefreeWindow N).card : ℝ) ≤
      ∑ m ∈ Finset.Ico N (2 * N),
        (((fermiCellResponse N moebiusReal (2 * m + 2) -
            fermiCellResponse N moebiusReal (2 * m + 1)) -
          (fermiCellResponse N moebiusReal (2 * m + 1) -
            fermiCellResponse N moebiusReal (2 * m))) ^ (2 : ℕ) +
        addDiff (sieveSeq N moebiusReal) (2 * m + 1) ^ (2 : ℕ)) := by
  refine (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)).trans
    (two_mul_sum_moebiusReal_sq_le_sum_second_octave_fermi_and_gradient_sq N)
  rw [oddSquarefreeWindow_card_eq_weighted_sum]
  have hbij : (∑ k ∈ Finset.Ioc N (2 * N),
      (if 2 ∣ k then (0 : ℝ) else ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ (2 : ℕ))) =
      ∑ m ∈ Finset.Ico N (2 * N),
        (if 2 ∣ (m + 1) then (0 : ℝ) else moebiusReal (m + 1) ^ (2 : ℕ)) := by
    refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hk
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro k₁ hk₁ k₂ hk₂ heq
      obtain ⟨hlo₁, _⟩ := Finset.mem_Ioc.mp hk₁
      obtain ⟨hlo₂, _⟩ := Finset.mem_Ioc.mp hk₂
      omega
    · intro m hm
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
      exact ⟨m + 1, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk
      obtain ⟨hlo, _⟩ := Finset.mem_Ioc.mp hk
      have hk1 : k - 1 + 1 = k := by omega
      rw [hk1]
      rfl
  rw [hbij]
  refine Finset.sum_le_sum fun m _ => ?_
  by_cases htwo : 2 ∣ (m + 1)
  · rw [if_pos htwo]
    exact sq_nonneg _
  · rw [if_neg htwo]

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
