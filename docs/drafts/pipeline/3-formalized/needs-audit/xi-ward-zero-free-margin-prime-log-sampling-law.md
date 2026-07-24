# Zero-free margin and prime-log sampled completeness of the four-unit Ward law

- **ID:** `xi-ward-zero-free-margin-prime-log-sampling-law`
- **Stage:** 3-formalized
- **Type:** THEOREM, RH-complete discrete sampling criterion + budget-slack law
- **Scientific status:** `[UNCONDITIONAL] [LEAN] [CORPUS-NEW] [FIRST ANT-TO-WARD BRIDGE] [NOT RH]`
- **Lean source:**
  `formal/GaloisForLFunctions/RHTower/XiWardZeroFreeMarginPrimeLogSampling.lean`
- **Depends on:**
  - `GammaSewnMobiusXiWardEulerEdgeCompleteness.lean` (Euler-edge scalar law `RH <-> |r(1/2+it)|^2 <= 4`);
  - `ZetaZeroFreeRegion.lean` (formalized de la Vallée Poussin region, `c = zetaZeroFreeC`);
  - `ZetaLowHeightZeroFree.lean` (compactness margin for `|t| <= 9`);
  - `ShrinkingWindowPrimeSupply.lean` (primes in windows `[e^y, e^{y+eta}]`,
    `eta >= K exp(-c2 y^{1/10})`).

## Result

Write `r = continuedXiAntiCausalWardResponse` and define the margin

```text
m(y) = c' / log^9(|y| + 9),      c' = min(zetaZeroFreeC, delta_lowheight) > 0.
```

Five unconditional theorems, all on standard axioms only:

1. **Margin transport** (`xiRightCenteredZero_re_le_half_sub_margin`): every
   strict-right centered Xi zero `lambda` satisfies
   `Re lambda <= 1/2 - m(Im lambda)`.  First consumption of the formalized
   zero-free region by the Ward lane.

2. **Detection window** (`normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four`):
   for every strict-right pair and every real `t` with
   `(t + Im lambda)^2 <= m(Im lambda)/2`, already `|r(1/2+it)|^2 > 4`.  The
   four-unit failure is not a point event at the adapted node; it occupies a
   window of a-priori polylogarithmic width.

3. **Relaxed-budget completeness**
   (`riemannHypothesis_iff_continuedXiWardRelaxedEulerEdgeScalarLaw`):

   ```text
   RH  <->  for all t : |r(1/2+it)|^2 <= 4 + 8 m(t).
   ```

   The four-unit wall has unconditional thickness: any mechanism achieving the
   budget only up to the zero-free margin already proves RH.  This strictly
   enlarges the target of every future `W_P` positivity mechanism.

4. **Sampled completeness** (`riemannHypothesis_iff_continuedXiWardSampledScalarLaw`):
   for every `S` meeting each detection window
   (`XiWardDetectionCover S`: for all `y`, some `t` in `S` has
   `(t+y)^2 <= m(y)/2`),

   ```text
   RH  <->  for all t in S : |r(1/2+it)|^2 <= 4.
   ```

5. **Prime-log instantiation**
   (`exists_cutoff_riemannHypothesis_iff_primeLogSampledScalarLaw`): past an
   explicit cutoff `Y`, the family

   ```text
   S(Y) = { +-log p : p prime } union (finite grid of step sqrt(m(Y)/2) below Y+1)
   ```

   is a detection cover, because the shrinking-window prime supply places a
   `log p` inside every window `[y, y + sqrt(m(y)/2)]` for large `y`: prime-log
   gaps decay stretched-exponentially, detection radii only
   polylogarithmically.  Hence

   ```text
   RH  <->  the four-unit law sampled on S(Y) alone.
   ```

   `xiWardPrimeLogSampleSet_bounded_finite` proves `S(Y)` is locally finite:
   the criterion is strictly discrete and cannot be recovered from the known
   `for all t` law by density/continuity transfer.  Byproduct
   `re_continuedXiAntiCausalWardResponse_nonneg`: `Re r >= 0` on `Re w > 0`
   (standalone Herglotz positivity of the Ward response).

## Why this matters for the `W_P` lane

`W_P` positivity restricted to the Euler edge is exactly RH
(`riemannHypothesis_iff_continuedXiWardEulerEdgeBoundaryGramLaw`).  This law
replaces the uncountable edge quantifier by a countable, locally finite,
arithmetically indexed family: the primes are a sufficient jury for the Ward
law.  Referee-verified (hostile pass): no circularity (margin, cover, and
`S(Y)` are RH-free; the zero copy appears only as the standard contrapositive
witness), not classically trivial (the `forall S` sampling criterion and the
RH-free cover theorem carry the content), and not derivable from the corpus
`forall t` law.  Without the zero-free margin no fixed locally finite sample
set could be certified at all, since the geometric window
`(a+1/2)(1/2-a)` degenerates as `a -> 1/2`.

## Audit

- Module compiles clean (no warnings); `formal lint passed`.
- `#print axioms` on all eight principal declarations:
  `[propext, Classical.choice, Quot.sound]`.
- Cross-cone note: this is the first module importing both the Ward cone and
  the Perron/PNT cone; the blocking duplicate name `pow_mul_exp_neg_le` was
  resolved by renaming the Perron copy to `pow_mul_exp_neg_le_absorb_half`.

## Openings (next generative moves)

1. **Merged slack sampling** — combine laws 3 and 4: `RH <-> sampled law with
   budget 4 + m(t)` on `S(Y)`; makes the discrete criterion robust to
   margin-sized evaluation error (referee strengthening B; quantitative
   violation `> 4 + 3 m(b)` at the sampled node).
2. **Edge mass quantization (W5)** — `Re r >= 0` plus the Lorentzian shape
   gives `integral of Re r over [-T,T] ~ 4 pi N_off(T)`: the edge current's
   total mass counts off-line pairs.  Aperture-uniform defect estimates in
   Burnol style are unclaimed territory (literature sweep 2026-07).
3. **Log-rational grid** — replace the affine grid by logs of bounded-height
   rationals: the whole sample set becomes multiplicative-arithmetic
   (referee strengthening E), reformulating the edge law over `Q_+`.
4. **One-sided detection** — upper zero copies have detectors at `t ~ -b < 0`
   only; the negative half of `S(Y)` suffices (referee strengthening D).
5. Scoped no-go recorded: a prime-logs-only criterion (no low-height grid) is
   not reachable from current unconditional inputs — near height 1 the
   prime-log mesh (~0.3) exceeds the detection radius (<= 10^-2), and no
   unconditional low-height mechanism widens the window.

## Addendum: merged slack sampling `[PROVED AND LEAN-FORMALIZED]`

Opening 1 is discharged in
`formal/GaloisForLFunctions/RHTower/XiWardMergedSlackPrimeLogSampling.lean`
(standard axioms; lint clean):

- `xiWardZeroFreeMargin_close_le_two_mul`: log-slow variation
  `|t + b| <= 1  ->  m(t) <= 2 m(b)`.
- `re_xiAntiCausalWardSchwarzPairResponse_marginWindow_gt_two_add_half`:
  inside a detection window the selected pair response exceeds `2 + m(b)/2`.
- `normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four_add`:
  inside a detection window `|r(1/2+it)|^2 > 4 + 2 m(b)`.
- `riemannHypothesis_iff_continuedXiWardMergedSlackSampledScalarLaw`: on every
  detection cover `S`,

  ```text
  RH  <->  for all t in S : |r(1/2+it)|^2 <= 4 + m(t).
  ```

- `exists_cutoff_riemannHypothesis_iff_primeLogMergedSlackScalarLaw`: the same
  on the prime-log family `S(Y)` past an explicit cutoff.

The discrete criterion is therefore robust to a margin-sized error at every
node: budget slack and discrete sampling compose.  Remaining openings: edge
mass quantization (W5), log-rational grid, one-sided detection.

## Addendum 2: sampled Ward-matrix (`W_P`) completeness `[PROVED AND LEAN-FORMALIZED]`

The scalar sampling laws lift to the literal augmented Ward matrices in
`formal/GaloisForLFunctions/RHTower/XiWardPrimeLogSampledGramLaw.lean`
(standard axioms; lint clean):

- `continuedXiWardFourUnitSchurDefect_marginWindow_diag_re_neg` /
  `continuedXiWardFourUnitBoundaryGram_marginWindow_not_posSemidef`: a
  strict-right pair refutes PSD-ness of the one-node `W_P` at every sample in
  its margin window.
- `XiWardUpperDetectionCover`: covering the positive heights alone suffices
  (every off-line pair has an upper representative) — the one-sided
  sharpening at the interface level.
- `riemannHypothesis_iff_continuedXiWardSampledBoundaryGramLaw`: on every
  upper detection cover `S`,

  ```text
  RH  <->  W_P is PSD for every finite packet drawn from S on the Euler edge.
  ```

- `exists_cutoff_riemannHypothesis_iff_primeLogSampledBoundaryGramLaw`: the
  same on the prime-log family.  The goal-level object `W_P` itself now needs
  positivity only on finite packets of signed prime logarithms plus one finite
  grid.

Remaining openings unchanged: edge mass quantization (W5), log-rational grid,
negative-node-only instantiation of the upper cover.

## Addendum 3: edge mass quantization `[PROVED AND LEAN-FORMALIZED]`

Opening 2 (W5) is discharged in
`formal/GaloisForLFunctions/RHTower/XiWardEdgeMassQuantization.lean`
(standard axioms; lint clean):

- `re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq`: on the Euler edge one
  Schwarz pair is exactly two Lorentzian profiles of half-width `Re λ + 1/2`
  centered at the reflected heights.
- `lintegral_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge`: **universal
  pair charge** — every strict-right pair carries edge mass exactly `4π`,
  independently of its height and its distance from the critical line.
- `lintegral_re_continuedXiAntiCausalWardResponse_eulerEdge`: **edge mass
  quantization** —

  ```text
  ∫⁻ t, ofReal (Re r(1/2+it)) = Σ'_(q : upper pairs) ofReal (4π).
  ```

- `riemannHypothesis_iff_lintegral_re_continuedXiAntiCausalWardResponse_eq_zero`:
  RH is the vanishing of one nonnegative edge integral.

Interpretation: the Ward edge current is a charge-quantized counting measure
for off-line pairs.  While the pointwise budget `4` weighs a pair by its
distance from the line, the mass `4π` is distance-blind — the first exact
global invariant of the hypothetical off-line divisor in this lane.  Next:
windowed mass bounds (mass in `[b-1, b+1]` at least `2π`-ish) to combine
counting with the sampled laws, and the Burnol-style aperture-uniform defect
for `4 G_P - r_P r_P^*`.

## Addendum 4: integer-window mass criterion `[PROVED AND LEAN-FORMALIZED]`

The mass quantization localizes, in
`formal/GaloisForLFunctions/RHTower/XiWardIntegerWindowMassCriterion.lean`
(standard axioms; lint clean):

- `windowed_lorentzian_integral`: the half-unit window of a centered
  Lorentzian of half-width `x` carries mass `4·arctan(1/(2x))`.
- `le_xiWardIntegerWindowMass_round`: **localized counting** — every
  strict-right pair deposits mass at least `4·arctan(1/2)` in the unit-radius
  window at the integer nearest its reflected height.
- `riemannHypothesis_iff_forall_xiWardIntegerWindowMass_eq_zero`:

  ```text
  RH  <->  for all k : Z, (integer-window edge mass at k) = 0.
  ```

This is the cleanest countable criterion of the family: index set literally
`Z`, no cutoff, no grid, no choice anywhere in the statement.  Together with
the quantization identity, the off-line divisor is now globally counted
(charge `4π` per pair) and locally detected (mass `>= 4·arctan(1/2)` in an
explicit integer window).

## Addendum 5: Ward edge measure and quantitative Schur defect `[PROVED AND LEAN-FORMALIZED]`

`formal/GaloisForLFunctions/RHTower/XiWardEdgeMeasureDefect.lean`
(standard axioms; lint clean) packages the family into one object:

- `xiWardEdgeMeasure`: the positive Borel measure `volume.withDensity (Re r)`
  on the Euler edge — unconditionally defined.
- `xiWardEdgeMeasure_univ`: total mass = quantized pair count (`4π` each);
  `xiWardEdgeMeasure_integerWindow`: window masses = the integer detectors.
- `riemannHypothesis_iff_xiWardEdgeMeasure_eq_zero`: **RH is the vanishing of
  one positive measure.**
- `continuedXiWardFourUnitSchurDefect_adaptedNode_re_lt_neg_margin`:
  **quantitative Schur defect law** — at the adapted node of any strict-right
  pair the one-node `W_P` Schur defect is `< -8·margin`: PSD failure is
  bounded away from zero polylogarithmically.  First brick of the
  aperture-uniform (Burnol-style) defect estimate.

Duplication check (mandate): `formal_tools.py research` + `rg` sweeps for
edge-measure / window-mass / Lorentzian-mass / quantitative-defect objects
return only this session's six modules; the corpus's only prior "Lorentzian
kernel" occurrence (`XiAperturePoissonResponseSignature`) is the disjoint
scale-increment signature lane.  No duplication.

## Addendum 6: threshold-8 and edge blindness `[PROVED AND LEAN-FORMALIZED]`

- `XiWardThresholdEightCompleteness.lean`
  (`riemannHypothesis_iff_continuedXiWardCornerLiftLaw`): RH ⟺ corner-`c`
  Ward lift law for every `0 ≤ c < 8`; pair-energy floor
  `4(1/a + a/(a²+b²)) > 8` on the adapted two-node packet.  The completeness
  threshold of the corner budget is 8, twice the four-unit value.
- `XiEdgeLogDerivativeBlindness.lean` (`re_logDeriv_xi_criticalLine`,
  `deriv_conj_reflect`, `deriv_xi_conj`, `deriv_xi_one_sub`):
  `Re(ξ'/ξ) ≡ 0` on the critical line — relative positivity is the only
  divisor detector, now as theorem.

Both lint-clean on standard axioms.  Successor campaign: the two-quantum
energy law (`xi-ward-moire-prime-pair-attack.md`).

## Addendum 7 — closed-budget 4π integrated edge law (XiWardEdgeL2CrossKernel.lean)

[PROVED HERE] `riemannHypothesis_iff_continuedXiWardEdgeQuadEnergyLaw {c} (hc0 : 0 ≤ c)
(hc : c ≤ 4*π) : RiemannHypothesis ↔ ContinuedXiWardEdgeQuadEnergyLaw c` — RH is equivalent
to the single integrated inequality ∫⁻_t ofReal(normSq r(½+it)) dt ≤ ofReal c for ANY fixed
budget in the CLOSED window [0, 4π].  Supporting certified layers: ∫(x+i(t+β))⁻² dt = 0
(complex FTC), ∫(x/(x²+(t+β)²))² dt = π/(2x), per-pair lintegral floor ofReal(4π/x) with
x = Re λ + ½ < 1.  Axioms: propext, Classical.choice, Quot.sound.  Module compiles clean,
lint clean, umbrella wired.

## Addendum 8 — edge-L² lattice stack (steps 9i–9q), capstone

[PROVED HERE] Modules XiWardEdgeL2CrossKernel.lean, XiWardEdgeEnergyMarginWindow.lean,
XiWardEdgeReChannelDeposit.lean, XiWardEdgeImChannelGram.lean (all compile clean, all
results on propext/Classical.choice/Quot.sound, umbrella wired, lint clean).
Headline theorems: riemannHypothesis_iff_continuedXiWardEdgeQuadEnergyLaw (RH ⟺ edge
energy ≤ c, any 0 ≤ c ≤ 4π, closed endpoint); xiWardEdgeQuadEnergy_eq_zero_or_fourPi_lt
(unconditional spectral-gap dichotomy); card_nsmul_le / card_le / finiteness laws
(energy counts the divisor); height-window clearing (margin-budget certificate clears
heights ≤ T); sharp per-pair and pair-pair deposits in closed form; pairwise channel
equipartition; xiWardEdgeQuadEnergy_eq_tsum_gram (the FULL quadratic explicit formula,
finite/infinite dichotomy, no Fubini); riemannHypothesis_iff_tsum_gram_le (RH as a
lattice-sum inequality ≤ 4π with every diagonal entry > 8π).

## Addendum 9 — interior program + J-ladder modules (steps 9x–9az)

[PROVED HERE] New modules, all compiling clean on propext/Classical.choice/Quot.sound,
umbrella wired, indexed:
- XiWardInteriorTraceSplit.lean — interior trace splitting; Ward-response interior
  decomposition; quotient-constancy kill; functional-equation rotation;
  logDeriv xi = 1/s + 1/(s−1) + logDeriv Γℝ − L(Λ,·) on Re s > 1 (THE ARITHMETIC
  RESPONSE IDENTITY); the interior spectral discard (per-term + tsum);
  re_continuedXiAntiCausalWardResponse_le_arithmetic (UNCONDITIONAL arithmetic upper
  bound); interior_pair_quantum + xiWard_window_clearing (THE CLEARING ENGINE);
  xiWard_centralWindow_clearing (boundary-conditional central clearing at certified
  margin 0.599 < 0.600); Γℝ–digamma split; von Mangoldt real-series machinery with
  certified floor 0.414; log π > 1.1, log 5 > 1.6, γ ∈ (½,⅔) numeric chains.
- XiThetaExplicitBounds.lean (minimal cone) — explicit theta decay 3e^{−πt};
  two-piece FE-modified kernel bounds; quartic exponential floor; exact outer moment
  (1/π+1/π²)e^{−π}; both Mellin piece bounds + integrabilities; THE CERTIFIED STRIP
  BOUND ‖Λ₀(s)‖ ≤ 2/5 on Re s ∈ [−3/2, 5/2] (norm_completedRiemannZeta₀_le +
  stripConstant_le_two_fifths).
- XiCentralDiscBound.lean — ‖XiC‖ ≤ 7/4 on ‖z‖ ≤ 2; ‖XiC 0‖ ≥ 9/20;
  **XiC_ne_zero_of_norm_le_one** (Jensen + evenness, margin 35 < 36);
  **xiRightUpper_height_sq_gt** (unconditional off-critical height floor 3/4);
  **riemannZeta_ne_zero_of_dist_le_one** (unconditional central zero-free disc for ζ).
Named obstructions recorded on the campaign card: central blindness (9aj); J5 counting
capacity (9ay).
