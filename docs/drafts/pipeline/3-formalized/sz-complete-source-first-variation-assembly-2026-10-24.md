# Suzuki: complete critical source first variation

- **Stage:** 3-formalized (complete source theorem and arithmetic-family transfer)
- **Parent:** `sz-critical-source-first-variation-2026-10-18.md`
- **Scope:** Finish the literal `suzukiSourceHFinite` first variation, then test
  connections to the broader Lean corpus for an actual source estimate.

## Exact endpoint

For every real compactly supported C² source `f`, let `C = autocorr f` and
`A_w(t) = exp(t/2) * Re(suzukiSourceHFinite w (exp t))`. Prove

`lim_(w→0+) [C(0) - integral_(0,infinity) C(t) A_w(t)] / w
 = Re(weilFullFunctional Λ (weilTest f f))`.

Keep the forming Gamma atom, both polar exponentials, and every prime-power
cusp. All integrability and limiting premises must follow from the stated
source domain. No sign hypothesis, innerness, or RH premise is allowed.

## Work split and verification gates

- [x] Read complete parent paper proof and primary Beta implementation.
- [x] Use the translated-cusp leaf once its independent ongoing check finishes;
  preserve that worker's edits and avoid duplicate concurrent compilation.
- [x] Prove the exact logarithmic primary/pole convolution identity.
- [x] Prove compactly tested pole convergence, keeping the growing exponential
  inside the compact aperture throughout Fubini and dominated convergence.
- [x] Assemble the locally finite arithmetic source using the common support
  cutoff and `hasDerivAt_suzukiShiftedCoefficient`.
- [x] Identify Gamma/Lévy/pole/prime normalization with the complete Weil form.
- [x] Check canonical leaves, audit every public declaration's transitive
  axioms, wire imports without compiling umbrellas.
- [x] Search the broader corpus for estimates applying to this exact source;
  formalize any substantive premise discharge found.

## Remaining mathematical frontier

The fixed-source first variation supplies an unconditional analytic input. It
does not establish nonnegative first variation, a growing-aperture estimate, or
JAS power-budget positivity. These remain the source-level research targets
after the complete identity is formalized.

## Pole-limit proof refinement

The finite logarithmic identity is formalized in
`SuzukiCriticalLogKernel.lean`:

`G_w(t) = B_w(t) - 2w Q_w(t)`,
`Q_w(t) = integral_(0,t) B_w(r) exp((1/2-w)(t-r)) dr`.

To justify the pole limit without a global convolution interchange, use the
primary first moment `L_w = integral_0^infinity r B_w(r) dr`. The existing
compensated-primary convergence theorem gives `L_w → 0`: its required
dominator is integrable because

`r * 2 exp(-r/2)/(1-exp(-2r)) <= (1+2r) exp(-r/2)`.

For `0<w<=1/2`, the truncated exponential weight differs from one by at most
`(1+1/t)r`. Hence its pairing with `B_w` differs from the total mass by at most
`(1+1/t)L_w`. It follows that `Q_w(t)→exp(t/2)` for every `t>0`, while
`0<=Q_w(t)<=M_w exp(t/2)`. Compact support then justifies the tested pole
limit by dominated convergence. This retains the complete growing polar branch.

## Shared-workspace integration

The concurrent `SuzukiCriticalLogKernel` and `SuzukiCriticalPolePairing` leaves
provide the exact log identity and the compact Fubini argument. This assembly
uses those leaves, rather than keeping duplicate declarations. The alternative
first-moment derivation above remains a paper argument; its scratch Lean files
are not part of the certified dependency chain.

Assembly work now owns `SuzukiCriticalWeilNormalization`,
`SuzukiCriticalArithmeticVariation`, and the complete source capstone.

## Broader-corpus checks during assembly

- `SuzukiFiniteShiftGeneratorLimit`: the divided-difference theorem is for the
  exact artificial family `F + delta J`, with nonzero endpoint assumptions.
  It does not supply a literal-source sign estimate or growing-aperture limit.
- `SuzukiWeilFriedrichsOperator`: `suzukiWeilIntervalCovariance_isPositive`
  concerns `boundedPerturbedFormCovariance`, a shifted covariance. The exact
  interval form itself equals `ccmRestrictedWeilForm`. Positivity of that
  unshifted form is not proved by the covariance theorem.
- `CompactFiniteJumpWeilFormula` identifies the full signed spectral form with
  the prime–Gamma–polar physical expression on the finite-jump domain. This is
  used directly in the complete first-variation capstone, with jump
  integrability discharged from compact C² regularity.
- `CCMRealGramComplexEnergy` splits complex phase-source energies into two real
  energies after reality of the mixed matrix is established. It does not
  remove the need to establish the sign of those real energies.

Certified assembly leaves: `SuzukiCriticalWeilNormalization`,
`SuzukiCriticalArithmeticVariation`, `SuzukiCriticalCuspEstimate`,
`SuzukiCriticalFirstVariation`. Their canonical Lean checks and transitive-axiom audits passed.

## Verification record

- `SuzukiCriticalWeilNormalization`: dependency olean built successfully;
  canonical source checked again after removing redundant tactics.
  `#print axioms RHTower.suzukiCriticalWeil_normalization` reports exactly
  `propext`, `Classical.choice`, `Quot.sound`.
- The concurrent `SuzukiCriticalLogKernel`, `SuzukiCriticalTranslatedCusp`, and
  `SuzukiCriticalPolePairing` dependency oleans now exist. Their full public
  declaration audit passed as part of the complete capstone audit.
- `SuzukiCriticalArithmeticVariation`: canonical dependency compile passed.
  All five public declarations report only `propext`, `Classical.choice`,
  `Quot.sound`.
- `SuzukiCriticalCuspEstimate`: canonical dependency compile passed; all four
  public declarations report the same three standard axioms.
- `SuzukiCriticalFirstVariation`: canonical dependency compile passed; all
  57 public declarations in the complete chain report only the three standard
  axioms. The main paper card is now in stage 3. The strict-deficit application
  also passed its canonical check without producing an olean; its transitive axiom audit
  reports only the same three standard axioms. All 58 public declarations
  across the chain and application are certified.

## Fourteen-programme review

The introductions, source mechanisms, and relevant frontier sections were
reviewed. README claims were treated as leads. The entries directly used below
were checked against their Lean statements.

| Programme | Relevant mechanism | Consequence for the Suzuki route |
|---|---|---|
| Arithmetic Positivity Theory | Positive compact dyadic critical families; finite-jump smoothing | Gives an unconditional strict literal-source deficit after the first-variation transfer. Formal application certified in `SuzukiCriticalFamilyContraction`. |
| BiScale Uncertainty | Krein increments, finite Lévy energy, complete finite-jump Weil formula | Directly supplies the translated cusp estimate and the complete normalization. |
| Trans-Horizon Incidence Mechanics | Keep signed source and boundary across the horizon | Existing zero-free-band estimates do not give a fixed damping below the half threshold at every horizon. |
| Bézout–Valuation Incidence | Damped Möbius divisor response and centered damping chain | Exact coefficient-level connection exists; compactness in `c₀` does not give the needed receiver `ℓ²` bound. |
| Arithmetic Criticality Theory | Jump form and aperture ground energy | Identifies the unpaid even pole directions and the all-aperture sign; no supplied global floor. |
| Square-Root Threshold | Prime length versus height | Locates the growing-aperture obstruction; bounded-window positivity cannot substitute for it. |
| Arithmetic Incidence Positivity | Shared archimedean allocation, ratio/product correlations | A possible way to pay multiple towers without charging the same diagonal budget repeatedly. No such all-aperture payment is proved here. |
| Arithmetic Continuation and Critical Energy | Signed work as damping autocorrelation | Keeps the cross terms that size bounds discard. Its square-integrated positivity alone gives no horizon-uniform upper bound. |
| Scale-Signed Incidence Criticality | What magnitude and finite-window data forget | Helps audit information loss; contributes no missing source estimate by itself. |
| Arithmetic Compensation Theory | Subtract prime and pole before taking norms | Matches the actual Suzuki error transform. Existing de la Vallée Poussin savings remain above the critical scale. |
| Arithmetic Castelnuovo–Severi | Low-frequency section obstruction | High-frequency positivity and finite defect count leave the low directions and pole unpaid. |
| Signed Arithmetic Energy Incidence | Nonlocal allocation and residue Gram | Suitable language for joint tower payment, but the required actual-source conductances remain open. |
| Trans-Threshold Pair Correlation | Signed close prime pairs | Targets a zero proportion; its averaged surplus is not an all-test Suzuki sign theorem. |
| Arithmetic Orientation Theory | Reflected continuum Cholesky modes | A concrete positive decomposition beyond lattice tests, retaining complementary fibres. Its lower bound on the prime contribution has the opposite direction from the upper bound needed for Weil positivity. |

### Checked source connections

- `ShiftedEulerFloorMobiusTailCoupling.suzukiShiftedSummatory_eq` writes
  `c_ω` as the actual Möbius divisor synthesis.
- `suzukiCoupledError_eq` keeps the signed power-sum floor error and the
  Möbius tail coupled. `SuzukiTailSummatoryErrorTransform.
  suzukiSourceHOneFinite_eq_coupledErrorStieltjes` removes the positive main
  term exactly. This bridge already exists; rediscovering it is not new progress.
- `ArithmeticOrientationTheory.continuumTower_reflection_cholesky` writes
  `Mass + 2 Ratio - Crossing` as three nonnegative square terms for
  `0 ≤ r ≤ 1`, including the reflected zeroth fibre. This improves on a
  lattice-only reading of the tower law. The sign must be retained: the prime
  contribution enters the complete Weil form with coefficient `-2`, so
  Cholesky nonnegativity alone supplies the wrong inequality direction for
  the needed Weil lower bound.
- `ArithmeticPositivityTheory.
  exists_compactFullWeilEnergy_criticalTruncatedTest_pos` proves positivity
  for arbitrary nonzero coefficient patterns in sufficiently high dyadic
  blocks, with unbounded compact truncation length. Its sources are Lipschitz,
  so `re_weilFullFunctional_smooth_tendsto` supplies smooth admissible sources
  without assuming a new analytic input.

### Concrete application and surviving research lead

The exact strict-deficit theorem and complete paper proof are in
`sz-critical-positive-family-transfer-2026-10-24.md`.
This transfers an existing positive arithmetic family into a genuine
finite-shift inequality for the literal Suzuki source. It is a standard
mathematical consequence, not a scientific novelty claim.

The remaining research lead is an upper estimate for the compensated aggregate
of reflected continuum tower energies. Writing `T_p = Mass + 2 Ratio_p -
Crossing_p`, the prime contribution is `sum_p log(p) (T_p - Mass)`, with
`T_p ≥ 0`. The subtraction, pole term, and common archimedean energy must stay
together. A separate lower bound on each `T_p` cannot prove the desired upper
bound on this aggregate. The open tasks are an actual signed estimate and
control as aperture grows. Neither a new criterion nor another sign-blind
bound would discharge them.

## Final verification

- Canonical source checks passed for the new leaves. Dependency artifacts were
  produced only where downstream proof files import them, and no existing
  olean was rebuilt.
- All 57 public declarations in the complete first-variation chain and the
  arithmetic-family theorem have been audited transitively. Every axiom list
  contains only `propext`, `Classical.choice`, and `Quot.sound`.
- Static audit found no proof placeholders, added axioms, trusted computation,
  or raised elaboration limits in the nine involved leaves.
- Completed imports were added to `RHTower.lean`; the umbrella was not compiled.
- The core limiting premise is closed. General signed positivity, energy-domain
  coverage of arbitrary source mixtures, and joint aperture/shift control remain
  mathematical research tasks; they are not assumptions of the certified results.
