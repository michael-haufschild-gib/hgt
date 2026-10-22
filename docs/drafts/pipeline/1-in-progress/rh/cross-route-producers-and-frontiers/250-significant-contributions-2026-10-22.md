# Cross-corpus research: 250 significant contributions

- **ID:** CROSS-250-2026-10-22
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME
- **Source:** `/Users/michael/.codex/attachments/9be6a181-d5da-4b1d-b9ad-ea3668abc26a/pasted-text-1.txt`
- **Target:** 250 distinct, significant contributions meeting the user's three permitted categories.
- **Accepted contributions:** 0. No existing result, context audit, equivalent criterion, routine bridge, numerical improvement, or no-go is credited.

## Completion requirements

1. Read the nine specified programme READMEs fully; keep them read-only.
2. On every goal turn, search the whole project corpus through `scripts/formal_tools.py research` before checking Mathlib or writing Lean.
3. Combine actual corpus results to discharge a significant hypothesis, significantly reduce the RH proof burden, or prove a significant new mathematical tool. User's subsequent instruction: **do not search the web; use conjecturing and the corpus search tool only**. This overrides the skill's external-search workflow. Do not claim a completed external novelty audit.
4. Run the conjecture, hostile audit, dependency-closed paper proof, Lean proof, and significance audit cycle. Rejected conjectures do not count; record their strongest positive survivor before retirement.
5. No added analytic premises, axioms, proof gaps, numerical experiments, or heartbeat increases. Audit each finished leaf with `lake --old env lean <file>`; one foreground build at a time, no full or umbrella builds. Wire new modules and refresh declaration indexes.
6. Preserve unrelated worktree changes. Record theorem names, precise scientific advance, prior-art comparisons, full proof, and final compiler/axiom evidence for every accepted contribution.

## Context reading checkpoint

Completed: root/formal instructions, formal guide and overview, `docs/reports/STATUS.md`; the following READMEs in full:

- `ScaleSignedIncidenceCriticality/README.md`
- `ArithmeticContinuationAndCriticalEnergy/README.md`
- `arithmetic-positivity-theory/README.md`
- `BiScaleUncertainty/README.md`
- `TransHorizonIncidenceMechanics/README.md`
- `BezoutValuationIncidence/README.md`
- `ArithmeticCriticalityTheory/README.md`
- `SquareRootThreshold/README.md`
- `ArithmeticIncidencePositivity/README.md`

All nine specified READMEs have been read fully. Their shared-target section is byte-for-byte identical to the SSIC section. Temporary source excerpts in `/tmp/hgt250-context/` omit only this verified duplicate; `manifest.json` records source hashes and chunk counts. These excerpts are reading aids, not modified source files. Frontier-map inspection has started; source-specific entries still need examination before selecting a conjecture.

## Facts controlling conjecture selection

- All nine programmes address the same complete signed form. A new equivalence between its names does not discharge its sign.
- APT already proves the entire limiting critical prime kernel strictly negative on every finite real pattern, via singleton mean and Poisson-window bounds. Its complete-form positivity on blocks, polynomial windows, compact truncations and lacunary unions still uses a growing archimedean term. None is new work for this programme.
- ACCE's averaged signed relative-loss criterion is an admission equivalence. Pointwise or absolute-loss formulations must be checked against exact Lean statements; README prose sometimes conflates them. The unpaid input is a source-derived, horizon-uniform covariance bound.
- SSIC's faithful band and rate readings supply reconstruction, not estimates. Bounded aperture certificates cannot establish a universal zero-width bound.
- THIM's eventual sign for finite-sieve polarization defects does not bound the centered-prefix pronic energy. BVI's complete-period and unbalanced-scale bounds leave the balanced signed source unpaid.
- SRT proves the reverse ground-energy-rate arrow under `OffLineCopiesLocallyBounded M`. Without that assumption its unconditional reverse arrows use an archimedean or derivative-weighted norm, rather than the `L²` norm consumed by the ground-energy path. The exponent identity without a local count is explicitly open.
- The actual width-rate source and its card are newer than this README description: `OffLineDepthLocallyBounded W` replaces the count premise by a uniform bound on squared depths in every unit-height window. `UnsignedDepthSamplingDetectsLocalMass` proves that the corresponding unsigned sampling bound at even one fixed aperture is equivalent to this local arithmetic bound. A derivative-free unsigned estimate would therefore reinsert, not discharge, the missing hypothesis.
- AIP's per-strip estimates cannot be added without allocation. Its prime-comb reduction leaves a cross-prime second moment, with positive cross terms on the already-proved resonant trains; a criterion for that moment is not an estimate for it.
- Possible substantial targets: remove the local off-line-depth sampling premise in the reverse ground-rate theorem; derive signed source control from arithmetic dilation/inversion identities; transfer critical-family positivity without the archimedean term. These are research questions, not proved contributions.

## Search evidence

- Whole-corpus hybrid search: `arithmetic incidence positivity critical energy signed scale RH missing hypothesis`. Finished, `partial=false`; semantic coverage incomplete, compiler enrichment pending. Hits included the RW signed Markov/pole card and prior criticism of circular nodal-defect criteria. Search results are source evidence, not compiler certificates.
- Whole-corpus hybrid search: `signed damping work covariance prime dilation`; results saved at `/tmp/hgt250-context/search-signed-work.json`, inspected. Prior work already supplies the exact continuous log-dilation equation and complementary-current decomposition. The source sign is unpaid.
- Whole-corpus hybrid search: `ground energy rate L2 off-line zero sampling H1`; results saved at `/tmp/hgt250-context/search-ground-rate.json`. `partial=false`, no errors; coverage snapshot is older than current generation, semantic coverage incomplete, compiler enrichment pending. Relevant sources: `TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster`, `TheZeroWidthIsALandauExponent`, `ComplexLocalSamplingAtDepth`, `CCMFiniteSamplingGroundRigidity`, and the two width-to-floor pipeline cards. No source-only result is treated as a fresh compiler certificate.

## Next action

Formalize C002's dependency-closed paper proof, beginning with centered heat bounds, then phase recurrence and the quantitative smooth cutoff. C001 remains open. Use corpus searches and conjecturing only, per user correction. Do not credit context work as a contribution or mark the 250-result goal complete.

## C001 — signed width-to-ground-energy law

**Exact conjecture.** For the actual Riemann zeta function,
`GaloisForLFunctions.SquareRootThreshold.polarGroundEnergyRate = zetaZeroWidth`.
A stronger producer target is: for every real `β > zetaZeroWidth` there is `C ≥ 0` such that
`Re Wζ(f,f) ≥ -C exp(2βA) ∫|f|²` for every `A > 0` and every smooth compact complex test
supported in `[-A,A]`. Neither target assumes an off-line count, a depth-mass bound, RH, or a
test-dependent constant.

**Why this matters.** It would remove the sole extra arithmetic premise from the sharp reverse
ground-rate arrow, completing the currently one-sided comparison between a zero width and the
operator's negative-energy exponent. It would not itself bound the width or prove RH.

**Exact existing input.** `zetaZeroWidth_le_polarGroundEnergyRate` is unconditional;
`polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineDepthLocallyBounded` is conditional on
`OffLineDepthLocallyBounded W`. The unconditional polar floor has exponent `1` in aperture.
The source quadratic is the absolutely convergent zero sum on smooth interior sources.

**Attack.** The analogous assertion for arbitrary strip configurations is false: the corpus
already contains clustered off-line configurations with logarithmic local count and an
unbounded-below form. Dropping the positive square in
`4 Re(u conj v) = |u+v|² - |u-v|²` returns the already-characterized unsigned sampling problem.
The exact signed compensation must use the actual zeta source. A bounded aperture, a prescribed
derivative class, or the fact that each fixed aperture is semibounded does not establish the
claimed exponential rate.

**Verdict:** `SURVIVES PRELIMINARY ATTACK` for actual zeta; no paper proof, no Lean proof,
no contribution credited. `[OPEN CORE]`: bound the negative part of the *difference* of the two
zero-side square energies at rate `2β`, uniformly over all tests, without separately bounding
the unsigned depth energy by an unavailable local depth-mass constant.

## Rejected shortcuts after C001

- Convexity of the damped Möbius energy already implies admission in `TheEscapeIsAnInteriorBump`; no source curvature estimate was obtained.
- The pronic dilation norm and sharp Hardy estimate are already supplied by `TheDilationSelfSimilarityOfThePronicMeasure` and `TheDilationHardyInequalityOnThePronicMeasure`. Their new normalization would be rediscovery, not a contribution.
- No no-go theorem is claimed here. These are novelty rejections with existing positive survivors, not newly retired mathematical routes.

## C002 — effective detection from any off-line zero

**Exact candidate.** There exist absolute constants `C > 0` and `b > 0` such that every actual zeta zero `rho = 1/2 + eta + i gamma` with `delta = |eta| > 0` admits a smooth compact complex test `f`, supported in `[-A,A]`, with

```text
A <= C delta^(-2) (3 + |gamma|)^b,
Re W_zeta(f,f) < 0.
```

No near-top, attained-top, spectral gap, zero separation, or uniformly bounded local off-line count is assumed. This concerns the full test cone; it does **not** assert a comparable bound for the fixed two-bump lag family. A smooth approximation must retain the stated support bound and strict sign.

**Potential significance.** The current explicit contact-aperture receiver requires a near-top zero. The proposed bound would replace that global premise by the data of any one off-line zero. Merely recovering qualitative Weil detection, or changing an existing numerical bound, would not qualify.

**Proposed mechanism, not yet a closed proof.** Center spectral points at `gamma` and set
`H_gamma(t) = sum_q exp(-t (z_q-gamma)^2)`. Localize the head to `|Re z_q-gamma| <= 1`; its copy count is `N = O(log(3+|gamma|))`. Simultaneous phase recurrence makes every head term have real part at least half its modulus at some `t = k T`, `1 <= k <= 16^N`, where `T` is of order `delta^(-2) log(3+|gamma|)`. The known zero then forces `H_gamma(t) > H_gamma(1)`; the outer tail is bounded using `sum |z_q|^(-2) < infinity` and the strict half-strip. A positive derivative gives a negative Weil value for an odd Gaussian modulated to `gamma`. Weighted second-derivative tail bounds should permit compact cutoff at a polynomially bounded aperture.

**Existing parents checked.** `FiniteOffLineSetsAreVisible` needs a finite off-line set and depth gap. `NearTopZerosForceNegativeGroundEnergyBeyondAnExplicitAperture` needs global near-topness. The heat Turan bottom-pair detector assumes a bottom conjugate pair; the tilted heat zero detector is qualitative. Polynomial Gaussian heat criteria already detect arbitrary off-line zeros qualitatively. None of these observations by itself proves novelty of the effective claim.

**Verdict:** `SURVIVES PRELIMINARY ATTACK`, provisionally. The complete
[paper proof](../../../2-fully-proven/centered-heat-polynomial-aperture-detection.md) is recorded.
It proves aperture at most `C delta^(-2) (4+|gamma|)^38` using the actual logarithmic local count,
eight-box phase recurrence, a positive heat derivative, and a quantitative smooth cutoff. There
is no open paper dependency. Lean implementation started in
`formal/GaloisForLFunctions/RHTower/XiCenteredHeatBounds.lean`; it is not yet audited or wired.
No contribution is credited until the exact theorem is formalized and its significance audited.

**Search checkpoint.** Whole-corpus searches `arbitrary zero explicit aperture no separation no top`, `shifted Gaussian heat trace monotone derivative Riemann`, `simultaneous phase approximation Gaussian centered heat finite aperture`, `effective Weil criterion`, and `Gaussian simultaneous approximation` completed with `partial=false` and no errors. Some snapshots have incomplete semantic coverage; compiler enrichment is not a certificate. The recurrence search found `HTGeometry/DirichletSimultaneousApproximation.lean`.

**Additional comparison.** `GaussianArithmeticBoundedCeilingReceiver` proves qualitative centered
heat amplification, with no finite time bound. `wd-heated-offline-detection.md` uses a deleted-pair
inverse-square mass and `Xi(gamma) != 0`. `GaussianZetaGeometry` isolates an exposed Gaussian
packet and takes a qualitative limit. C002 does not use those separation inputs. Source identity
is already unconditional in `CCMZetaWeilSmoothIdentity`; the `SuzukiWeilTestSpace` diagonal
modulus-square formula assumes RH and must **not** be used here.

**Implementation checkpoint.** The API probe `/tmp/hgt250-context/probe-centered.lean` compiled
successfully after correcting the Mathlib import to `Analysis.Calculus.SmoothSeries`. First leaf
check found only a reciprocal-norm simplification mismatch and an unused binder; a revised leaf
also includes derivative-term domination and is being checked. No missing analytic premise has
been introduced. The declared constants and estimates are intermediate proof infrastructure,
not separate contributions.
