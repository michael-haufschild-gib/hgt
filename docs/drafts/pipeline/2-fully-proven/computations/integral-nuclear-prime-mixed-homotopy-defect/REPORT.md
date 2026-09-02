# ULF-INHD-001 Runpod computation audit

- **Date:** 2026-09-02
- **Route card:** `docs/drafts/pipeline/5-failed/universal-law-field/direct-subunit-anchor/integral-nuclear-prime-mixed-homotopy-defect.md`
- **Compute host:** Runpod `root@213.173.111.85:31945`, CPU-only, Python 3.8.10
- **Script:** `scripts/numerics/integral_nuclear_homotopy_defect_audit.py`
- **Raw result:** `runpod-results.json`
- **Result SHA-256:** `b51064ba47b745c3776fb64dc2cd2613cfcb759b6c70ac4b4d4fb506f21e391c`
- **Script SHA-256:** `dd9f4aad052ea9000deca3503bab6272cb1754a2cd79a1394774093ba793bb85`

Command used on Runpod:

```text
python3 /root/integral_nuclear_homotopy_defect_audit.py \
  --prime-limit 50000000 --depth-max 30 \
  --output /root/hgt-inhd-audit/results.json
```

## What was tested

The run enumerated 3,001,134 primes through 50,000,000 and evaluated the full prime-depth source
budget, exact base/collision kernels, eight-cell prime/depth packets under zero, clustered, and
mixed ordinate clocks, all eight diagonal sign gradings of the three P-G194 channels over aperture
`0 <= c <= 64`, projection-pair trace norms, finite coherent zero-defect factorizations, anomaly
subtraction, P-G196 eigencharacter gaps, and the P-G206 rank-one environment short. Critical
grading residuals were re-evaluated at 80 decimal digits.

## Main results

- Exact one-cell calculation gives collision charge `115/864`, base/collision ratio `216/115`,
  and half-base/collision ratio `108/115`. Aperture-scale swap does not commute with the doubled
  Gram: commutator entry is `7/32`.
- Computed collision budget is at least `0.21468250813666773`. The evaluated analytic truncation
  bound gives at most `0.2221907074040952`; hence half-base mass lies numerically in
  `[0.2016148772066097, 0.20866605564906332]`, far below one.
- Base and collision packet matrices were positive semidefinite to floating-point tolerance. Their
  off-diagonal entries are not scalar multiples: best scalar-fit relative residual is `4.62%` at
  zero/clustered clocks and `11.38%` at mixed clocks.
- P-G194 three-channel Gram conservation held with relative residual below `8e-17`.
- Every fixed diagonal `+/-` grading of those three channels failed to give zero finite defect.
  Global scan minimum was `8.894%` residual at zero/clustered clocks and `11.477%` at mixed clocks;
  80-digit reevaluation confirmed both values.
- At centered rate `a=1/4`, formation and companion partial sums grew from about `298` to `5267`,
  while their relative source remainder stabilized near `0.20223`, matching the proved
  non-trace-class/trace-class subtraction pattern.
- Symbolic P-G206 block `[[c^2,c],[c,1]]` has determinant and Schur short exactly zero.
- A rank-difference-one projection pair attained trace norm exactly one; 500 random pairs all had
  larger trace norm. Coherent equal positive/negative finite factors retained defect exactly zero
  at every packet size.

## Preliminary interpretation

**Verdict: `SURVIVES PRELIMINARY ATTACK`; continue at Stage 1 only.** Scalar capacity, full
off-diagonal source Gram, anomaly cancellation, aperture anomaly, and environment shorting all
behave as required. Computation falsifies two shortcuts: importing the diagonal collision/base
ratio entrywise, and using any fixed diagonal grading of the three P-G194 channels.

This is not evidence for ULF-INHD-1 or ULF-INHD-2. No computation constructs the required
source-canonical non-diagonal landing, the two completed horizon projections, or their escape/index
identification. Moreover, any bounded trace-norm-coherent limit of zero finite defects remains
zero. A surviving construction must therefore exhibit a genuine singular boundary/extension
mechanism and prove why its completed trace-class defect is not the trace-norm limit of the finite
zero defects. Without that theorem, no paper-proof or Lean promotion is justified.

Raw numbers are computational evidence, not certified interval arithmetic or proof. Exact
inequalities and identities remain those already proved in the Lean corpus.

## Final post-computation decision

Subsequent corpus and operator-theoretic audit closes the surviving non-diagonal singular-landing
loophole for this architecture.  The route is **retired**, not continued.

The computation showed that bounded finite packet factors either retain a nonzero defect or, when
made coherent with the actual zero finite horizons, give defect exactly zero.  Corpus theorems make
this exhaustive at completion level:

- `routeR_no_continuousArithmeticCoreHorizonLanding` says a continuous landing vanishing on the
  dense finite arithmetic core is zero and cannot retain the horizon;
- `deningerCalderonWittCrossPrimeClosedRelation_eq_top_prod_vertical` says the closed-relation
  alternative has a source-independent vertical fibre;
- `closedLinearRelation_completeResolutionPrimeHilbert_fullVertical` says retaining all affine
  prime-normal packets forces the whole Hilbert target to be vertical;
- `TraceNormLimit.traceTower_limit` says trace-norm coherent zero finite defects retain trace zero.

Therefore the proposed source factorization has only two horns.  A bounded/contractive
Hilbert--Schmidt landing inherits the subunit budget but forces completed defect `T=0`.  A genuinely
singular landing may retain the rank-one horizon but cannot inherit the estimate
`||T||_1 <= ||Abar||_2^2`.  Relative-index theory makes a trace-class projection difference
integral after it exists; it does not construct the missing arithmetic/theta comparison.

Interpretation for future agents: do not rerun larger prime cutoffs or search more channel
gradings for ULF-INHD-001.  Those computations cannot resolve this topological dichotomy.  Any new
route must change source topology before completion, act nontrivially on actual finite arithmetic
witnesses, and prove a new norm estimate native to that topology.  Reusing the old half-base
budget through a bounded landing is closed.

Primary-source cross-check: Avron--Seiler--Simon, *The Index of a Pair of Projections*, JFA 120
(1994), proves integrality for trace-ideal projection differences; Bunke's relative index theory
assumes the Fredholm/invertibility-at-infinity structure needed to define the relative class.
Neither supplies the missing arithmetic producer.
