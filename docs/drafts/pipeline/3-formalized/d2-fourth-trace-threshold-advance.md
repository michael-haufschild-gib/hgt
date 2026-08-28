# D2 fourth-trace threshold advance

- **ID:** `d2-fourth-trace-threshold-advance`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / quantitative D2 source theorem (Lean)
- **Source route:** D2 pure-prime log-height defect
- **Statement:** The exact fourth reciprocal-trace exclusion yields an unconditional explicit
  lower floor for the pure-prime log-height defect throughout every band
  `233/20 < Im s ≤ R` with `(R+1/2)^2 < 2365/16`, and therefore raises D2's RH-equivalent tail
  threshold to any such `R`.

## Goal

Exploit margin hidden by rounded verified-height constant `243/20`. Existing D2 endpoint begins at
`233/20` because verified-height transfer loses one half-unit. Corpus's stronger exact statement
places every off-line zero at squared ordinate at least `2365/16`. Recover full algebraic margin,
prove literal pure-prime floor on newly exposed band, and remove that band from remaining D2
burden.

## Gates

- [x] 0 → 1 in-progress: corpus-derived exact squared-height attack and route passport
- [x] 1 → 2 fully-proven: dependency-closed paper proof and quantitative threshold theorem
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem note and independent expert audit

## Conjecture

Let

```text
D(s) = 2 Re(infinitePrimeFlux(s)) - log(Im s),
K    = -(log pi + log 2) - 8.
```

For every real `R` satisfying

```text
233/20 < R,        (R + 1/2)^2 < 2365/16,
```

prove unconditionally

```text
0 < Re s < 1/2 and 233/20 < Im s ≤ R  =>  K ≤ D(s).       (1)
```

Then prove

```text
PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow(R)
  <-> RiemannHypothesis.                                  (2)
```

An exact rational specialization will use `R=58289/5000`, for which Lean can close both strict
rational inequalities.

## Attack

1. Generalize fourth-trace certificate: if `H^2 < 2365/16`, every Xi zero through positive height
   `H` lies on critical line.
2. Put `H=R+1/2`. Verified-height relative-resolvent theorem gives
   `Re(completedPrimeGammaFlux(s)) ≥ 0` throughout target band.
3. Corpus Stirling estimates give
   `Re(logDeriv archFactor(s)) ≥ heightMain(Im s)-4`, with
   `heightMain(t)=log(t)/2-(log pi+log 2)/2`. Combine to prove `(1)`.
4. Split every Gaussian-rational sample above `233/20` at `R`. Use `(1)` below `R` and assumed
   tail floor above `R`; their minimum recovers old canonical D2 premise. Existing endpoint gives
   RH. RH gives converse immediately.

## Proof

Fix `H` with `H^2 < 2365/16`. Given a positive-height Xi zero `rho` with `Im rho≤H`, make its
multiplicity copy `q`. Positivity gives

```text
(Im rho)^2 ≤ H^2 < 2365/16.
```

The exact fourth-trace theorem therefore forces `Re rho=1/2`. Hence `RHVerifiedThrough(H)` holds
for every such `H`, with no imported computation.

Now fix `R` satisfying conjecture's inequalities and take `H=R+1/2`. For
`0<Re s<1/2`, `233/20<Im s≤R`, set

```text
z = Im(s) + i(1/2-Re(s)).
```

Then `0<Im z<1/2`, `|Re z|≤R`, and `1/2+i z=s`. Verified-height transfer gives

```text
Im(-i * completedPrimeGammaFlux(s)) ≤ 0,
```

so

```text
0 ≤ Re(completedPrimeGammaFlux(s))
  = Re(infinitePrimeFlux(s))-Re(logDeriv archFactor(s)).   (3)
```

Corpus's unconditional Stirling estimates on this band give

```text
Re(logDeriv archFactor(s)) ≥ main(s)-4
                           ≥ heightMain(Im s)-4,
heightMain(t)=log(t)/2-(log pi+log 2)/2.                  (4)
```

Combining `(3)--(4)` and doubling proves `(1)` with exact floor `K`.

For `(2)`, suppose D2 defect has floor `L` above `R`. On samples above old threshold `233/20`,
split at `R`. Below or at `R`, `(1)` supplies floor `K`; above `R`, hypothesis supplies `L`.
Thus `min(L,K)` is a global floor above `233/20`, and canonical D2 equivalence proves RH.
Conversely RH supplies canonical floor above `233/20`, hence above larger `R`.

Finally, exact rational normalization proves

```text
233/20 < 58289/5000,
(58289/5000 + 1/2)^2 < 2365/16,
```

so `(2)` has a closed premise-free specialization at `58289/5000`.

## Strongest positive survivor and route impact

- **Exact theorem:** Unconditional floor `(1)` for every exact fourth-trace band, generic threshold
  equivalence `(2)`, and premise-free rational specialization.
- **New insight:** Rounded verified-height transfer discarded strict algebraic margin. D2's open
  tail need not begin at `233/20`; it may begin at any `R` satisfying exact square condition.
- **Remaining burden:** Prove one common floor above `58289/5000` (or any still larger threshold
  reached by future source moment exclusions). Entire interval from `233/20` through this new
  rational threshold is now discharged unconditionally.

## Novelty audit

Mandatory corpus search found exact squared-height exclusion, rounded verified-height transfer,
Stirling envelope, and canonical D2 threshold, but no theorem recovering algebraic margin or
raising pure-prime threshold. Platt--Trudgian rigorously verify RH to vastly greater height by
interval arithmetic; that literature result is computational and does not state this
reciprocal-trace-to-pure-prime defect transfer. Search through 2026-08-28 found no primary source
with `(1)--(2)` or rational threshold `58289/5000`. Candidate novelty is restricted to exact
source-theorem synthesis.

Primary comparison:

- D. Platt and T. Trudgian, [*The Riemann hypothesis is true up to
  `3·10^12`*](https://arxiv.org/abs/2004.09765).

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/PrimeArchLogHeightDefectFourthTraceThresholdAdvance.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct source check: PASS
- Targeted build: PASS (`12854/12854`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `rhVerifiedThrough_of_sq_lt_2365_over_16`,
  `primeArchLogHeightDefect_lower_of_fourthTraceBand`,
  `primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_iff_rh_of_fourthTraceBand`,
  `xiFourthTraceD2Threshold`,
  `primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_xiFourthTraceThreshold_iff_rh`.
- Formal lint: new wired module clean; repository-wide reachability failures belong only to
  unrelated unwired dirty-tree modules.

## Log

- 2026-08-28 — Corpus-first conjecture isolated from `2365/16` fourth-trace exclusion and D2
  `233/20` endpoint; frontier map kept read-only.
- 2026-08-28 — Primary-literature audit found numerical finite-height verification but no exact
  fourth-trace pure-prime threshold recovery.
- 2026-08-28 — Conjecture succeeded: proved generic verified-height certificate, explicit
  pure-prime floor, generic threshold equivalence, and rational `58289/5000` specialization in
  clean Lean scratch.
- 2026-08-28 — Formalized source module, wired umbrella, passed direct check, standard-axiom
  audit, local lint, and targeted `12854/12854` build; promoted to fully proven.
