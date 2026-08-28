# D2 order-23 source-height exclusion

- **ID:** `d2-order23-source-height-exclusion`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / unconditional zero-height and D2 threshold theorem (Lean)
- **Source route:** D2 plus centered order-23 fourth reciprocal trace
- **Statement:** Kernel-clean order-23 source budget should force every off-line Xi zero to have
  squared ordinate at least `431/2`, yielding a premise-free D2 threshold at `141799/10000`.

## Goal

Turn corpus's atomwise order-23 fourth-trace floor and global source cap into a zero-location
theorem the corpus does not yet state. Transfer resulting much taller verified-height band to an
explicit pure-prime D2 defect floor and delete full interval up to `141799/10000` from remaining
RH burden.

## Gates

- [x] 0 → 1 in-progress: corpus-derived source/atom contradiction and route passport
- [x] 1 → 2 fully-proven: dependency-closed paper proof and exact threshold theorem
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem note and independent expert audit

## Conjecture and pivot

Initial strongest target used sixth reciprocal trace through squared height `467/2`. Corpus has
the required atom floor and conditional source cap, but its only closed first-atom certificate
depends on `native_decide` axioms. Axiom audit exposed

```text
thetaRationalQuadrature_firstAtom_bounds._native.native_decide.ax_1_1.
```

That route is inadmissible under current no-computation/standard-axiom rules and is not used.

Kernel-clean pivot: corpus proves, with only standard axioms,

```text
normalizedPrimeArchMoment(1) < 17/200000,                (1)

2365/16 ≤ Im(q)^2 < 431/2 and q off-line
  => 17/800000 < Re(reciprocalSquare(q)^2),               (2)

4 Re(reciprocalSquare(q)^2) ≤ normalizedPrimeArchMoment(1). (3)
```

Together `(1)--(3)` are contradictory. Below `2365/16`, existing exact fourth-trace exclusion
already forces critical-line location. Conjecture:

```text
Im(q)^2 < 431/2  =>  Re(q)=1/2.                           (4)
```

Hence every `H` with `H^2<431/2` satisfies `RHVerifiedThrough(H)`.

For a verified band `R+1/2≤H`, prove generic source transfer

```text
0<Re s<1/2, 233/20<Im s≤R
  => -(log pi+log 2)-8 ≤ primeArchLogHeightDefect(s).      (5)
```

Then lower boundedness of D2 defect above any `R>233/20` with a verified band is equivalent to RH.
Specialize to

```text
R=141799/10000,
(R+1/2)^2<431/2.                                         (6)
```

## Attack

1. Split an alleged off-line copy below `431/2` at old `2365/16` exclusion.
2. In upper case, feed divisor strip bound `0<u<1/4` and height interval to order-23 atom floor;
   combine quartet domination and source cap by linear arithmetic.
3. Convert `(4)` to `RHVerifiedThrough(H)` for every `H^2<431/2`.
4. Prove reusable verified-height-to-pure-prime floor `(5)` using centered coordinate rotation and
   existing Stirling envelope.
5. Split canonical D2 sample set at `R`; combine floors by `min` and invoke existing endpoint.

## Proof

Let `q` be an Xi zero copy with `Im(q)^2<431/2`. Suppose it is off critical line. If
`Im(q)^2<2365/16`, exact fourth-trace height theorem already forces `Re(q)=1/2`, contradiction.
Otherwise

```text
2365/16 ≤ Im(q)^2 < 431/2.
```

Open-strip divisor bounds and off-line strictness give

```text
0 < (Re(q)-1/2)^2 < 1/4.
```

All hypotheses of order-23 atom estimate now hold, so `(2)` applies. Quartet domination `(3)`
implies

```text
17/200000 < normalizedPrimeArchMoment(1),
```

contradicting strict source cap `(1)`. This proves `(4)`, equivalently every off-line copy obeys

```text
431/2 ≤ Im(q)^2.                                         (7)
```

For `H^2<431/2`, any positive-height Xi zero of height at most `H` has squared ordinate below
`431/2`, hence lies on critical line by `(4)`. Therefore `RHVerifiedThrough(H)`.

For generic verified band `R+1/2≤H`, use centered coordinate

```text
z=Im(s)+i(1/2-Re(s)),       1/2+i z=s.
```

Verified-height accretivity yields nonnegative real completed prime--Gamma flux. Uniform
archimedean estimate gives

```text
Re(logDeriv archFactor(s)) ≥ log(Im s)/2-(log pi+log 2)/2-4.
```

Their sum proves `(5)`. Splitting old canonical sample set at `R` and taking minimum of lower and
upper floors proves generic threshold equivalence. Exact rational arithmetic closes `(6)` for
`R=141799/10000`; thus its D2 lower-bound condition is equivalent to RH.

## Strongest positive survivor and route impact

- **Rejected stronger route:** Sixth-trace frontier `467/2` currently depends on native-decision
  certificate and is inadmissible here.
- **Positive survivor:** Kernel-clean order-23 height gap `(7)`, generic verified-band pure-prime
  floor `(5)`, and premise-free D2 endpoint at `141799/10000`.
- **New insight:** Existing order-23 source budget was used only to close angular moment
  positivity, but its atom floor already forbids every off-line divisor in full height annulus.
- **Remaining burden:** Prove one common pure-prime defect floor only above `141799/10000`.
  Compared with prior `58289/5000`, additional interval of width `252101/100000` is discharged.

## Novelty audit

Mandatory corpus search found all three inequalities `(1)--(3)` in separate order-23 modules,
but no theorem combines them into `(4)`, no verified-height certificate through the order-23
frontier, and no D2 threshold transfer. Primary searches through 2026-08-28 found numerical
finite-height RH verification, reciprocal/power-sum criteria, and zero-density estimates, but no
noncomputational order-23 source-moment exclusion or pure-prime defect endpoint `(4)--(6)`.
Candidate novelty is restricted to this exact source synthesis.

Primary comparison:

- D. Platt and T. Trudgian, [*The Riemann hypothesis is true up to
  `3·10^12`*](https://arxiv.org/abs/2004.09765).
- A. Simonič, [*Explicit zero density estimate for the Riemann zeta-function near the critical
  line*](https://arxiv.org/abs/1910.08274).

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/PrimeArchLogHeightDefectOrderTwentyThreeThresholdAdvance.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct source check: PASS
- Targeted build: PASS (`12855/12855`)
- Axiom audit: every principal declaration uses exactly
  `[propext, Classical.choice, Quot.sound]`; no native-decision axiom occurs.
- Principal declarations:
  `xiZeroCopy_re_eq_half_of_im_sq_lt_fourHundredThirtyOne_halves`,
  `fourHundredThirtyOne_halves_le_im_sq_of_xiZeroCopy_offLine`,
  `rhVerifiedThrough_of_sq_lt_fourHundredThirtyOne_halves`,
  `primeArchLogHeightDefect_lower_of_verifiedHeightBand`,
  `primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_iff_rh_of_verifiedHeightBand`,
  `rhVerifiedThrough_xiOrderTwentyThreeD2Threshold_add_half`,
  `primeArchLogHeightDefect_lower_of_orderTwentyThreeBand`,
  `primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_xiOrderTwentyThreeThreshold_iff_rh`.
- Formal lint: new wired module clean; repository-wide reachability failures belong only to
  unrelated unwired dirty-tree modules.

## Log

- 2026-08-28 — Mandatory search identified sixth-trace `467/2` route, but axiom audit rejected its
  native-computation certificate.
- 2026-08-28 — Pivoted to strongest standard-axiom source package: order-23 fourth trace through
  `431/2`.
- 2026-08-28 — Proved order-23 off-line height gap, generic verified-band D2 floor and threshold
  equivalence, exact rational verified-height certificate, and premise-free endpoint in clean Lean
  scratch.
- 2026-08-28 — Formalized, wired umbrella, passed direct check, standard-axiom audit, local lint,
  and targeted `12855/12855` build; promoted to fully proven.
