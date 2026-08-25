# Route P wild-saddle Stokes-parity quadratic anomaly

- **ID:** `route-p-wild-saddle-stokes-parity-quadratic-anomaly`
- **Stage:** 3-formalized
- **Type:** FALSIFIED / THEOREM (Lean)
- **Source:** Route-P one- and two-step irregular stationary-phase saddles
- **Statement:** Signed Stokes pairing kills each primewise linear coordinate, but the one-to-two-step wild-saddle correction has a strictly positive summable quadratic `det₂` anomaly.

## Goal

Decide whether opposite-orientation pairing, by itself, makes wild-saddle corrections
determinant-neutral. If so, changing stationary-phase depth could not change the paired `det₂`
coordinate. This tests the proposed cancellation mechanism behind the unresolved determinant
question left by `route-p-wild-saddle-minimal-trace-class-depth.md`.

## Gates

- [x] 0 → 1  in-progress: source-pure, exact falsifier, paper proof frozen
- [x] 1 → 2  fully-proven: hostile paper audit complete
- [x] 2 → 3  formalized: exact scalar anomaly theorem, targeted Lean check, axiom audit
- [ ] 3 → 4  publication-ready: standalone note and external review

## Conjecture and hostile verdict

The candidate was:

```text
opposite Stokes orientations cancel the full det₂ relocation anomaly.
```

It is false. For one paired eigenvalue `(+a,-a)`, the regularized factors obey

```text
((1-z*a) exp(z*a)) ((1+z*a) exp(-z*a)) = 1-z^2*a^2.
```

Pairing removes the degree-one exponential, not the square-spectrum factor. Replacing `a` by `b`
changes the factor unless `a^2=b^2`.

## Strongest positive survivor

For every Route-P prime label, let `a_p` be the one-step wild-saddle reciprocal and `b_p` the
two-step reciprocal. Then

```text
0 < b_p - a_p,
0 < b_p^2 - a_p^2,
sum_p (b_p^2-a_p^2) < infinity.
```

The signed linear correction is `(+delta_p,-delta_p)` and has zero primewise pair sum. Its
quadratic power-coordinate correction is exactly

```text
2 * (b_p^2-a_p^2) > 0.
```

Thus the first surviving Hilbert--Carleman coordinate is a positive source-only `l1` anomaly.
The one-to-two-step linear correction itself is not claimed trace class; its primewise
cancellation is only the proposed parity mechanism. Trace-class relocation supplies determinant
comparability, but parity cannot supply determinant equality.

## Paper proof

Put `L = log(M/e)`, `u1=L-log L`, and `u2=L-log u1`. Existing source estimates give `2 <= L`
and `1 <= u1 < L`. Strict monotonicity of `log` gives

```text
u2-u1 = log L-log u1 > 0.
```

The common denominator `2*pi*M` is positive, hence `0<a_p<b_p`. Therefore
`b_p^2-a_p^2=(b_p-a_p)(b_p+a_p)>0`. The two-step signed operator is Schatten-2, so
`sum_p b_p^2<infinity`; comparison `0<=b_p^2-a_p^2<=b_p^2` proves summability. The displayed
paired factor identity proves the determinant interpretation.

## No-go closure

- **Exact killing theorem/mechanism:** opposite orientations cancel each paired odd/linear
  coordinate; the even square-spectrum coordinate survives. No global first trace of the
  one-to-two-step correction is asserted.
- **Strongest positive survivor:** strictly positive summable quadratic wild-saddle anomaly.
- **New insight:** two stationary-phase corrections are sharp for trace-class Xi relocation, but
  no trace-class theorem can be promoted to determinant equality without an independent
  source-derived even Stokes/tau identity.
- **Status:** corpus search found target-side reciprocal-square collapse, RVM-specific paired
  products, and a different BV/Wold graded anomaly, but no one-to-two-step Route-P theorem.
  Bertola's Malgrange/Fredholm theory and Painleve-II Fredholm formulas retain independent Stokes
  parameters; regularized Fredholm product formulas explicitly retain a multiplicative anomaly.
  Exact Route-P application is `[CORPUS-NEW] [BRIDGE]`, not claimed as standalone determinant
  theory novelty. Formalized in
  `RHTower.RoutePWildSaddleStokesParityQuadraticAnomaly`; targeted Lean check is green and all new
  theorem declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-25 — candidate falsified; positive quadratic survivor frozen and paper-proved.
- 2026-08-25 — survivor formalized; direct module check and declaration-by-declaration axiom audit
  passed; umbrella import wired without an umbrella build.
