# Suzuki positive completed Mellin finite part

- **ID:** `suzuki-positive-completed-mellin-finite-part`
- **Stage:** 5 — failed/retired
- **Status:** `[FALSE CLASS] [LEAN-REFUTED] [POSITIVE SURVIVOR EXTRACTED]`
- **Killed claim:** after the unital cofinal obstruction, dropping the unit or changing regulator
  can still produce a positive finite-valued Suzuki completion containing a critical-strip Mellin
  profile and preserving all finite source cutoffs.

## Exact killing theorem

For every nonnegative nonsummable mass `w*f`, positivity on a linear domain containing `f` and all
finite truncations forces every finite partial mass below the single real number `Phi(f)`.  This is
impossible.  Any exact linear extension is also unbounded below on the domain's full nonnegative
cone, because a global lower floor plus positive scaling forces positivity.

For the actual Suzuki critical transport,

```text
w(p)f_sigma(p) = Lambda(p) exp(-sigma log p),
Summable(w*f_sigma) <-> 1 < sigma.
```

Thus the whole completed left-half family (`sigma < 1/2`) is excluded.  The obstruction uses no
unit, continuity, normality, topology, cutoff scheme, or choice of regulator.

## Strongest positive survivor

`SUZUKI-SIGNED-NORMALIZED-ANOMALY`:

1. retain exact finite-aperture source values;
2. descend the principal logarithmic shell modulo the trace/Schatten relative ideal;
3. use a canonical signed finite part, not a positive weight;
4. seek a lower floor only on the source-normalized non-conic family consumed by the RH endpoint;
5. prove that floor from the Burnol anomaly and connect it to completed left-half positivity.

The survivor is nontrivial: the theorem determines the necessary order geometry of any remaining
Suzuki proof.  Positivity may survive on a normalized family, but not on the ambient positive cone.

## New insight

Failure is carried by the completed profile itself, not by the order unit or a bad cutoff.  Hence
no alternate positive-semifinite completion assigning that profile a finite value can solve the
problem.  Remaining work is uniquely pushed into signed canonical anomaly/coercivity.

## Status

- Paper and Lean certificate:
  `../3-formalized/new_scientific_knowledge/suzuki-completed-mellin-positive-domain-no-go.md`.
- Lean module:
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCompletedMellinPositiveDomainNoGo.lean`.
- Build passed 2026-07-22; key theorems use only standard Lean axioms.
- Full Suzuki lane is not retired: signed Burnol anomaly remains a logically live source class.

`NO POSITIVE SALVAGE FOUND` does not apply: signed source-normalized finite-part descent is the
precise survivor.

## Log

- 2026-07-22 — positive completed-profile class retired by universal domain-independent theorem.
