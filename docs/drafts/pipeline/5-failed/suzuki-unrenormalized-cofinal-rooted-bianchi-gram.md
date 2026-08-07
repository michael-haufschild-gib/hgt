# Suzuki unrenormalized cofinal rooted Bianchi Gram

- **ID:** `suzuki-unrenormalized-cofinal-rooted-bianchi-gram`
- **Stage:** 5 — failed/retired
- **Status:** `[FALSE] [LEAN-REFUTED ARCHITECTURE] [POSITIVE SURVIVOR EXTRACTED]`
- **Killed claim:** standalone raw rooted Bianchi Hilbert leg can be passed cofinally at Suzuki
  critical source weight.

## Exact obstruction

Corpus raw diagonal is

```text
b_x(p)=Lambda(p)/p * exp(-x log p).
```

Critical screw normalization forces `x=-1/2`, hence

```text
b_(-1/2)(p)=Lambda(p)/sqrt(p) >= log(2)/p.
```

Euler prime-harmonic divergence proves `sum_p b_(-1/2)(p)=infinity`.  Existing unique complete
Gamma-conormal boundary renormalization has coordinate `sqrt(b_x(p))`; at critical displacement it
therefore has divergent squared norm.  Moreover any constant residual multiple `c sqrt(b)` is
square-summable iff `c=0`.

Consequently original cofinal equation

```text
Gram(J-mB)+Gram(archimedean remainder)
```

is invalid if `B` is first assigned standalone critical `ell^2` limit.  This does not refute any
finite-cutoff Gram.

## Positive survivor

`SUZUKI-FINITE-APERTURE-RENORMALIZED-MIDPOINT-GRAM`:

1. keep physical Euler/Volterra aperture finite;
2. form actual prime coordinate
   `R_M(p;z)=J_M(p;z)-m B_M(p)+L_M(p;z)` with source-derived boundary leakage `L_M`;
3. combine exact Gamma/polar counterterm in canonical compound kernel;
4. prove finite kernel is Gram;
5. pass cofinally only after coordinatewise leading critical mass has cancelled.

Scalar rigidity proves cancellation must remove complete leading `B` coefficient.  Global scalar
renormalization, finite border, and “positive remainder” outside square cannot repair route.

## Paper and Lean status

- Paper proof:
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki/suzuki-critical-rooted-bianchi-cofinal-no-go.md`.
- Lean proof:
  `formal/GaloisForLFunctions/RHTower/SuzukiCriticalRootedBianchiCofinalNoGo.lean`.
- Formal certificate:
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki/suzuki-critical-rooted-bianchi-cofinal-no-go-formalized.md`.

`NO POSITIVE SALVAGE FOUND` does not apply: finite-aperture cancel-before-limit survivor is exact
and strictly stronger architecturally.
