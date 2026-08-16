# Route P primitive Gamma--Julia raw cofinal trace obstruction

- **ID:** `route-p-primitive-gamma-julia-log-cofinal-trace-no-go`
- **Stage:** 3-formalized / needs audit
- **Type:** `[FALSIFIED] [POSITIVE SURVIVOR] [THEOREM] [P-G105H]`
- **Parent:** `route-p-primitive-gamma-julia-signed-bivariate-stability.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaLogCofinalTraceNoGo.lean`

## Goal

Test whether P-G105F/P-G105G prime-log-conjugated source matrices admit a raw trace-class cofinal
limit over all primitive prime-depth cells.

## Conjecturing loop

### Conjecture 1 — P-G186 cubic source regularization survives prime-log promotion

**Falsified exactly.** P-G186 diagonal source weight contains `(log p)^-2`. P-G105F primitive
promotion is congruence by `L=diag(log p)`, so its diagonal trace multiplies by `(log p)^2` and
cancels the entire logarithmic regularizer.

### Conjecture 2 — depth decay still makes the full promoted density summable

**Falsified by a principal slice.** Exact promoted density is

```text
w(p,e) = (1/4) p^{-(e+1)} (e+1)^-3.
```

At depth zero,

```text
w(p,0)=1/(4p).
```

Euler divergence of the prime harmonic series makes this slice, hence the full nonnegative
prime-depth density, nonsummable.

### Conjecture 3 — finite packet traces might remain uniformly bounded despite nonsummability

**Falsified.** Nonnegative density plus a uniform bound on all finite sums would imply summability.
Therefore positive finite-packet trace sums are unbounded.

## Paper proof

The P-G186 base weight is

```text
(216/115)(115/864) [p log(p)^2]^-1 p^-e (e+1)^-3.
```

The constants multiply to `1/4`. Multiplication by the two diagonal prime-log factors yields

```text
(1/4) p^{-(e+1)} (e+1)^-3.
```

P-G186 Gram diagonal equals its base weight independently of packet ordinate. Thus the real trace
of every actual finite matrix `L G L` is exactly the sum of this density over packet labels.
Restricting to `(p,0)` gives one quarter of `sum_p 1/p`, which diverges. Since all cells are
nonnegative, boundedness of all finite sums is equivalent to summability and is impossible. `QED`

## Positive survivor and novelty audit

No-go is not endpoint. Exact survivor is Euler-pole coefficient `1/4`, not only divergence. For
every finite prime set `S`, Lean proves

```text
4 sum_(p in S) w(p,0) = sum_(p in S) 1/p.
```

This identifies precise residue a completed polar/Stokes channel must cancel. Prime-log promotion
acts as a residue/differentiation operation: it consumes source's two-log trace regularizer and
exposes Euler wall. Finite signed stability from P-G105G does not address this phenomenon and
remains valid.

This is route-specific new knowledge because it is computed on literal P-G186 diagonal after
P-G105F operator-valued Gamma--Julia weld. It is not inferred from generic trace-class heuristics.
It agrees structurally with corpus's independent P-G100 quantized oriented-current/polar cancellation,
but no identification between those currents is asserted here.

## Formal status

Lean proves unconditionally:

- exact promoted density on every prime-depth cell;
- exact depth-zero `1/(4p)` law;
- nonnegativity;
- exact finite prime residue normalization;
- exact trace identity for every actual finite P-G186 log-conjugated Gram;
- nonsummability over all cells;
- unboundedness of all positive finite sums;
- premise-free P-G105H capstone.

Direct Lean and target-only module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Forbidden scan and `git diff --check` pass. Module is wired;
no umbrella build was run.

## Refined open core

Raw cofinal trace-class passage is retired. Construct source-derived aperture multiplier and
negative polar/Gamma channel which cancel exact Euler pole before wall limit, while preserving full
off-diagonal incidence, P-G105G signed bivariate stability, and divisor data. Free scalar
renormalization is excluded by corpus; cancellation must be literal completed-source geometry.

## Higher universal principle

Finite Krein stability and infinite nuclearity are orthogonal constraints. Channel chirality turns
negative index into anti-Pick stability, but primitive logarithmic Jacobian simultaneously shifts
summability by one Euler pole. Completion must therefore act twice: signed channel geometry controls
zeros, while source-derived polar transgression controls cofinal residue. Treating either as scalar
normalization erases the mechanism needed by the other.

## Log

- 2026-08-16 — P-G105H raw cofinal trace conjecture falsified; exact Euler-pole survivor
  paper-proved and formalized.
