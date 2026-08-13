# Hedenmalm completed source: line-conjugate Dirac resolvent

- **Label:** `P-G126`
- **Route:** P
- **Parents:** `P-G123`, `P-G125`, `BurnolHedenmalmCompletionDomain`
- **Status:** theorem and affine-source self-adjointness no-go proved in Lean

## Conjecture tested

Let `X` be maximal multiplication by real completed spectral coordinate, `f_rho` actual completed
first-divided Xi vector, `g` completed theta Fourier source, and
`z_rho = xiSpectralPointSupport rho`. Existing exact recurrence is

```text
X f_rho = z_rho f_rho + g.
```

Critical-line partner `rho#` should satisfy `z_(rho#)=conj(z_rho)` and
`f_(rho#)=star(f_rho)`. Writing `a=Re z`, `b=Im z`,

```text
u = (f_rho + f_(rho#))/2,
v = (f_rho - f_(rho#))/(2i),
```

conjecture exact real two-channel system

```text
(X-a)u = g-bv,
(X-a)v = bu.
```

Source occurs only in invariant channel; anti-invariant channel is source-free after pairing.

## Scientific decision gate

- **Success:** classify exact source-driven resolvent mechanism permitting nonreal spectral
  parameters despite formal self-adjointness; identify strongest positive odd-channel survivor.
- **Failure:** line conjugation contains further phase/multiplicity data; isolate that datum.
- Prove pointwise/`L²` star law, domain closure, both channel recurrences, source reality, and sharp
  nonzero/off-line criterion. No RH premise, computation, axiom, or abstract landing assumption.

## Prior-research audit

- 2026-08-13 — Searched `formal/`, formalized pipeline, support extraction log, paper-proven and
  failed cards. Existing corpus has divisor-side line-conjugate isometries and completed affine
  source recurrence, but no completed first-divided `L²` star law or paired real Dirac system.

## Conjecturing log

- 2026-08-13 — Opened exact two-channel conjecture before implementation. Expected obstruction:
  formal self-adjointness alone cannot force `b=0` because common nonzero source drives invariant
  channel and coupled odd response.

## Verification log

- 2026-08-13 — Direct `lake env lean` passed for
  `HedenmalmCompletedSourceLineConjugateDiracResolvent.lean`.
- 2026-08-13 — Exact module build passed: `12948/12948` jobs.
- 2026-08-13 — `#print axioms` audit passed for all capstones with only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-08-13 — Module is imported by `GaloisForLFunctions.RHTower`.

## Result and no-go closure

Conjecture is true, with stronger exact source-work law. Lean proves

```text
f_(rho#) = star(f_rho),                 star(g)=g,
star(u)=u,                              star(v)=v,
f_rho=u+i v,                            f_(rho#)=u-i v,
(X-a)u=g-bv,                            (X-a)v=bu.
```

Almost everywhere, with `D_x=(x-a)^2+b^2>0` off the null real-zero set,

```text
u(x)=XiC(x)(x-a)/D_x,
v(x)=XiC(x)b/D_x.
```

Thus odd response vanishes exactly when `b=0`, and global odd-response collapse is exactly RH.
More sharply, radial source-work density

```text
b Re(conj(v(x)) XiC(x))
```

is strictly positive almost everywhere for `b != 0`. Formal self-adjointness plus two-channel
system integrates this into exact identity

```text
b Re< v,g > = b^2 (||u||^2+||v||^2).
```

Right side is strictly positive off line because `f_rho` is nonzero and reconstructs from `u,v`.
Hence global zero radial source work is exactly RH.

This closes bare self-adjointness as producer: affine recurrence is not a defective eigenvalue
equation waiting for source cancellation. Common completed Xi source actively supplies precisely
positive work needed to sustain every nonreal paired response. Strongest survivor is an exact
passivity target: Route P must derive nonpositive/zero radial work from independent arithmetic or
boundary geometry; source recurrence itself forces opposite strict sign off line.
