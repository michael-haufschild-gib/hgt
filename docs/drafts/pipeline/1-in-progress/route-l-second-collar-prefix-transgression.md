# Route L: original second collar and finite-prefix transgression

- **ID:** RH-L-C66
- **Stage:** 1-in-progress
- **Target:** Full-source fixed Gamma/BV reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.

C65 made verified progress: every original native collar is admitted in the
all-exponential Meyer source, and its original prime-anchored radial tail is
integrable with an exact source-derived horizontal mass. The next obstacle
is the whole second collar and its comparison with the fixed reader.

Write `H_h(y)=h(log|y|)`, `Q_p(h)(y)=Σ_(n<p) μ(n)h(log(n|y|))`, and let
`A_p(h)` be the complete tail starting at the unchanged original index `p`.
For `y≠0`, absolute summability gives `A_p(h)=M(h)-Q_p(h)`, where `M` is
the existing even all-integer Möbius preimage. The original source
`h=h_(k,m)` has the exact exchange

```
Jh(t)=(-1)^k exp((m-1)t)h(t).
A_p(Jh)(y)=(-1)^k |y|^(m-1)
  Σ_(n≥p) μ(n)n^(m-1)h(log(n|y|)).
```

This is the same native depth and internal jet. The two powers cannot be
separated by dropping the physical factor. Strong source admission of `Jh`
should prove absolute convergence of the weighted sum, including all positive
depths. The all-integer-minus-finite-prefix identity should prove integrability
of the complete second tail.

The intended distribution-level comparison retains the whole prefix:

```
K_p(h)=Fourier(D A_p(h))-D A_p(Jh)
QBoundary_p(h)=Fourier(D Q_p(h))-D Q_p(Jh)
K_p(h)=K_0(h)-QBoundary_p(h).
GammaBoundary(h)-K_p(h)
  = ExistingGreenStokesTransgression(h)+QBoundary_p(h).
```

These are current paper proof targets. `GammaBoundary` here means the existing
adiabatic Gamma distribution. Its identification with the fixed degree-six
Gamma/BV reader is not assumed. No vanishing of `K_0`, `K_p` or the prefix
boundary is inferred; full distribution equality is stronger than the
specified fixed-reader equality and must not be substituted for it.
