# Route T: positive Borel Abel renormalization

- **ID:** `route-t-borel-abel-renormalization`
- **Stage:** 3-formalized
- **Route:** T2, C5b.2
- **Status:** unconditional finite identity and sharp above-half no-go proved in Lean

## Corpus-derived conjecture

Corpus search found the centered Wold recurrence, finite physical Abel transport, scalar
second-factorial Borel--Laplace identity, and the sharp prohibition on residual exponential rate
beyond half height. Their unproved common consequence was that source-cutoff Borel transport
should reproduce the finite `Wold - logMesh - holonomy` renormalization before any infinite
interchange.

## Proven result

Writing

```text
Q_N(x,xi) = exp(-i h_N x) Phi(-i h_N xi),
```

Lean proves the exact finite identity

```text
R_N Q_N + sum_(n<N) R_n(Q_n-Q_(n+1))
  = sum_(n<=N) woldCoeff_n Q_n
    - sum_(n<N) (h_(n+1)-h_n)Q_(n+1)
    - (h_0+holonomy)Q_0.
```

Every node and edge on `xi=i y t` is individually Laplace integrable, and the integrated identity
is exactly the corresponding finite Wold--mesh--holonomy current at `s=-y+i x`. The difference
between this renormalized cutoff and the integrated raw edge cutoff is the terminal

```text
R_N exp(-i h_N(x+i y)),
```

with exact norm `|R_N| exp(y h_N)`. Its convergence to zero is equivalent to agreement of the two
finite-cutoff prescriptions. For every `y>1/2`, Lean proves that convergence impossible by reducing
it to the corpus sharp half-density residual-rate obstruction.

## RH contribution

This rules out both sourcewise absolute Tonelli and any attempt to continue first to a sector
wider than half height. Surviving chain is:

```text
strict-sub-half cancellation-first lateral landing
  -> exact terminal control
  -> identification with requiredResidual at s=-y+i x
  -> zero off-line principal part
  -> requiredResidual regularity
  -> RH endpoint.
```

Open burden is strict-sub-half lateral landing; no auxiliary wider-sector estimate can replace it.

## Lean audit

Module:
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelAbelRenormalization.lean`.

- `lake env lean` passes.
- Targeted `lake build` passes.
- Wired into `GaloisForLFunctions.RHTower` umbrella; umbrella build intentionally not run.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No computation, premise, added axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration is used.

