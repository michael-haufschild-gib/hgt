# Route T: forced rotated Borel landing and divisor charge

Status: `LEAN-PROVED`

Module:
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelStokesCharge.lean`

## Result

The forced source-coordinate continuation

```text
B_req(z) = xiHeatCassiniWoldResidualLaplaceContinuation(i z)
```

equals the lower-Hardy residual on `Im z < 0`, and therefore equals the proved source-ordered
negative-ray Borel--Laplace sum there. Every zeta zero `rho` with `Re rho > 1/2` and multiplicity
`m >= 1` produces the exact rotated residue

```text
lim_(z -> -i(rho-1)) (z+i(rho-1)) B_req(z) = i m.
```

Under critical prime-gap energy, RH is equivalent to continuity of this forced continuation at
all rotated candidate poles.

## Route consequence

Any positive-ray lateral continuation must land on this same branch and eliminate this exact
quantized charge. Module does not assume or construct missing lateral continuation.

## Audit

- `lake env lean` passed.
- Targeted module build passed.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.

