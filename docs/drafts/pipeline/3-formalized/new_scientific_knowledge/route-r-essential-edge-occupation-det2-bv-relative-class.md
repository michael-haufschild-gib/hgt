# Route R essential-edge occupation `det2` / BV relative class

- **ID:** `route-r-essential-edge-occupation-det2-bv-relative-class-formalized`
- **Stage:** 3-formalized
- **Type:** SOURCE-DERIVED DIAGONAL OPERATOR / REGULAR-SINGULAR RELATIVE CLASS
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `route-r-prime-essential-edge-schatten-threshold.md`
- **Open successor:**
  `../../1-in-progress/route-r-essential-edge-occupation-det2-bv-relative-class.md`

## Exact theorem

For every ordinary prime `p`, the first two coordinates of the literal strict-preclosure source
edge recover the canonical nome without retaining the auxiliary Bertrand prime:

```text
a_p(1) = -p/farPrime(p),
a_p(2) = 1/p - p/farPrime(p)^2,
a_p(2) - a_p(1)/farPrime(p) = 1/p.
```

Multiplicative occupation condensation of these source-derived nomes gives the diagonal spectrum
`1/N(nu)`, hence every reciprocal positive integer exactly once. The resulting kernel is
Hilbert--Schmidt but not trace class. Its quadratic Hilbert--Carleman cocycle and determinant are

```text
C_2(t) = t^2 zeta(2)/2,
det2(I - t Q_edge) = exp(gamma*t) / Gamma(1-t)
```

on the proved Hilbert--Schmidt disk; its polarized ratio is the exact Wold--Gamma phase.

For every prime, the off-multiple defect is governed by one relative spectral-zeta class

```text
Z_p(s) = (1-p^(-s))*zeta(s).
```

Its regular quadratic trace is `Z_p(2)`. Its singular first residue is `1-p^(-1)`, exactly the
unit-exponential Wold boundary mass and the coefficient multiplying the adjacent continued BV
source residue. Regular `det2` anomaly and singular BV first trace are therefore two grades of one
source-derived relative class, not an asserted equality between distinct numerical functionals.

## Lean realization

Module:

```text
formal/GaloisForLFunctions/RHTower/
PrimeEssentialEdgeOccupationDet2BVRelativeClass.lean
```

Load-bearing declarations:

- `primeFirstTraceEssentialEdgeNomeReal_eq`;
- `primeFirstTraceEssentialEdgeOccupationEntry_eq`;
- `not_summable_primeFirstTraceEssentialEdgeOccupationEntry`;
- `primeFirstTraceEssentialEdgeOccupationKernel_isHS`;
- `primeFirstTraceEssentialEdgeOccupationKernel_quadraticTrace`;
- `primeFirstTraceEssentialEdgeOccupationQuadraticCocycle_eq_woldGammaAnomaly`;
- `primeFirstTraceEssentialEdgeOccupationFredholmDet_eq_gamma`;
- `primeFirstTraceEssentialEdgeOccupationPolarizedDet_eq_gammaPhase`;
- `primeWoldBVRelativeDefectKernel_quadraticTrace`;
- `primeWoldBVRelativeSpectralZeta_residue_one_eq_woldBoundaryMass`;
- `primeWoldBVRelative_regularSingularClass`.

Verification:

- direct `lake env lean` on module: passed;
- repository formal lint: passed;
- targeted `lake build GaloisForLFunctions.RHTower.PrimeEssentialEdgeOccupationDet2BVRelativeClass`:
  passed, 9385 jobs;
- axiom audit of load-bearing theorems: `propext`, `Classical.choice`, `Quot.sound` only.

## Exact limit

`primeFirstTraceEssentialEdgeOccupationFredholmDet_ne_zero` proves the diagonal determinant is
nowhere zero. Thus this construction cannot itself annihilate the existing Xi landing. The open
Route-R theorem remains a sign-indefinite, genuinely off-diagonal, nonseparable source differential
acting before scalarization and annihilating the completed horizontal comparison. No such theorem,
and therefore no RH proof, is claimed here.

## Gates

- [x] exact source nome extraction
- [x] reciprocal-integer diagonal realization
- [x] Hilbert--Schmidt membership and non-trace-class threshold
- [x] quadratic Wold--Gamma cocycle
- [x] `det2` / Gamma product
- [x] regular Wold trace / singular BV residue unification
- [x] zero-free scalar-determinant obstruction
- [ ] source-derived arithmetic Xi annihilation
- [ ] RH
