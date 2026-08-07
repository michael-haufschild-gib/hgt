# Route R squarefull-tail Gamma–Cartier index

Status: `[PAPER-PROVED; LEAN-PENDING]`

## Frontier

Route R arithmetic-horizon globalization is already equivalent, pointwise at every Xi divisor
point `rho`, to

```text
routeRTwoThreeGammaCartierTransportPort rho = 0.
```

The missing source theorem must not assume centered-rate vanishing, critical-line placement,
same-fibre norm/source-dagger identities, or RH.

## Conjecture loop

### C1 — reflected activation products are the same source state

`[FALSIFIED]`. Euler–Gamma reflection changes every valuation-shell probability. Functional-equation
symmetry does not identify the two product measures. Assuming equality would hide the missing
same-fibre descent.

### C2 — reciprocal KMS tensor cyclicity annihilates the odd port

`[FALSIFIED]`. Modular-charge-balanced tensors are cyclic but erase the odd difference; unbalanced
tensors retain the port but are not cyclic. This is the previously recorded reciprocal-Gamma tensor
wall, not a new producer.

### C3 — one central squarefull-tail projection is a complete orientation detector

`[PROVED ON PAPER]`. For `0 < sigma < 1`, let `mu_sigma` be the Euler activation product and

```text
E2 = {K | {p : primes | 2 <= K(p)} is finite}.
```

The already proved level cascade gives

```text
mu_sigma(E2) = 1  iff  1/2 < sigma.
```

Its infinite-hit complement gives the missing zero half:

```text
mu_sigma(E2) = 0  iff  sigma <= 1/2.
```

Consequently the reflected pair has exactly three states:

```text
sigma < 1/2 : (mu_sigma(E2), mu_(1-sigma)(E2)) = (0,1)
sigma = 1/2 : (mu_sigma(E2), mu_(1-sigma)(E2)) = (1,1)
sigma > 1/2 : (mu_sigma(E2), mu_(1-sigma)(E2)) = (1,0).
```

Therefore

```text
mu_sigma(E2) = mu_(1-sigma)(E2)  iff  sigma = 1/2.
```

Off the center, `E2` is also an explicit mutual-singularity witness for the reflected activation
measures. No general Kakutani theorem is needed.

At `sigma = Re(rho)`, Xi-divisor open-strip support supplies `0 < sigma < 1`. Existing Route R
identifications then give the unconditional chain

```text
reflected squarefull-tail balance at rho
  iff Re(rho) = 1/2
  iff routeRTwoThreeGammaCartierTransportPort rho = 0
  iff arithmetic-horizon globalization at rho.
```

## Scientific delta

This does **not** prove reflected tail balance and therefore does not prove RH. It removes a larger,
previously open representation-theoretic burden: full GNS/Kakutani equivalence is unnecessary.
Arithmetic-horizon globalization is completely detected by equality of two probabilities on one
explicit pre-divisor central projection. The source producer may now target this single event.

The standard parents are Borel–Cantelli and mutual singularity of product measures. Project-specific
novel content is the exact identification of the level-two Euler activation phase projection with
Route R's Gamma–Cartier port/globalization obstruction.

## Anti-circularity audit

- no RH or critical-line hypothesis;
- no port, centered-rate, same-fibre norm, or source-dagger vanishing;
- no equality of reflected source states;
- only Euler activation product structure, level-two Borel–Cantelli threshold, Xi open-strip support,
  and already proved equivalences are used;
- remaining open theorem is explicit: derive equality of the two `E2` probabilities from independent
  pre-divisor Euler–Gamma Stokes structure.

## Lean target

New module:

```text
GaloisForLFunctions.RHTower.RouteRSquarefullTailGammaCartierIndex
```

Principal statements:

```text
eulerActivationProductMeasure_finiteSquarefull_eq_zero_of_le_half
eulerActivationProductMeasure_reflected_finiteSquarefull_eq_iff
routeREulerGammaSquarefullTailBalanced_iff_port_eq_zero
routeRTwoThreeGammaArithmeticCorona_global_eq_local_iff_squarefullTailBalanced
```

