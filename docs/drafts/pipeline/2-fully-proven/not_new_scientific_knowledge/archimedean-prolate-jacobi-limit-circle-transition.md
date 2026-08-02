# Archimedean prolate Jacobi limit-circle transition

- **ID:** `archimedean-prolate-jacobi-limit-circle-transition`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / DOMAIN CLASSIFICATION (paper)
- **Scientific status:** BRIDGE / NOT CLAIMED AS NEW SCIENTIFIC KNOWLEDGE
- **No RH input:** yes
- **No computation:** yes
- **Primary inputs:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators:
  semilocal adelic operators*, Proposition 3.5; Raphael Pruckner, *Density of the spectrum of
  Jacobi matrices with power asymptotics*, Theorem 2.
- **Lean infrastructure:**
  `formal/GaloisForLFunctions/RHTower/SemilocalProlateCriticalPotential.lean`

## Theorem

Fix a positive prolate parameter `lambda`.  Each of the even and odd archimedean prolate parity
Jacobi minimal operators is in the limit-circle case.  Hence each has deficiency indices `(1,1)`,
and the full parity-preserving minimal operator has deficiency indices `(2,2)`.

At `lambda=0`, both parity blocks are in the limit-point case.

## Proof

The parent prolate paper gives the positive-phase even-parity Jacobi parameters

```text
rho_n^+
 = (1/4)sqrt((4n+1)(4n+2)(4n+3)(4n+4)),

q_n^+
 = -8n^2-2n-3/4+2 pi lambda^2(8n+1).
```

Expanding the exact polynomial under the square root gives

```text
rho_n^+ = 4n^2+5n+5/4+O(n^-2),
q_n^+   = -8n^2+(16 pi lambda^2-2)n+O(1).
```

Thus Pruckner's exceptional power-asymptotic notation has

```text
beta=2, x_0=4, x_1=5, y_0=-8, y_1=16 pi lambda^2-2.
```

The critical ratio is `2x_0=|y_0|`.  Its next-order transition parameter is

```text
2x_1/x_0 - 2y_1/y_0 = 2+4 pi lambda^2.                 (1)
```

For `lambda>0`,

```text
3/2 < beta=2 < 2+4 pi lambda^2.
```

Case (ii) of Pruckner's exceptional theorem therefore puts the even block in the limit-circle
case.

For the odd block the parent parameters are

```text
rho_n^-
 = (1/4)sqrt((4n+3)(4n+4)(4n+5)(4n+6)),

q_n^-
 = -8n^2-10n-15/4+2 pi lambda^2(8n+5),
```

and hence

```text
rho_n^- = 4n^2+9n+19/4+O(n^-2),
q_n^-   = -8n^2+(16 pi lambda^2-10)n+O(1).
```

Now `x_1=9` and `y_1=16 pi lambda^2-10`, but the same calculation gives exactly `(1)`.
The odd block is therefore limit-circle as well.

At `lambda=0`, equality holds in the next-order critical relation:

```text
beta = 2x_1/x_0 - 2y_1/y_0 = 2.
```

Pruckner's case (iii) is limit-circle only under the strict condition `2<beta`; this fails.
Both zero-parameter blocks are therefore limit-point.

The standard half-line Jacobi alternative identifies limit-circle with deficiency indices `(1,1)`
and limit-point with `(0,0)`.  Direct sum adds deficiency indices.  This proves all claims.

## Exact critical-potential infrastructure

For four consecutive positive Jacobi radii `x_0,x_1,x_2,x_3`, define

```text
R=x_0x_1-x_1^2-x_2^2+x_2x_3.
```

The new Lean module proves the exact identity

```text
2R
 =(x_3^2-x_2^2)-(x_1^2-x_0^2)
  -(x_3-x_2)^2-(x_1-x_0)^2.                            (2)
```

If

```text
delta_n=a_(n+1)^2-a_n^2-[2(n+1)+1/2],
```

then on the quartet starting at `2k`,

```text
2R
 =4+delta_(2k+2)-delta_(2k)
  -(a_(2k+3)-a_(2k+2))^2-(a_(2k+1)-a_(2k))^2.          (3)
```

Finally, diagonal plus the two adjacent even-parity off-diagonals is exactly the grading term plus
`R`.  Equations `(2)`--`(3)` isolate the source datum which must replace the explicit
archimedean power expansion in the semilocal problem.

## Route consequence

- `[CLOSED]` The archimedean transported control is not merely subject to an unresolved
  `(0,0)`/`(1,1)` alternative.  For every positive prolate parameter it has one boundary angle on
  each parity block.
- `[CLOSED]` Essential self-adjointness cannot be imported from the archimedean control.
- `[SHARP TRANSITION]` The grading term moves the double-root Jacobi matrix from limit-point at
  `lambda=0` to limit-circle for every `lambda>0`.
- `[OPEN SEMILOCAL CORE]` Coarse `rho_n asymp n^2` bounds do not determine the semilocal
  alternative.  By `(3)`, the hard input is the high-degree behavior of the metaplectic anomaly
  second difference and the two adjacent Jacobi-radius increment energies.

## Novelty audit

Pruckner's exceptional Jacobi classification is established literature.  The classical prolate
differential operator is also known to have limit-circle endpoints and source-selected
self-adjoint extensions.  Applying the power-asymptotic theorem to the displayed prolate Jacobi
coefficients closes a repository gap but is not claimed as new science.

The four-point critical-potential decomposition is exact and newly formalized here, but algebraic
repackaging alone does not pass the scientific novelty gate.  Its value is that it exposes the
specific semilocal asymptotic invariant which must now be proved, instead of allowing the vague
phrase “do a sharper limit-circle analysis.”
