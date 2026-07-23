# Von Mangoldt successor principal-relative Hankel current

- **ID:** `von-mangoldt-successor-principal-relative-hankel-current`
- **Stage:** 3-formalized / external novelty audit pending
- **Parent:** `SR-40`; `von-mangoldt-successor-bianchi-hankel-curvature-weld.md`.
- **Type:** `[SIGNED PRINCIPAL-RELATIVE COMPLETION]`, `[SOURCE HANKEL CURRENT]`.
- **Scientific status:** `[PROVED] [LEAN-VERIFIED DIRECTLY] [NOT RH]`.
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/VonMangoldtSuccessorPrincipalRelativeHankel.lean`.

## 1. Frontier

Finite pointed weld proved

```text
Head_M = Successor_M + Tail_M + Cross_M.               (1)
```

but both endpoint Grams diverge cofinally. Open `SR-40` question was whether source-fixed
principal subtraction preserves forced mixed block or destroys it in limit. Define

```text
rho_q = sum_(n>=2) Lambda(n)/n
  *((log(n+1))^q-(log n)^q).                           (2)
```

This is not a fitted target sequence: it is forced by subtracting actual pointed Bianchi tail
from actual successor head on same von Mangoldt coordinate.

## 2. Absolute source law

For every `q` and `n>=2`, Lean proves

```text
|Lambda(n)/n * (log(n+1)^q-log(n)^q)|
 <= 4*q*|log(n+1)|^q*(n+1)^(-2).                      (3)
```

Consequently every `rho_q` is absolutely summable. No regularization choice, target moment, Xi
character, or RH assumption enters `(3)`.

## 3. Exact finite principal-relative identity

Let `W_M`, `B_M`, `S_M`, and `X_M` denote coupled head weld, pointed Bianchi tail, successor Gram,
and forced symmetrized mixed block. Matrix equality holds at every aperture and jet size:

```text
R_M := W_M-B_M = S_M+X_M.                              (4)
```

Every entry is exact partial relative moment:

```text
(R_M)_(i,j)
 = sum_(n=2)^(M+1) Lambda(n)/n
   *((log(n+1))^(i+j+2)-(log n)^(i+j+2)).              (5)
```

Thus principal subtraction removes only divergent pointed tail; it retains mixed block exactly.

## 4. Cofinal universal Hankel law

Absolute convergence gives simultaneous convergence in every fixed finite matrix space:

```text
R_M -> R,                  R_(i,j)=rho_(i+j+2).         (6)
```

Define infinite kernel `R(r,s)=rho_(r+s+2)`. Lean proves all-order shift identity

```text
R(r+1,s)=R(r,s+1)                                    (7)
```

and its exact finite counterpart. Combining finite `(4)` with finite shift gives, at every
admissible `i,j`,

```text
X_M(i+1,j)-X_M(i,j+1)
 = -(S_M(i+1,j)-S_M(i,j+1)).                           (8)
```

So forced mixed curvature survives source principal subtraction and cancels successor anti-Hankel
curvature at every order, not merely first curvature.

## 5. Scientific-method verdict

Falsifiers were:

- some `(2)` fails absolute summability;
- head-minus-tail is not exact partial `(2)`;
- principal subtraction loses `X_M`;
- cofinal limit violates Hankel shift.

Lean refutes all four. Corpus collision search across `HTGeometry`, `RHTower`, `HilbertMetric`,
formalized/proven cards, support extraction log, and failed routes found generic summability,
moment-Hankel closure, and fixed-aperture Sonin finite parts, but no source-specific linear
successor relative current or preservation theorem `(4)`--`(8)`. Generic layers are
`FORMAL-CLOSURE`; exact von Mangoldt/Bianchi composition is `ADVANCE`. External novelty remains
provisional pending source/literature audit.

## 6. Boundary of claim

This solves matrix-entry/cofinal-Hankel part of `SR-40`. It does **not** prove current positive,
embed coherent odd Gamma--Jacobi residual, identify completed Euler multiplication/trace, produce
critical fibre orientation, or prove RH. Next source problem is a positive or Krein realization of
`R` coupled to coherent odd Gamma--Jacobi channel, with completed Euler trace fixed before any Xi
target is read.

## Gates

- [x] absolute summability of every `rho_q`
- [x] exact finite relative-moment identity
- [x] exact `Successor+Cross` principal-relative identity
- [x] finite-dimensional cofinal convergence
- [x] all-order finite and cofinal Hankel law
- [x] unconditional direct Lean verification
- [ ] final targeted build/lint/axiom audit
- [ ] external novelty audit
