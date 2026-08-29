# Theta rank-three source-positive sl2 structure

- **ID:** S6F-SL2
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Lean module:** `GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveSl2`

## Result

Let `V` be the autonomous `(U,B,Q)` source-positive theta vector field and define

```text
D = (U/2)∂U + (B/2)∂B + (Q+3/8)∂Q,
W = -3∂U + ∂B + (3B/4)∂Q,
e = V+W,  f = -W,  h = 4D.
```

Lean proves unconditionally

```text
[h,e]=2e,  [h,f]=-2f,  [e,f]=h.
```

It also proves the adapted-coordinate laws for

```text
r=U+3B,  b=B,  k=Q+3/8-3B²/8:
W(r)=0, W(b)=1, W(k)=0,
D(r)=r/2, D(b)=b/2, D(k)=k,
V(r)=2br+16k,
V(b)=b²+4k-1,
V(k)=4bk-2kr.
```

## Route consequence

S6F scale variation is controlled by a genuine finite-dimensional representation, not an
accidental determinant polynomial.  Raw coefficientwise matrix-Bernstein positivity is false, so
next exact target is a positive contravariant/Shapovalov form on the reflected-jet module or a
congruence mixing scale layers.  This sharpens but does not close native D1 positivity or the
cofinal/all-order landing.

## Audit

- `lake env lean GaloisForLFunctions/HTGeometry/PolynomialODEJetRankThreeSourcePositiveSl2.lean`
- `lake build GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveSl2`
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- Wired in `GaloisForLFunctions.HTGeometry`.
