# Von Mangoldt successor Dirac--Krein edge realization

- **ID:** `von-mangoldt-successor-dirac-krein-edge-realization`
- **Stage:** 3-formalized
- **Type:** FORMAL CLOSURE / KNOWN SUCCESSOR-CURRENT REALIZATION
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Parents:** `SR-38`, `SR-40`, `SR-42`.

## Classification

`SR-40` constructs the cofinal signed jet kernel

```text
R(i,j)=sum_(n>=2) Lambda(n)/n
  * (log(n+1)^(i+j+2)-log(n)^(i+j+2)).
```

`SR-42` proves its finite sections have unbounded negative index. The realization below exposes
the already known successor differences as an edge integral. It is a useful carrier model but
does not alter either theorem.

## Theorem

For `t>0`, define the first-order jet column

```text
Phi_i(t)=((i+1)t^i,t^(i+1))
```

and give `R^2` the exchange form

```text
[(a,b),(c,d)]_J=a*d+b*c,
J=[[0,1],[1,0]].
```

Then every successor edge has the exact Dirac--Stokes identity

```text
log(n+1)^(i+j+2)-log(n)^(i+j+2)
  =integral_[log n,log(n+1)] [Phi_i(t),Phi_j(t)]_J dt.   (1)
```

Let

```text
X=disjoint union_(n>=2) [log n,log(n+1)],
dmu(n,t)=Lambda(n)/n dt.
```

The lifted columns `Phi_i(n,t)=Phi_i(t)` lie in the Hilbert majorant
`L2(X,dmu;R^2)` for every `i`. Their Krein Gram should equal `R`:

```text
[Phi_i,Phi_j]_(L2(J))=R(i,j).                            (2)
```

Finite apertures are literal restriction to first edge components, and aperture inclusion is zero
extension.

## Why this does not change `SR-41`

The carrier retains source-edge label while evaluating the already proved scalar difference:

```text
source edge n  x  continuous logarithmic edge coordinate t.
```

But the factorization is only product rule plus fundamental theorem of calculus. Lean makes the
non-novelty exact:

```text
finiteVonMangoldtSuccessorDiracKreinGram
  = finiteVonMangoldtSuccessorPrincipalRelativeMatrix,

vonMangoldtSuccessorDiracKreinGram
  = vonMangoldtSuccessorPrincipalRelativeKernel.
```

Thus no new source coupling has been proved. `SR-38` absolute odd-Jacobi coordinate and completed
Euler cyclic reader remain absent. The result is infrastructure, not a paper theorem.

## Falsifiers

- some lifted jet column fails Hilbert-majorant square summability;
- the exchange pairing fails to reproduce a successor difference;
- aperture restriction is not isometric zero extension;
- the construction contracts the source edge before the pairing;
- the `SR-38` coherent residual cannot be represented on any common refinement of the edge and
  absolute Jacobi coordinates.

## Gates

- [x] universal edge identity
- [x] square summability of every lifted jet
- [x] finite and cofinal Gram identities
- [x] aperture increment identity
- [x] corpus collision audit
- [x] classified as formal closure, not novelty
- [x] dependency-closed Lean formalization
- [ ] common-coordinate coupling with `SR-38`
- [ ] completed Euler cyclic reader
