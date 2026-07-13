# Hilbert closure makes the finite zeta summation constraint maximally multivalued

- **ID:** `zeta-summation-constraint-graph-dense-collapse`
- **Stage:** 2-fully-proven / Lean orthogonality core verified
- **Type:** THEOREM / NON-FOCK CONSTRAINT ROUTE GATE
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `dirichlet-diagonal-hilbert-rigging-abscissa-barrier`; separate from RHTower Routes A--D
- **Lean core:** `formal/GaloisForLFunctions/RHTower/DirichletHilbertRiggingBarrier.lean`

## Statement

Let `D=c_00(N)` be the finite coefficient sequences inside `ell^2(N)` and let

```text
S(x)=sum_n x_n,   x in D.                              (1)
```

Then the graph of `S` is dense in `ell^2(N) direct_sum C`. Consequently:

1. `S` is not closable;
2. its graph closure is the maximal linear relation `ell^2 direct_sum C`, not the graph of an
   operator; and
3. Hilbert closure of the finite Dirichlet summation rule assigns **every** scalar value to every
   coefficient vector.

Therefore analytic continuation of zeta cannot be obtained by closing the finite summation
constraint in coefficient Hilbert space. A separate non-Hilbert renormalisation law is logically
mandatory.

## Proof by orthogonal complement

Let

```text
G={(x,Sx): x in c_00} subset ell^2 direct_sum C.
```

Suppose `(y,c)` is orthogonal to `G`. For every standard basis vector `e_n`,

```text
(e_n,1) in G,
```

so orthogonality gives

```text
<y,e_n> + conjugate(c) = 0                           (2)
```

up to the fixed inner-product convention. Thus every coordinate of `y` is the same constant.
The only constant sequence in `ell^2` is zero, hence `c=0` and `y=0`. Therefore

```text
G^perp={0},
closure(G)=ell^2 direct_sum C.                        (3)
```

This proves the theorem.

An explicit nonclosability witness is

```text
x^(N)=(1/N,...,1/N,0,0,...),
```

with `N` nonzero entries. Then

```text
||x^(N)||_2=N^(-1/2) -> 0,
S(x^(N))=1.                                           (4)
```

Lean proves the reusable orthogonality ingredient in greater generality. For any Bessel family
`{u_n}`, a constant response `<u_n,y>=c` forces `c=0`
(`bessel_constant_response_eq_zero`). Applied to the canonical orthonormal basis, this is the
nonzero-constant exclusion used in `(2)`--`(3)`.

## Meaning for a Wheeler--DeWitt constraint

One might try to evade the absence of a normal summation vector by adjoining a scalar coordinate:

```text
Z_s = ((n^(-s))_n, z_s) in ell^2 direct_sum C,
```

and declaring the second coordinate to be the renormalised amplitude. But `(3)` shows that Hilbert
closure of the finite source does not determine `z_s`: every choice is compatible with the closed
relation. Choosing `z_s=zeta(s)` is therefore an added constraint, not a consequence of the
coefficient superposition.

This is the exact constraint-side analogue of the earlier metric blindness:

```text
finite coefficient rule --Hilbert closure--> no scalar information.
```

A Wheeler--DeWitt equation built only by closing the finite summation graph is vacuous in its scalar
sector.

## Surviving possibilities

The obstruction leaves three genuinely different mechanisms:

1. impose a stronger nuclear/analytic topology before taking the graph closure;
2. specify a singular finite-part functional using the completed Euler--Gamma source; or
3. encode the amplitude as a cohomology/quotient class rather than a graph coordinate.

Each mechanism must prove that its selected scalar value is canonical and phase-sensitive. Merely
adjoining `zeta(s)` as a coordinate is circular.

## Novelty verdict

Dense graphs of nonclosable summation functionals are standard functional analysis. The exact
application is a useful and rigorous quantum-constraint no-go, but not new scientific knowledge.
