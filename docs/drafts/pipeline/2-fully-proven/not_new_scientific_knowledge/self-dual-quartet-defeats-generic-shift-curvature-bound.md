# A self-dual quartet defeats every generic shifted-curvature bound

- **ID:** `self-dual-quartet-defeats-generic-shift-curvature-bound`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** COUNTEREXAMPLE THEOREM (paper),
  `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `shifted-euler-quotient-twisted-cocycle-flatness.md`;
  `infinitesimal-euler-leakage-cauchy-energy-threshold.md`
- **Statement:** Functional equation, Schwarz symmetry, critical-strip geometry, boundary
  unimodularity, the exact full-shift cocycle, and Toeplitz contractivity do not imply any uniform
  bound on the infinitesimal leakage-curvature corner.  A degree-four self-dual polynomial family
  satisfies all these generic structures while its corner energy is arbitrarily large.

## Counterexample family

Fix

```text
0<a<1/2,       gamma>0,
```

and put `z=s-1/2`.  Define

```text
F_(a,gamma)(s)
 =((z-a)^2+gamma^2)((z+a)^2+gamma^2).                    (1)
```

Its zeros are

```text
1/2+a+i gamma,   1/2+a-i gamma,
1/2-a+i gamma,   1/2-a-i gamma.                         (2)
```

All lie in `0<Re s<1`.

## Theorem A: all generic completed-source symmetries hold

The polynomial `(1)` satisfies

```text
F_(a,gamma)(1-s)=F_(a,gamma)(s),
F_(a,gamma)(conjugate s)=conjugate(F_(a,gamma)(s)).       (3)
```

For real `omega>0`, define

```text
R_omega(s)=F_(a,gamma)(s-omega)/F_(a,gamma)(s+omega).
```

On the critical boundary `Re s=1/2`,

```text
|R_omega(s)|=1                                           (4)
```

away from its finitely many zeros and poles.  It also obeys the exact full-shift cocycle

```text
R_(omega+eta)(s)=R_omega(s-eta)R_eta(s+omega).            (5)
```

Consequently boundary multiplication is unitary and its causal Toeplitz compression is a
contraction for every `omega`.

### Proof

The polynomial in `z` is even and has real coefficients, proving `(3)`.  If `Re s=1/2`, then

```text
s-omega=1-conjugate(s+omega).
```

Use both identities in `(3)` to get

```text
F(s-omega)=conjugate(F(s+omega)),
```

which proves `(4)`.  Equation `(5)` is the telescoping quotient identity.  A unimodular boundary
multiplier is unitary on `L^2`; compression by an orthogonal projection is contractive.

## Theorem B: the curvature corner is unbounded

The right-half divisor consists of the two simple zeros at ordinates `gamma` and `-gamma`, both at
displacement `a`.  Its normalized anti-causal profile is

```text
ell_(a,gamma)(t)
 =2exp(-(a+i gamma)t)+2exp(-(a-i gamma)t)
 =4exp(-at)cos(gamma t).                                (6)
```

Therefore the Toeplitz-curvature corner is

```text
C_(a,gamma)(0,0)
 =integral_0^infinity |ell_(a,gamma)(t)|^2 dt
 =4/a+4a/(a^2+gamma^2).                                 (7)
```

In particular,

```text
C_(a,gamma)(0,0)>8,
lim_(a->0+) C_(a,gamma)(0,0)=infinity.                   (8)
```

### Proof

Equation `(6)` is the universal first-order residue profile with multiplicity one.  Using

```text
cos^2(gamma t)=(1+cos(2gamma t))/2
```

gives

```text
16 integral_0^infinity exp(-2at)cos^2(gamma t)dt
 =8(1/(2a)+(2a)/((2a)^2+(2gamma)^2)),
```

which is `(7)`.  Since `a<1/2`, its first term is greater than `8`, proving `(8)`.

## Route C consequence

No theorem using only the following generic data can prove the required corner bound `<=4`:

1. entire or Cartwright-type finite-order completion;
2. `F(1-s)=F(s)` and Schwarz symmetry;
3. all nontrivial zeros lying in the open critical strip;
4. unimodularity of the centered shifted quotient;
5. the exact full-shift cocycle; or
6. contractivity and positivity of the associated Toeplitz Schur defect.

The family `(1)` satisfies all six and violates the bound by an arbitrarily large amount.  Any live
Route C proof must therefore use a property absent from `(1)`: the exact infinite Euler product,
the explicit gamma/theta completion, and a quantitative law coupling them at the compressed
boundary.  Generic self-dual entire-function or operator theory is fully excluded as the source of
the bound.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The counterexample is an elementary symmetric polynomial quartet,
and the energy is a two-exponential integral.  It is decisive route control but not a new theorem
in entire-function or operator theory.

## Gates

- [x] 0 -> 1: generic compressed-cocycle premise and smallest falsifier isolated.
- [x] 1 -> 2: symmetries, strip geometry, unimodularity, cocycle, contractivity, and unbounded
  curvature proved on paper.
- [ ] 2 -> 3: no Lean formalization selected; a polynomial wrapper would not address the open
  Euler--Gamma boundary estimate.
- [ ] 3 -> 4: no scientific-novelty claim.
