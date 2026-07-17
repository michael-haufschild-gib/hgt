# Von Mangoldt Hardy scaling and the free-matroid no-go

- **ID:** `von-mangoldt-hardy-scaling-free-matroid-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE / NO-GO
- **Scientific status:** `[PROVED] [REDISCOVERED PARENT THEORY] [SIGNIFICANT POSITIVE NO-GO]`
- **Lean:** `RHTower/VonMangoldtHardyGramScaling.lean`

## Theorem

Put

```text
F(z)=sum_(n>=2) Lambda(n)n^(-1-z)=-zeta'(1+z)/zeta(1+z).
```

For `Re(s)>0`, Lean proves the source scaling law

```text
t F(ts) -> 1/s                         as t->0+.
```

Hence, for every finite right-half-plane packet `w_i`, the positive von Mangoldt source Gram

```text
G_t(i,j)=t F(t(w_i+conj(w_j)))
        =t sum_n Lambda(n)/n n^(-t w_i)n^(-t conj(w_j))
```

converges entrywise to the Hardy--Cauchy Gram

```text
G_0(i,j)=1/(w_i+conj(w_j)).
```

The same source gives the canonical pole contact

```text
p_t(w)=2tF(t(w+1/2)) -> 2/(w+1/2),
4tF(t) -> 4.
```

If the nodes are distinct, Lean also proves that the rows of `G_0` are linearly independent,
`det(G_0)!=0`, and therefore

```text
eventually det(G_t)!=0.                (1)
```

The strictness proof is the finite Cauchy independence theorem: the poles `w_i` and nodes
`-conj(w_j)` are separately distinct and cannot meet because their real parts have opposite sign.
Determinant continuity then gives `(1)`.

## Exact matroid consequence

Apply `(1)` to every subset of one fixed finite packet.  There are only finitely many subsets, so
one scale threshold works for all of them.  Below that threshold every subset is independent.
Thus the ordinary represented matroid of the scaled positive source packet stabilizes to the free
matroid.

This is the sharp positive no-go for the retired matroid route: the source boundary limit does not
encode the Xi divisor as a dependence pattern.  Any RH-bearing successor must retain additional
pointed charged data, namely the boundary contact and its completed source transport.  A family or
meta-family of ordinary matroids erases exactly that datum.

## Novelty gate

The analytic scaling is not new scientific knowledge.  Olsen's 2011 theory of local properties of
weighted Hilbert spaces of Dirichlet series explicitly treats the von Mangoldt weight and proves
that its local boundary behavior is Hardy-space behavior.  General Dirichlet-series RKHS theory
already contains the kernel, and the contact column is the ordinary reproducing-kernel evaluation
vector at `1/2`.  The local Laurent expansion of `-zeta'/zeta` is stronger than the finite entrywise
limit used here.

Primary parents:

- Jan-Fredrik Olsen, *Local properties of Hilbert spaces of Dirichlet series*, JFA 261 (2011),
  arXiv:1011.3370;
- McCarthy--Shalit, *Spaces of Dirichlet series with the complete Pick property*, Israel J. Math.
  220 (2017), arXiv:1507.04162;
- Olsen--Saksman, *On the boundary behaviour of the Hardy spaces of Dirichlet series and a frame
  bound estimate*, Crelle 663 (2012), arXiv:0907.2708.

The corpus value is nevertheless significant.  The result constructs the metric endpoint and its
four-unit pole contact directly from the actual von Mangoldt source, while proving that the
dependency-only shadow becomes trivial.

## What it does not prove

The limiting pole column

```text
p_P(i)=2/(w_i+1/2)
```

is not the continued Xi Ward column `r_P`.  Safe positive source covariance produces the Euler
pole and contains no nontrivial-zero information.  The open theorem is still a source-defined,
nonexpansive charged-graph transport which replaces the pole contact by the completed normal class
without changing the Hardy metric.

## Lean certificate

- `tendsto_scaled_vonMangoldtPrimeLaplaceChannelComplex`
- `tendsto_scaledVonMangoldtEulerContactResponse`
- `tendsto_scaledVonMangoldtEulerContactNormSq`
- `scaledVonMangoldtPrimeRightHalfPlaneGram_posSemidef`
- `tendsto_scaledVonMangoldtPrimeRightHalfPlaneGram`
- `cauchyRightHalfPlaneGram_rows_linearIndependent`
- `det_cauchyRightHalfPlaneGram_ne_zero`
- `eventually_det_scaledVonMangoldtPrimeRightHalfPlaneGram_ne_zero`

The exact leaf module builds unconditionally.  No numerical computation is used.

## Gates

- [x] source scaling and contact proved
- [x] finite positive Gram convergence proved
- [x] distinct-packet full-rank limit proved
- [x] eventual free-matroid consequence extracted
- [x] corpus overlap audited
- [x] primary-literature novelty gate failed honestly
- [ ] construct the source-calibrated contact-to-divisor transport
