# Route E approximate-transpose divergence law

- **ID:** `ROUTE-E-APPROXIMATE-TRANSPOSE-DIVERGENCE-001`
- **Stage:** 3-formalized
- **Type:** `[LEAN-CERTIFIED] [EXACT FINITE DECOMPOSITION] [LOAD-GRADIENT INTERFACE]`
- **Parent:** `route-e-right-to-left-short-window-transfer.md`,
  `route-e-two-sided-column-load-gradient-pairswitch-law.md`
- **RH used:** no
- **Computation used:** no
- **Lean:** `formal/GaloisForLFunctions/RHTower/RouteEApproximateTransposeDivergence.lean`

## Exact theorem

Let `P,Q` be finite real kernels with every row sum equal to one. Define their equal mixture and
their failure to be mutual transposes by

\[
 R_{ij}={P_{ij}+Q_{ij}\over2},\qquad D_{ij}=Q_{ij}-P_{ji}.
\tag{1}
\]

Write

\[
 \ell_R(i)=\sum_jR_{ji},\qquad
 \operatorname{div}D(i)=\sum_jD_{ij}-\sum_jD_{ji}.
\tag{2}
\]

Then

\[
 \boxed{1-\ell_R(i)={1\over2}\operatorname{div}D(i).}
\tag{3}
\]

Indeed, row completeness gives

\[
 \sum_jD_{ij}=1-\ell_P(i),\qquad
 \sum_jD_{ji}=\ell_Q(i)-1,
\]

and subtraction gives `(3)`. Consequently

\[
 \ell_R(i)-\ell_R(j)
 ={1\over2}\bigl(\operatorname{div}D(j)-\operatorname{div}D(i)\bigr).
\tag{4}
\]

For every finite edge set `E` and every real reporter weight `w`, with no sign or positivity
assumption on `w`, Lean proves the exact energy identity

\[
 \boxed{
 \sum_{(i,j)\in E}w_{ij}(\ell_R(i)-\ell_R(j))^2
 ={1\over4}\sum_{(i,j)\in E}w_{ij}
   (\operatorname{div}D(i)-\operatorname{div}D(j))^2.}
\tag{5}
\]

The same decomposition gives the auxiliary absolute estimate

\[
 \sum_i|1-\ell_R(i)|\le\sum_{i,j}|D_{ij}|.
\tag{6}
\]

## Exact-transpose boundary

If `Q=Pᵀ` and every row of `Q` sums to one, then every column of `P` already sums to one. Hence
declaring the shifted-downward kernel to be the exact transpose of the upward kernel cannot create
column balance: it assumes it. A useful construction must expose and estimate a nonzero arithmetic
mismatch `D`.

## Route E consequence

The right-to-left window transfer supplies complete rows in both numerical directions. Equation
`(5)` identifies the remaining non-circular producer for their mixture: do not estimate total
column defect, which retains the original signed sum; instead prove that the divergence of the
up/down transpose mismatch varies slowly along the actual strict-half physical edges.

For the product-truncated entropy-complement relation, `D` must be decomposed into source-visible
pieces:

1. shifted terminal-window discrepancy;
2. row-normalizer discrepancy;
3. product-cutoff loss;
4. zero/one-large-prime seam discrepancy;
5. physical collisions under projection from labelled histories.

Only the edge-gradient energy of the combined divergence is required. Its value may have an
order-one hydrodynamic profile; equation `(5)` does not require `D` or the column defect to have
small total mass.

## What remains open

No arithmetic estimate for the mismatch-divergence gradient is proved here. In particular, this
module does not construct the prime-factor kernel, prove its physical injectivity, control its
cutoff seams, establish the `X^{o(1)}` energy bound, bound Mertens sums, or prove RH.

## Verification

Direct foreground check passed:

```text
lake env lean GaloisForLFunctions/RHTower/RouteEApproximateTransposeDivergence.lean
```

Module is wired into `formal/GaloisForLFunctions/RHTower.lean`. Targeted build and axiom audit are
recorded after final audit.
