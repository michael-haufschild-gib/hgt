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

## Row-normalized raw-incidence split

Let `U,V` be the unnormalized upward and downward physical incidences, and put

\[
 a_j=\sum_kU_{jk},\qquad b_i=\sum_kV_{ik},\qquad
 P_{ji}={U_{ji}\over a_j},\qquad Q_{ij}={V_{ij}\over b_i}.
\tag{7}
\]

Whenever all raw rows are nonzero, `P,Q` have complete rows. Their transpose mismatch has the exact
two-term decomposition

\[
 \boxed{
 Q_{ij}-P_{ji}
 ={V_{ij}-U_{ji}\over b_i}
 +U_{ji}\left({1\over b_i}-{1\over a_j}\right).}
\tag{8}
\]

First term is literal geometric mismatch between downward incidence and transposed upward
incidence. Second is local row-normalizer mismatch on shared physical edges. Lean combines `(8)`
with `(5)`, proving that mixed normalized column-gradient energy is exactly one quarter of the
divergence-gradient energy of these two raw terms.

## Symmetric-incidence reduction

After restricting to a genuinely pair-stable physical support, choose one symmetric raw incidence
`U`, so `U(i,j)=U(j,i)`, and normalize its rows. Literal geometric mismatch then vanishes exactly:

\[
  P_{ij}-P_{ji}
  =U_{ij}\left({1\over a_i}-{1\over a_j}\right),
  \qquad a_i=\sum_jU_{ij}.
\tag{9}
\]

Define reciprocal-row-mass flux

\[
  F_U(i)=\sum_jU_{ij}\left({1\over a_i}-{1\over a_j}\right).
\tag{10}
\]

The transpose-mismatch divergence is exactly `2F_U(i)`. Consequently the factor `1/4` in `(5)`
cancels, and Lean proves the exact identity

\[
  \boxed{
  \sum_{(i,j)\in E}w_{ij}(\ell_P(i)-\ell_P(j))^2
  =\sum_{(i,j)\in E}w_{ij}(F_U(i)-F_U(j))^2.}
\tag{11}
\]

Thus, once raw support is pair-stable, global Hall terminology can be replaced by one concrete
arithmetic target: control the edge-gradient energy of reciprocal local token masses. Symmetric
support alone does not make these masses constant and does not imply balance.

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

For the product-truncated entropy-complement relation, the pair-stability theorem removes bulk
decoder mismatch on the friable/friable sector. The remaining source-visible pieces are:

1. symmetric-shell boundary loss;
2. row-normalizer discrepancy;
3. zero/one-large-prime seam discrepancy;
4. physical collisions under projection from labelled histories.

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

Targeted module build passed:

```text
lake build GaloisForLFunctions.RHTower.RouteEApproximateTransposeDivergence
```

Module is wired into `formal/GaloisForLFunctions/RHTower.lean`. `#print axioms` on every public
theorem reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
