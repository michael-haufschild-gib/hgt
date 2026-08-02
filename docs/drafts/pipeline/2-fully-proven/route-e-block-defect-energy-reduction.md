# Route E block-defect energy reduction

- **ID:** `ROUTE-E-BLOCK-DEFECT-ENERGY-001`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper and Lean) / SOURCE-INVARIANT REDUCTION
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** dependency-closed finite theorems formalized in
  `MobiusBlockDefectCompression.lean` and `MobiusBlockDefectEnergy.lean`

## Statement

Let \(B_j\) be consecutive integer blocks, let \(\xi_j=\min B_j\), and suppose
\[
0\le n-\xi_j\le h\qquad(n\in B_j).
\]
For arbitrary complex coefficients \(|a_n|\le1\), define the block defect
\[
d_j=\sum_{n\in B_j}a_n.
\]
Then, for every \(x\ge0\),
\[
\left|
\sum_n a_ne^{-xn}-\sum_jd_je^{-x\xi_j}
\right|
\le
xh\sum_n e^{-x\xi_{j(n)}}.                              \tag{1}
\]
The representative sum is an exact fiber regrouping, not an approximation.

For a finite real defect sequence \(d_0,\ldots,d_N\), put
\[
D_j=\sum_{i=0}^j d_i.
\]
Every real weight sequence satisfies the exact Abel identity
\[
\sum_{j=0}^N d_jw_j
=D_Nw_N+\sum_{j=0}^{N-1}D_j(w_j-w_{j+1}),               \tag{2}
\]
and hence
\[
\left|\sum_{j=0}^N d_jw_j\right|
\le |D_N||w_N|
+\left(\sum_{j<N}D_j^2\right)^{1/2}
 \left(\sum_{j<N}(w_j-w_{j+1})^2\right)^{1/2}.           \tag{3}
\]
If \(w_j=e^{-x\xi_j}\), \(\xi_j\le\xi_{j+1}\), and
\(\xi_{j+1}-\xi_j\le h\), then
\[
\sum_{j<N}(w_j-w_{j+1})^2
\le (xh)^2\sum_{j<N}e^{-2x\xi_j}.                        \tag{4}
\]

If the finite sequence is an extended sector current with
\(\sum_{j=0}^Nd_j=0\), then `(2)` has no endpoint:
\[
\sum_{j=0}^Nd_jw_j
=\sum_{j<N}J_j(w_j-w_{j+1}),\qquad
J_j=\sum_{i\le j}d_i.                                   \tag{4a}
\]
Thus the moving-cutoff flux \(J_j\) is literally the cumulative-defect coordinate paired by
Abel summation, and the same quadratic energy bound applies sectorwise.

## Proof

For \(r\le n\le r+h\), write \(d=n-r\).  Monotonicity of the exponential and
\(1-e^{-xd}\le xd\) give
\[
|e^{-xn}-e^{-xr}|
=e^{-xr}(1-e^{-xd})
\le xhe^{-xr}.
\]
Multiply by \(a_n\), use \(|a_n|\le1\), sum, and apply the triangle inequality.  Regrouping the
representative sum over the fibers of \(n\mapsto j(n)\) gives `(1)`.

Identity `(2)` follows by induction on \(N\).  The induction step adds \(d_{N+1}w_{N+1}\) and
uses
\[
D_Nw_N+d_{N+1}w_{N+1}
=(D_N+d_{N+1})w_{N+1}+D_N(w_N-w_{N+1}).
\]
Apply the triangle inequality and finite Cauchy--Schwarz to obtain `(3)`.  Applying the
pointwise exponential estimate above to consecutive representatives and squaring gives `(4)`.

All steps are formalized unconditionally.

Lean theorems
`sum_range_mul_eq_sum_prefix_mul_sub_of_total_eq_zero` and
`abs_exp_zeroTotalSectorFluxCurrent_le_prefixEnergy` prove `(4a)` and its Gibbs-gradient bound.

## Critical Route E scaling

On a dyadic shell \([U,2U]\), take \(x\asymp U^{-1}\), block width \(h\), and
\(\asymp U/h\) blocks.  Equation `(1)` costs \(O(h)\).  Equation `(4)` gives
\[
\sum_{j<N}(w_j-w_{j+1})^2\ll\frac hU.                   \tag{5}
\]
Thus the random-walk-scale cumulative-defect law
\[
\sum_{\xi_j\in[U,2U]}M(\xi_j)^2
\le \frac{U^{2+o(1)}}h                                  \tag{6}
\]
forces an \(U^{1/2+o(1)}\) contribution after global Abel summation.  Here
\(M(y)=\sum_{n\le y}\mu(n)\); using global cumulative defects removes artificial dyadic endpoint
terms because \(M(y)e^{-xy}\to0\) unconditionally as \(y\to\infty\).

The critical choice \(h=U^{1/2+o(1)}\) makes `(1)` admissible and turns `(6)` into
\[
\sum_{\xi_j\in[U,2U]}M(\xi_j)^2\le U^{3/2+o(1)}.         \tag{7}
\]
There are only \(U^{1/2+o(1)}\) sampled endpoints. Consequently `(7)` allows individual sampled
values as large as \(U^{3/4+o(1)}\) only when the samples are treated as an arbitrary array.
That conclusion is false for the actual Mertens function because
\(|M(n+1)-M(n)|\le1\). A spike of height \(A\) persists over \(\gg A/h\) mesh points and costs
\(\gg A^3/h\), giving the sharper consequence \(A\le U^{2/3+o(1)}\). Moreover,
bounded-increment interpolation across each block gives
\[
\sum_{U<n\le2U}M(n)^2
\le 2h\sum_jM(\xi_j)^2+O(Uh^2)
\le U^{2+o(1)}
\]
at \(h\le U^{1/2+o(1)}\). Thus `(7)` belongs to the classical all-\(\varepsilon\) Mertens
mean-square RH-criterion family; it is a useful exact Gibbs reduction, not an independently weaker
arithmetic producer. Full correction and proof:
`../3-formalized/not_new_scientific_knowledge/route-e-mesh-energy-classical-mean-square-bridge.md`.

## Hostile audit

- `(1)` proves that the ordinary defect current is exactly the original source at critical
  precision; it does not create cancellation.
- Small individual increments \(d_j\), their one-block mean square, and a power-saving set of bad
  blocks do not imply `(6)`.  They control high-frequency increment energy, while `(6)` controls
  the accumulated low-frequency mode.
- A two-phase sequence with positive defects on the first half and negative defects on the second
  has zero endpoint defect and small individual defects but violates the required cumulative
  energy by a macroscopic factor.  Lean theorem
  `twoPhase_geometricCurrent_transfer` proves its exact denominator-free transfer law
  \[
  S_m(r)(1-r)=A(1-r^m)^2.
  \]
  For \(A=\delta h\), \(r=e^{-xh}\), \(m\asymp U/h\), and \(x\asymp U^{-1}\), this is
  \(S_m(r)\asymp\delta U\).
- The continuous analogue of `(6)` is an \(L^2\)-Mertens criterion. The bounded-increment
  interpolation above places the mesh criterion inside that classical RH-equivalent mean-square
  family. No source novelty is claimed. The surviving project contribution is the exact Gibbs
  compression and rigorous separation from published almost-all increment laws.
- For a rectangle sector, static marginal conservation supplies exactly the zero-total hypothesis
  in `(4a)`.  The analytic co-moving-flux obligation is therefore a sectorwise prefix-energy law;
  arithmetic coverage and local Hall capacity remain separate and are not implied by `(4a)`.

## Status

`[PROVED HERE; LEAN-CERTIFIED SOURCE REDUCTION]`.

This closes the representation question for ordinary windows: the surviving hard input is
cumulative Möbius defect energy, not local opposite-sign capacity.  It does not prove `(6)`, so
Route E remains open.
