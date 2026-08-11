# Prime-exponent source edge, refinement energy, and criticality law

- **ID:** ULF-SFHM-2
- **Stage:** 3-formalized
- **Type:** THEOREM / LITERAL SOURCE FUSION AND EXACT CONSERVATION
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [DEPENDENCY-CLOSED] [UNCONDITIONAL]`
  `[ARITHMETIC-INCIDENCE-PHASE-CAPACITY FUSION] [NOT RH]`

## 1. Arithmetic source edges

Fix a prime `p`.  For `m>=1`, define the prime-exponent profile

\[
 A_m(e)=(m\operatorname{Part}_m\mu)(p^e),\qquad e\in\mathbb N.
 \tag{SE.1}
\]

The established power-dilation formula for Möbius coefficients gives

\[
 \boxed{A_m=\delta_0-\delta_m.}
 \tag{SE.2}
\]

Therefore the normalized successor channel is

\[
 \boxed{A_{m+1}-A_m=\delta_m-\delta_{m+1}.}
 \tag{SE.3}
\]

For a base `K>=1`, the complete normalized source restricts to the head edge
`delta_0-delta_K` and the tail edges

\[
 e_{K,j}=\delta_{K+j}-\delta_{K+j+1},\qquad j\ge0.
 \tag{SE.4}
\]

### Theorem 1.1 — source subdivision and boundary conservation

For every `r>=1` and `q>=0`,

\[
 \boxed{
 \sum_{k=0}^{r-1}e_{K,rq+k}
 =\delta_{K+rq}-\delta_{K+r(q+1)}.}
 \tag{SE.5}
\]

If `K=rK_0`, and `P_r(delta_e)=delta_(re)`, then

\[
 \boxed{
 \sum_{k=0}^{r-1}e_{rK_0,rq+k}=P_r(e_{K_0,q}).}
 \tag{SE.6}
\]

The head obeys the same law: `delta_0-delta_(rK_0)=P_r(delta_0-delta_(K_0))`.

### Proof

Equation `(SE.2)` is the prime-power formula
`mPart_m(mu)(p^e)=1` for `e=0`, `-1` for `e=m`, and zero otherwise.  Subtracting adjacent values
proves `(SE.3)`.  In `(SE.5)` every interior point mass occurs once with each sign and cancels.
Substitution `K=rK_0` proves `(SE.6)`. QED.

This is not a graph imposed on a route.  It is the coefficient restriction of the actual
normalized arithmetic source.  Taking Dirichlet series turns power pushforward into argument
dilation and `(SE.6)` into the block identity `C_r h_(rK)(s)=h_K(rs)`.

## 2. Joint reconstruction from oriented responses

Let `V` be a real inner-product space and let `u_0,...,u_r in V`.  Define the oriented responses

\[
 d_k=u_{k+1}-u_k\qquad(0\le k<r).
 \tag{SE.7}
\]

### Theorem 2.1 — anchor plus differential reconstructs history

The data `(u_0,d_0,...,d_(r-1))` reconstructs the full vertex history:

\[
 \boxed{u_j=u_0+\sum_{k=0}^{j-1}d_k.}
 \tag{SE.8}
\]

The coarse boundary response is conserved:

\[
 \boxed{u_r-u_0=\sum_{k=0}^{r-1}d_k.}
 \tag{SE.9}
\]

### Proof

Both identities telescope. QED.

Thus the incidence/source organ and the oriented phase/history organ are jointly faithful up to
one unavoidable additive gauge.

## 3. Positive capacity and exact refinement conservation

Put

\[
 \bar d={u_r-u_0\over r}={1\over r}\sum_{k=0}^{r-1}d_k.
 \tag{SE.10}
\]

### Theorem 3.1 — harmonic/cofluctuation Pythagoras

For every `r>=1`,

\[
 \boxed{
 \sum_{k=0}^{r-1}\|d_k\|^2
 ={\|u_r-u_0\|^2\over r}
 +\sum_{k=0}^{r-1}\|d_k-\bar d\|^2.}
 \tag{SE.11}
\]

Equivalently,

\[
 \boxed{
 r\sum_k\|d_k\|^2-\left\|\sum_kd_k\right\|^2
 =\sum_{k<l}\|d_k-d_l\|^2.}
 \tag{SE.12}
\]

The refinement excess is nonnegative and vanishes exactly when all `d_k` are equal, equivalently
when

\[
 u_j=(1-j/r)u_0+(j/r)u_r.
 \tag{SE.13}
\]

Hence the coarse term in `(SE.11)` is the minimum fine energy among all histories with the same
endpoints, and the minimizer is unique.

### Proof

Write `d_k=(d_k-bar d)+bar d`.  The cross term in the sum of squared norms is

\[
 2\left\langle\sum_k(d_k-\bar d),\bar d\right\rangle=0.
\]

Also `r||bar d||^2=||u_r-u_0||^2/r`, proving `(SE.11)`.  Expanding the right side of `(SE.12)`
gives `r sum||d_k||^2-||sum d_k||^2`.  Equality in `(SE.11)` is equivalent to every
`d_k=bar d`, which telescopes to `(SE.13)`. QED.

This fuses a third organ: positive energy/capacity is not an independent scalar.  It is the
orthogonal quotient of the same source differential by the coarse boundary response.

## 4. Fourth-organ prediction: spectral criticality of radial characters

Fix `p>1`, `nu in R`, and put

\[
 u_j=p^{\nu j}.
 \tag{SE.14}
\]

For `r>=2`, its consecutive drops are

\[
 d_k=p^{\nu k}(p^\nu-1).
 \tag{SE.15}
\]

### Theorem 4.1 — exact critical refinement detector

The following are equivalent:

1. the refinement excess in `(SE.11)` is zero;
2. the radial history is harmonic at every interior vertex;
3. its discrete Laplacian vanishes at one interior vertex;
4. `nu=0`.

Indeed,

\[
 \boxed{
 u_{j-1}-2u_j+u_{j+1}
 =p^{\nu(j-1)}(p^\nu-1)^2.}
 \tag{SE.16}
\]

Thus the Laplacian is nonnegative and is strictly positive off `nu=0`.  Moreover the oriented
first edge has sign

\[
 \operatorname{sgn}(u_1-u_0)=\operatorname{sgn}(\nu).
 \tag{SE.17}
\]

### Proof

For `r>=2`, zero excess forces `d_0=d_1`.  By `(SE.15)`, either `p^nu-1=0` or `p^nu=1`; both give
`p^nu=1`.  Since `p>1`, injectivity of the real exponential gives `nu=0`.  The converse is
immediate.  Expanding `(SE.16)` proves the Laplacian formula.  Monotonicity of `p^nu` proves
`(SE.17)`. QED.

For a divisor parameter `rho`, set `nu=2 Re(rho)-1`.  The exact source-refinement energy then
vanishes precisely on the critical line.  This is a selection **receiver**, derived only after the
three-organ fusion and conservation theorem.

## 5. Why this does not prove RH

Nothing proved here says that a Xi zero must define a refinement-harmonic radial potential.  The
remaining theorem would have to show, before Xi specialization, that the physical radial
deformation descends through the source-generated edge-subdivision system and that the descended
energy is nonerased.  Postulating that descent would insert the critical-line conclusion as a
constitutive axiom.

The exact gain is narrower and unconditional:

1. the normalized arithmetic source canonically generates the exponent-ray complex;
2. source subdivision, oriented response, and positive capacity obey one conservation law;
3. the fourth spectral organ is predicted and detects the critical parameter without a fitted
   matrix, route endpoint, or chosen zero;
4. the missing RH statement is now a typed **harmonic-descent** theorem, not another request for a
   mysterious source object.

## 6. Hostile audit

1. The Pythagorean and resistance laws are classical discrete potential theory.
2. The source-specific contribution is `(SE.2)`--`(SE.6)`: the actual normalized Möbius formation
   realizes the refinement complex coefficientwise.
3. Squared energy forgets the orientation in `(SE.17)`; phase/sign remains lift data.
4. Finite refinement gives no cofinal coercivity.  On longer paths the first nonzero Laplacian
   eigenvalue tends to zero, so a uniform global selection theorem needs an additional source
   boundary or weighted conductance law.
5. No RH, zero-free, or source-normality claim is made.

## Lean certification

`GaloisForLFunctions.HTGeometry.SourceFormationHarmonicMechanics` certifies the significant finite
core: literal Möbius prime-exponent edges, block boundary conservation, marked reconstruction,
finite refinement-energy Pythagoras, two-edge discrete-Laplacian energy, and prime-radial
criticality.  The companion source-edge polar theorem in the same module adds character
reconstruction and recurrent coherent closure with open positive history.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
