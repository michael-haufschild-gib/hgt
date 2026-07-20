# Quasi-free filling--bandwidth Fano law

- **ID:** quasi-free-filling-bandwidth-fano-law
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / UNIVERSAL HILBERT-SPACE LAW / NOVELTY GATE
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED]`
- **Novelty:** `[NOVELTY UNVERIFIED]`; no priority or general-journal claim
- **Source:** hostile finite-temperature extension of `spectral-bandwidth-slater-fano-law`
- **Statement:** The mean-minus-variance of any finite gauge-invariant quasi-free fermionic
  spectral statistic splits into a rank--filling spectral floor and three nonnegative defects.

## Goal

Replace the pure Slater/projection hypothesis by an arbitrary positive-contraction one-particle
density.  The theorem must expose the exact role of incomplete occupation, give a sharp
filling--bandwidth phase boundary, specialize to finite determinantal point processes, and retain
an unconditional finite-coordinate Lean proof.  Publication significance remains a separate gate.

## Gates

- [x] 0 -> 1 in-progress: well-posed, parent formula separated, hostile algebra audit complete
- [x] 1 -> 2 fully-proven: complete basis-independent paper proof, `[PROVED HERE]`
- [x] 2 -> 3 formalized: exact decomposition, sharpness, stability, and phase theorem compile
- [ ] 3 -> 4 publication-ready: independent expert novelty audit and compelling external use case

## Universal law `[PROVED HERE]`

Let `H` be a finite-dimensional real or complex Hilbert space, let `0 <= Gamma <= I` have support
rank `r`, and let `A=A*` have spectrum in `[a,b]`.  Choose an orthonormal eigenbasis `u_i` of the
support of `Gamma`, with positive eigenvalues `lambda_i`, and write

\[
 N=\operatorname{tr}\Gamma=\sum_i\lambda_i,\qquad
 h=a+b-1,
\]

\[
 \mu_i=\langle u_i,Au_i\rangle,\qquad
 \nu_i=\langle u_i,A^2u_i\rangle,\qquad
 C_{ij}=\langle u_i,Au_j\rangle.
\]

For the additive observable `X=dGamma(A)` in the gauge-invariant quasi-free state with one-body
density `Gamma`, the standard parent moment formula is

\[
 \mathbb EX=\sum_i\lambda_i\mu_i,\qquad
 \operatorname{Var}(X)=\sum_i\lambda_i\nu_i-
   \sum_{i,j}\lambda_i\lambda_j|C_{ij}|^2.                 \tag{1}
\]

Define

\[
 \epsilon_i=(a+b)\mu_i-ab-\nu_i
 =\langle u_i,(A-aI)(bI-A)u_i\rangle\ge0.                 \tag{2}
\]

Then the exact **filling--bandwidth three-defect identity** is

\[
\boxed{\begin{aligned}
 \mathbb EX-\operatorname{Var}(X)
 &=abN-\frac r4(a+b-1)^2
   +\mathcal E_{\rm edge}^{\Gamma}
   +\mathcal E_{\rm ctr}^{\Gamma}
   +\mathcal E_{\rm coh}^{\Gamma},\\
 \mathcal E_{\rm edge}^{\Gamma}&=\sum_i\lambda_i\epsilon_i,\\
 \mathcal E_{\rm ctr}^{\Gamma}&=\sum_i
   \left(\lambda_i\mu_i-\frac{a+b-1}{2}\right)^2,\\
 \mathcal E_{\rm coh}^{\Gamma}&=\sum_{i\ne j}
   \lambda_i\lambda_j|C_{ij}|^2.
\end{aligned}}                                             \tag{QFD}
\]

All three defects are nonnegative.  Hence

The coordinate decomposition is the expansion of a more intrinsic **two-defect Hilbert-space
identity**.  Let `P_Gamma` be the support projection of `Gamma`.  Then

\[
 \mathcal E_{\rm edge}^{\Gamma}
 =\operatorname{tr}\!\left[\Gamma(A-aI)(bI-A)\right],
\]

and cyclicity of the trace gives

\[
 \mathcal E_{\rm ctr}^{\Gamma}+\mathcal E_{\rm coh}^{\Gamma}
 =\left\|\Gamma^{1/2}A\Gamma^{1/2}
   -\frac{a+b-1}{2}P_\Gamma\right\|_{\rm HS}^{2}.
\]

Thus the basis-free master law is

\[
\boxed{\begin{aligned}
 \mathbb EX-\operatorname{Var}(X)
 &=ab\operatorname{tr}\Gamma-\frac{\operatorname{rank}\Gamma}{4}(a+b-1)^2\\
 &\quad+\operatorname{tr}\!\left[\Gamma(A-aI)(bI-A)\right]\\
 &\quad+\left\|\Gamma^{1/2}A\Gamma^{1/2}
   -\frac{a+b-1}{2}P_\Gamma\right\|_{\rm HS}^{2}.
\end{aligned}}                                               \tag{QFH}
\]

This is independent of the eigenbasis used to display (QFD).  It identifies the second defect as
the ordinary Euclidean distance, in Hilbert--Schmidt operator space, from the compressed observable
to one distinguished scalar operator.

Hence

\[
\boxed{\quad
 \mathbb EX-\operatorname{Var}(X)\ge
 ab\,\operatorname{tr}\Gamma-
 \frac{\operatorname{rank}\Gamma}{4}(a+b-1)^2.
\quad}                                                       \tag{QFB}
\]

When `a,b>0`, every such statistic is **Fano-underdispersed** (`Var X <= E X`) whenever its mean filling
`rho=tr(Gamma)/rank(Gamma)` satisfies

\[
\boxed{\quad
 \rho\ge \rho_*(a,b):=\frac{(a+b-1)^2}{4ab}.
\quad}                                                       \tag{QFT}
\]

For positive integral degrees `1,...,M`, this becomes the simple phase diagram

\[
 \boxed{\quad \rho\ge M/4.\quad}                            \tag{QFI}
\]

For `M=2,3,4`, the sharp universal filling thresholds are respectively `1/2, 3/4, 1`.
The degenerate band `M=1` is better: its exact Fano margin is `sum_i lambda_i^2`, so every filling
is underdispersed.  No filling in `[0,1]` can restore a universal law from degree five onward,
because the pure projection case already fails there.

## Dependency-closed proof `[PROVED HERE]`

Separate the diagonal term in the last sum of (1):

\[
 \mathbb EX-\operatorname{Var}(X)
 =\sum_i(\lambda_i\mu_i-\lambda_i\nu_i+\lambda_i^2\mu_i^2)
  +\sum_{i\ne j}\lambda_i\lambda_j|C_{ij}|^2.              \tag{3}
\]

The secant inequality for `x^2` on `[a,b]` gives (2).  For each occupied mode, direct completion
of the square gives the identity

\[
\begin{aligned}
 \lambda_i\mu_i-\lambda_i\nu_i+\lambda_i^2\mu_i^2
 &=\lambda_i\epsilon_i+\lambda_i ab-\lambda_i h\mu_i+\lambda_i^2\mu_i^2\\
 &=\lambda_i ab-\frac{h^2}{4}
   +\lambda_i\epsilon_i+\left(\lambda_i\mu_i-\frac h2\right)^2.
\end{aligned}                                               \tag{4}
\]

Summing (4) and restoring the off-diagonal terms proves (QFD).  Dropping the defects proves
(QFB), and (QFT) is exactly the condition that its floor is nonnegative.  Taking `a=1,b=M`
reduces (QFT) to (QFI).  The derivation uses no commutation between `A` and `Gamma`.

For the intrinsic form, put `B=Gamma^(1/2) A Gamma^(1/2)` on `supp Gamma`.  In the chosen
eigenbasis of `Gamma`, its entries are
`B_ij=sqrt(lambda_i lambda_j) C_ij`.  Therefore

\[
\begin{aligned}
 \left\|B-\frac h2P_\Gamma\right\|_{\rm HS}^{2}
 &=\sum_i\left(\lambda_i\mu_i-\frac h2\right)^2
   +\sum_{i\ne j}\lambda_i\lambda_j|C_{ij}|^2.
\end{aligned}
\]

Equation (2) is the coordinate expansion of the trace defect in (QFH), proving the basis-free
identity with no additional assumption.

## Sharpness

Assume `b-a>=1`, `a,b>0`, and `rho_*<=1`.  Give every support mode the common occupation
`lambda_i=rho_*`.  For each `i`, choose a mutually orthogonal pair of endpoint eigenvectors and an
endpoint mixture with mean

\[
 \mu_i=\frac{a+b-1}{2\rho_*}=\frac{2ab}{a+b-1}.
\]

The width assumption puts this mean in `[a,b]`.  Endpoint leakage and off-diagonal coherence
vanish, while every occupation-centering square vanishes.  Hence equality holds in (QFB) and the
boundary (QFT) is sharp.  Moving the common filling slightly below the boundary, while the
balancing mean remains inside `[a,b]`, gives a negative Fano margin.  Orthogonal direct sums give
the construction in every support rank.

For `a=1,b=M` with `2<=M<=4`, the sharp boundary is `rho=M/4` and the balancing endpoint mean is
`2`; the endpoint weight is `1/(M-1)`.  For `M=1`, direct substitution in (1) gives the exact
margin `sum_i lambda_i^2`, so there is no positive filling threshold.  In particular, quartic
stability is destroyed by any loss of filling, whereas quadratic and cubic systems retain a
nontrivial finite-temperature Fano-underdispersed phase.

## Determinantal and Hilbert-space interpretations

A finite DPP with Hermitian contraction kernel `Gamma` is the occupation process of the same
gauge-invariant quasi-free state.  For site weights given by the diagonal observable `A`, its
weighted additive statistic therefore obeys (QFD)--(QFT).  Projection DPPs are exactly the
full-filling face `rho=1`, recovering the Slater--Pluecker law.

Equivalently, (QFD) is a law for a positive contraction and a band-limited self-adjoint operator
on a Hilbert space.  It depends only on the trace and support rank of the contraction, the two
spectral endpoints, and three geometrically explicit defects.  The centering term is the new
mixed-state obstruction: incomplete occupation rescales each compressed spectral mean before it
can balance the universal affine secant.

## Operational consequences `[PROVED HERE]`

The law is invertible from the first two observed cumulants.  Rearranging (QFB) gives the
**noise-certified support-rank inequality**

\[
 \boxed{\quad
 4\left(ab\operatorname{tr}\Gamma-
   (\mathbb EX-\operatorname{Var}X)\right)
 \le \operatorname{rank}\Gamma\,(a+b-1)^2.
 \quad}                                                       \tag{QRW}
\]

Thus energy-counting mean and noise place a model-independent lower constraint on the number of
occupied one-particle modes, without reconstructing `Gamma` or diagonalizing it experimentally.

More strongly, let `Delta` be the excess of the Fano margin over the universal floor in (QFB).
The exact law gives two simultaneous stability estimates

\[
 \operatorname{tr}[\Gamma(A-aI)(bI-A)]\le\Delta,
\]

\[
 \left\|\Gamma^{1/2}A\Gamma^{1/2}
   -\frac{a+b-1}{2}P_\Gamma\right\|_{\rm HS}^{2}\le\Delta.   \tag{QST}
\]

Consequently near-optimal noise is rigid: it forces both endpoint concentration and metric
closeness of the occupied compression to the unique balancing scalar.  This turns the extremal
inequality into a robust certification theorem rather than only a sign criterion.

## Anti-theatre and hostile audit

1. **Parent-formula attack.**  The quasi-free/DPP moment formula (1) is standard full-counting
   statistics.  It is not novelty.  Only the exact decomposition, optimal floor, and phase
   boundary are candidates.
2. **Trivial-purification attack.**  A Naimark purification places auxiliary modes at spectral
   value zero and loses the positive lower endpoint.  It does not yield (QFB) or (QFT); the mixed
   centering square is essential.
3. **Commutation attack.**  No simultaneous diagonalization of `A` and `Gamma` is used.  The
   weighted off-diagonal compression energy is retained as a nonnegative defect.
4. **Rank-padding attack.**  Zero eigenvalues must be removed: otherwise artificial support
   padding adds cancelling negative floors and centering squares.  The invariant rank in (QFB) is
   exactly `rank Gamma`.
5. **Sharpness attack.**  Equal occupations and disjoint endpoint pairs annihilate all defects at
   the boundary, so no stronger bound can depend only on `a,b,tr Gamma,rank Gamma`.
6. **Known-inequality attack.**  Searches for weighted DPP Fano factors, quasi-free fermionic
   mean--variance bounds, spectral-width noise bounds, and occupation-dependent sub-Poisson
   thresholds found the standard variance identities and model-specific noise results, but not
   (QFD)--(QFI).  This is still only a search boundary; novelty remains unverified.
7. **Terminology attack.**  Here "Fano-underdispersed" means only `Var X <= E X`.  It does not
   assert moment-generating-function domination by a Poisson law.  Recent work on the stronger
   sub-Poisson MGF property explicitly shows that general scalar multiplication need not preserve
   it, so weighted degrees above one cannot be advertised under that stronger label.
8. **General-journal attack.**  Algebraic universality across operator theory, DPPs, and free
   fermions is promising but insufficient by itself.  General-journal suitability requires an
   independent expert search and a consequence that changes practice or resolves a named open
   problem.  No such claim is made here.

## Lean result

`GaloisForLFunctions.HilbertMetric.QuasiFreeFillingFano` compiles unconditionally with:

1. finite-coordinate quasi-free mean, variance, and Fano margin;
2. occupation-weighted edge, centering, and coherence defects;
3. the exact identities (QFD) and (QFH), including the literal squared Hilbert--Schmidt matrix;
4. nonnegativity of the defects under `lambda_i>=0` and the spectral band assumptions;
5. the floor (QFB), threshold (QFT), and positive-degree filling specialization (QFI);
6. the exact all-filling law for the degenerate unit-energy band;
7. the rank witness (QRW), stability bounds (QST), and equality classification;
8. a literal specialization to the existing Slater theorem at `lambda_i=1`.

## Log

- 2026-07-20 -- conjectured by replacing a projection density with a general contraction;
  completed the square in `lambda_i * mu_i`, discovered the basis-free Hilbert--Schmidt
  two-defect form, proved the sharp filling boundary and stability laws, and compiled the exact
  theorem family unconditionally.  Retained `[NOVELTY UNVERIFIED]` pending independent review.
