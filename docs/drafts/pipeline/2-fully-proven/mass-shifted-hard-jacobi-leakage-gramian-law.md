# Mass-shifted hard Jacobi leakage Gramian law

- **ID:** `mass-shifted-hard-jacobi-leakage-gramian-law`
- **Stage:** 2-fully-proven
- **Route:** mass-shifted spectral face / hard first-contact chamber
- **Type:** THEOREM + NO-GO + FRONTIER REDUCTION
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [LEAN PARTIAL]`
- **Depends on:** shifted reciprocal moment ODE, half-density Möbius source connection, finite
  orthogonal-polynomial recurrence, positive-chamber differentiability
- **Statement:** In the normalized orthogonal frame, the shifted-Xi half-density connection is an
  exactly skew nearest-neighbor ladder. Every finite Jacobi compression therefore satisfies a
  nonisospectral Riccati law with one negative rank-one boundary input. After inversion and
  centering by mass, that input becomes a positive rank-one controllability Gramian. Projection
  leakage is thus a positive hard-coordinate source, not an uncontrolled truncation error.

## Public sentence

Finite admission loses exactly one boundary channel; in reciprocal hard coordinates that lost
channel is positive and accumulates as a controllability Gramian.

## Exact setup

Let `L_y` be a differentiable positive moment functional on one chamber and suppose

`d/dy L_y(R) = -L_y(X (X R' + R))`

for every fixed polynomial `R`. Put

`K P = X^2 P' + (1/2) X P`,  `nabla P = dot P - K P`.

Let `P_k(y)` be the monic orthogonal polynomials, `h_k=L_y(P_k^2)>0`,

`a_k=sqrt(h_k/h_(k-1))` for `k>=1`, and `phi_k=P_k/sqrt(h_k)`.

Multiplication has the orthonormal Jacobi matrix

`X phi_k = a_(k+1) phi_(k+1) + b_k phi_k + a_k phi_(k-1)`.

For `n>=1`, let `J_n` be its compression to `phi_0,...,phi_(n-1)`, let
`e=e_(n-1)`, and define the skew tridiagonal matrix `A_n` by

`(A_n)_(k+1,k)=-(k+1/2)a_(k+1)`,

`(A_n)_(k,k+1)= +(k+1/2)a_(k+1)`.

## The theorem `[PAPER-PROVED]`

### 1. Metric-compatible nearest-neighbor connection

For every `k>=0`, with the negative-index term omitted,

\[
 \boxed{
 \nabla\phi_k
 =-(k+\tfrac12)a_{k+1}\phi_{k+1}
 +(k-\tfrac12)a_k\phi_{k-1}.
 }
 \tag{HJLG.1}
\]

Thus the connection matrix in the orthonormal frame is exactly skew and nearest-neighbor.

### 2. Finite Jacobi boundary-source law

The `n`-level Jacobi compression satisfies

\[
 \boxed{
 J_n'=[J_n,A_n]-J_n^2-2n a_n^2 ee^{\mathsf T}.
 }
 \tag{HJLG.2}
\]

The first two terms are gauge/nonisospectral bulk. The last term is the sole finite-admission
boundary source.

### 3. Centered inverse hard operator

Where `J_n` is invertible, define

\[
 U_n=J_n^{-1}-yI.
 \tag{HJLG.3}
\]

Then

\[
 \boxed{
 U_n'=[U_n,A_n]
 +2n a_n^2(J_n^{-1}e)(J_n^{-1}e)^{\mathsf T}.
 }
 \tag{HJLG.4}
\]

Let `O_n'=-A_nO_n`, `O_n(y_0)=I`. Since `A_n` is skew, `O_n` is orthogonal and

\[
 \boxed{
 O_n(Y)^{\mathsf T}U_n(Y)O_n(Y)-U_n(y_0)
 =\int_{y_0}^{Y}2n a_n(v)^2 z_n(v)z_n(v)^{\mathsf T}\,dv,
 }
 \tag{HJLG.5}
\]

where `z_n(v)=O_n(v)^T J_n(v)^(-1)e`. The right side is positive semidefinite.

### 4. Node shadow and exact strictness

The eigenvalues of `J_n` are the Gauss nodes `x_i`; those of `U_n` are

`u_i=x_i^(-1)-y`.

Irreducibility of the Jacobi matrix makes every eigenvector's last coordinate nonzero. Therefore
each simple nonzero node obeys

\[
 u_i'>0.
 \tag{HJLG.6}
\]

Using the standard last-coordinate/Christoffel identity reduces (HJLG.6) to the corpus paper law

\[
 u_i'=\frac{2n h_n}{x_i^2\gamma_i}>0.
 \tag{HJLG.7}
\]

Thus individual Gauss-node monotonicity is the spectral shadow of one matrix-valued positive
boundary Gramian.

## Complete paper proof

The half-density product law gives metric compatibility:

`d <P,Q>_y = <nabla P,Q>_y + <P,nabla Q>_y`.

Differentiate `<phi_j,phi_k>=delta_(jk)`. Hence the connection coefficients

`C_(j,k)=<phi_j,nabla phi_k>`

form a skew matrix. Since `dot phi_k` has degree at most `k`, while `K phi_k` has degree at most
`k+1`, `nabla phi_k` has degree at most `k+1`. If `j<=k-2`, skewness and the degree bound on
`nabla phi_j` give `C_(j,k)=0`. Therefore only the adjacent coefficients survive. The leading
coefficient of `phi_k` is `h_k^(-1/2)`. The top coefficient of `-K phi_k` is
`-(k+1/2)h_k^(-1/2)`. Since the leading coefficient of `phi_(k+1)` is
`h_(k+1)^(-1/2)`,

`C_(k+1,k)=-(k+1/2)sqrt(h_(k+1)/h_k)=-(k+1/2)a_(k+1)`.

Skewness supplies `C_(k-1,k)=(k-1/2)a_k`, proving (HJLG.1).

The already-proved covariant multiplication identity is

`nabla(XP)-X nabla(P)=-X^2P`.

Taking matrix coefficients in the moving orthonormal frame gives the infinite nonisospectral Lax
law

`J'=[J,A]-J^2`.

Compress to indices `0,...,n-1`. Only the edge between `n-1` and `n` crosses the compression.
Its Jacobi coefficient is `a_n`; its connection coefficient is `(n-1/2)a_n`. Therefore

`P[J,A]P-[PJP,PAP]=-(2n-1)a_n^2 ee^T`.

Also

`PJ^2P=(PJP)^2+a_n^2ee^T`.

Adding the two boundary contributions gives `-2n a_n^2ee^T`, proving (HJLG.2).

Write `B=J_n^(-1)`. Differentiating `BJ_n=I` gives `B'=-BJ_n'B`. Substitution of (HJLG.2)
and `BJ_n=J_nB=I` yields

`B'=[B,A_n]+I+2n a_n^2(Be)(Be)^T`.

Subtracting the derivative of `yI` proves (HJLG.4). For `O'=-AO`, skewness gives
`(O^TUO)'=O^T(U'-[U,A])O`, hence the positive rank-one integrand in (HJLG.5). Integration proves
the Gramian identity.

For a normalized eigenvector `v_i` of `J_n` with eigenvalue `x_i`, the commutator in (HJLG.4)
has zero Rayleigh quotient. Thus

`u_i'=2n a_n^2 x_i^(-2) (v_i^T e)^2`.

An irreducible Jacobi eigenvector cannot have last coordinate zero, proving strictness. The
Christoffel identity `a_n^2(v_i^Te)^2=h_n/gamma_i` gives (HJLG.7).

Every step is algebraic or finite-dimensional once metric compatibility is known; no RH statement,
asymptotic, or numerical input occurs.

## Conjecture -> proof/failure loop

1. `[CONJECTURE]` Coefficient projection of `K` is automatically dissipative in odd current.
   `[FALSIFIED]` The discarded top coefficient pairs with the first unseen moment, whose sign is
   freely variable by the existing boundary-extension-class theorem.
2. **Stronger replacement:** change from odd current to the reciprocal Jacobi hard operator.
   `[PAPER-PROVED]` The same discarded channel becomes the positive square in (HJLG.4).
3. `[CONJECTURE]` Positivity of the hard forcing by itself excludes a negative hard coordinate at
   first contact. `[FALSIFIED]` Even the scalar law `u'=r`, `r>0`, can start negative and end
   positive. Loewner monotonicity controls orientation, not absolute level.
4. **Positive survivor:** (HJLG.5) gives the exact level debt:

   \[
   U_n(y_0)=O_n(Y)^TU_n(Y)O_n(Y)-\mathcal G_n[y_0,Y].
   \tag{HJLG.8}
   \]

   A closure theorem must compare the far hard reserve with the future boundary controllability
   Gramian. It cannot be a face-only sign, fixed reporter, or orientation argument.
5. `[CONJECTURE]` Fixed-degree far positivity makes the right side of (HJLG.8) positive uniformly
   at cofinal degree. `[FALSIFIED]` The Möbius inverse degree horizon and bounded-super-apex model
   permit the Gramian debt to remain order one when `n` grows with mass.
6. **Stronger live conjecture:** selected completed-Xi incidence supplies a quantitative
   far-reserve-minus-Gramian inequality at `n asymp sqrt(y)`. `[OPEN CORE]` Neither phase-space
   compactness nor Padé-residue survival presently signs this difference.

## Higher universal principle

Three apparently different obstructions are shadows of one boundary-control law:

| Shadow | Universal object |
|---|---|
| half-density generator raises degree | boundary input channel `e` |
| rank-two Hankel terminal flux | Gram representation before orthogonalization |
| increasing centered reciprocal Gauss nodes | eigenvalue shadow of positive hard Gramian |
| positive Padé-pole residue | spectral mass seen by the same hard channel |

Finite admission is not losing an arbitrary class. It is eliminating one source-controlled port.
The port is indefinite in the original odd Hankel metric but positive after the centered inverse
Jacobi transform. Reasons earlier arguments stalled were shadows of using the wrong state variable:
orientation is a derivative, while endpoint admission is a reserve-minus-controllability-budget
comparison.

## Literature / collision audit

- `[LITERATURE]` Yue--Chang--Hu, *Stationary reduction method based on nonisospectral deformation
  of orthogonal polynomials, and discrete Painleve-type equations*, arXiv:2407.09875v3, derive
  nonisospectral Toda/Lax systems from time-dependent orthogonality.
- `[LITERATURE]` Vieira--Botta, *Orthogonal polynomials and Mobius transformations*,
  arXiv:1904.10766, develop Mobius-transformed orthogonality and recurrence relations.
- `[LITERATURE]` Ariznabarreta--Manas, *Linear spectral transformations for multivariate
  orthogonal polynomials and multispectral Toda hierarchies*, arXiv:1511.09129, develop moment
  factorization and Toda deformations.
- `[BRIDGE]` Skew orthonormal-frame connections and nonisospectral Lax equations are parent theory,
  so those ingredients are not claimed new.
- `[NOVELTY UNVERIFIED]` No audited source was found with the shifted reciprocal moment law's
  forced half-density coefficient, exact `2n a_n^2` finite boundary input, centered inverse hard
  Loewner Gramian, and its simultaneous identification with Gauss hard-coordinate and Padé-residue
  leakage. External priority remains unresolved.

## Gates

- [x] 0 -> 1: exact source law, falsifiers, and parent theories fixed
- [x] 1 -> 2: dependency-closed paper proof and hostile no-go audit complete
- [ ] 2 -> 3: exact Lean formalization and axiom/build audit
- [ ] 3 -> 4: specialist novelty review and publication form

## Lean target

Formalize, in this order:

1. exact coefficient projection of `K` as a single top-degree channel; **FORMALIZED**, together
   with stronger adaptive orthogonal landing, positive landing energy, and strict projected
   covariant dissipation in `RHTower.XiShiftedHalfDensityAdmissionBoundaryPort`;
2. orthonormal nearest-neighbor connection law from actual shifted-Xi coefficient curves;
3. finite Jacobi Riccati boundary term `2n a_n^2 ee^T`;
4. inverse hard-operator square and finite Gramian identity.

No abstract theorem with (HJLG.2) supplied as a hypothesis counts as route formalization.

## Log

- 2026-08-11 — internal/external audit, conjecture loop, paper proof, and exact remaining
  reserve-minus-Gramian open core completed.
- 2026-08-11 — item 1 formalized. Fixed coefficient truncation was rejected as final producer;
  current orthogonal admission gives a stronger positive three-channel completed source law.
