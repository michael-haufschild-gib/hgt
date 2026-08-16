# Mass-shifted hard Jacobi leakage Gramian law

- **ID:** `mass-shifted-hard-jacobi-leakage-gramian-law`
- **Stage:** 3 -- formalized in Lean 4
- **Route:** mass-shifted spectral face / hard first-contact chamber
- **Type:** THEOREM + NO-GO + FRONTIER REDUCTION
- **Scientific status:** `[LEAN-CERTIFIED] [UNCONDITIONAL] [BRIDGE] [NOVELTY UNVERIFIED]`
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
- [x] 2 -> 3: exact Lean formalization and axiom/build audit
- [ ] 3 -> 4: specialist novelty review and publication form

## Lean target

All four items are formalized:

1. exact coefficient projection of `K` as a single top-degree channel; **FORMALIZED**, together
   with stronger adaptive orthogonal landing, positive landing energy, and strict projected
   covariant dissipation in `RHTower.XiShiftedHalfDensityAdmissionBoundaryPort`;
2. orthonormal nearest-neighbor connection law from actual shifted-Xi coefficient curves;
   **MONIC EQUIVALENT FORMALIZED** in `RHTower.XiShiftedHalfDensityAdjacentConnection`, and
   consumed as the frame structure equation of `RHTower.ShiftedJacobiFrame`;
3. finite Jacobi Riccati boundary term `2n a_n^2 ee^T`; **FORMALIZED**, derived and not assumed,
   in `HTGeometry.JacobiRiccatiTruncation`, `HTGeometry.JacobiTodaRiccatiLaw` and
   `RHTower.XiShiftedJacobiFrameToda`;
4. inverse hard-operator square and finite Gramian identity; **FORMALIZED** in
   `HTGeometry.SkewConjugatedRiccatiGramian`, `HTGeometry.MatrixInverseCurveDerivative` and
   `RHTower.XiShiftedJacobiFrameToda`.

## Lean certificate

Every displayed law of this card is proved unconditionally in Lean 4.  `(HJLG.2)` is *derived*
from the frame structure equations, never supplied as a premise: the object of the theory is the
bundle `RHTower.ShiftedJacobiFrame`, which carries only the data the card's "Exact setup"
carries -- a differentiable polynomial frame of exact degree, its three-term recurrence, and the
half-density covariant ladder `(HJLG.1)` -- and every matrix law is a theorem about it.

Differentiation is entrywise on both matrices and polynomial curves, so no normed structure on
either space is used and no instance diamond can appear.

| Card item | Declaration | Module |
|---|---|---|
| coefficientwise derivative of a polynomial curve, with sum, scalar-product, `X`-multiplication and uniqueness | `PolyHasDerivAt`, `.add`, `.smul`, `.X_mul`, `.unique` | `RHTower.XiShiftedJacobiFrameToda` |
| the half-density generator is `ℝ`-linear | `xiShiftedMobiusHalfDensityGenerator_add`, `_smul` | same |
| **the frame bundle**: degree filtration, three-term recurrence, and the `(HJLG.1)` ladder | `ShiftedJacobiFrame` | same |
| **the covariant recurrence**: differentiating the recurrence and cancelling the generator against it leaves exactly the Riccati source `X²φ_k` | `ShiftedJacobiFrame.covariantRecurrence` | same |
| the frame is a degree filtration, so three consecutive frame vectors are independent | `ShiftedJacobiFrame.eq_zero_of_smul_three` | same |
| **the nonisospectral Toda system** `b_n' = 2(n−1)a_n² − 2(n+1)a_{n+1}² − b_n²`, `a_{n+1}' = a_{n+1}((n−½)b_n − (n+3/2)b_{n+1})` | `ShiftedJacobiFrame.level_zero_relations`, `.level_succ_relations`, `.jacobiTodaDeriv` | same |
| the symmetric tridiagonal Jacobi entries and the skew tridiagonal connection entries `(A_n)_{k,k+1} = (k+1/2)a_{k+1}` | `jacobiEntry`, `connectionEntry`, `jacobiCompression`, `connectionCompression` | `HTGeometry.JacobiRiccatiTruncation` |
| the connection matrix is skew; the Jacobi matrix is symmetric | `connectionCompression_skew`, `jacobiCompression_symm` | `…JacobiRiccatiTruncation`, `…JacobiTodaRiccatiLaw` |
| **the truncation identity**: dropping one level from `[J,A] − J²` costs exactly `2n a_n²` at the last diagonal entry | `jacobiCompression_riccati_truncation`, `jacobiCompression_riccati_matrix` | `HTGeometry.JacobiRiccatiTruncation` |
| **the entrywise Lax law**: the Toda system is exactly `J' = [J,A] − J²` for the infinite band | `laxTerm`, `laxSum_zero`, `laxSum_succ`, `laxSum_eq_jacobiEntry` | `HTGeometry.JacobiTodaRiccatiLaw` |
| **`(HJLG.2)`** at the level of coefficient curves | `jacobiCompression_deriv_eq_riccati` | same |
| **`(HJLG.2)`** for an actual frame | `ShiftedJacobiFrame.matrixHasDerivAt_jacobiLevel`, `.jacobiVelocityLevel_eq` | `RHTower.XiShiftedJacobiFrameToda` |
| entrywise differentiation of matrix curves, with product, sum, difference and transpose rules | `MatrixHasDerivAt`, `.mul`, `.add`, `.sub`, `.transpose`, `matrixHasDerivAt_smul_one` | `HTGeometry.SkewConjugatedRiccatiGramian` |
| a matrix curve with vanishing derivative is constant | `matrix_eq_of_matrixHasDerivAt_zero` | same |
| **`O' = −AO`, `A` skew, `O(y₀)=I` ⟹ `O` is orthogonal** | `transpose_mul_self_eq_one_of_skew_flow` | same |
| Cramer differentiability: determinant, adjugate and inverse of an entrywise differentiable curve | `differentiableAt_det_of_entries`, `differentiableAt_adjugate_of_entries`, `differentiableAt_inv_of_entries` | `HTGeometry.MatrixInverseCurveDerivative` |
| **the inverse curve is differentiable with `(J⁻¹)' = −J⁻¹J'J⁻¹`** | `matrixHasDerivAt_inv` | same |
| **`(HJLG.4)`**: `J' = [J,A] − J² − c·ee^T` ⟹ `U = J⁻¹ − y` obeys `U' = [U,A] + c(J⁻¹e)(J⁻¹e)^T` | `matrixHasDerivAt_centeredInverse` | `HTGeometry.SkewConjugatedRiccatiGramian` |
| **`(HJLG.3)`--`(HJLG.4)`** for an actual frame, with invertibility as the only side condition | `ShiftedJacobiFrame.matrixHasDerivAt_centeredInverseLevel` | `RHTower.XiShiftedJacobiFrameToda` |
| **skew conjugation removes the commutator** | `matrixHasDerivAt_conjugated` | `HTGeometry.SkewConjugatedRiccatiGramian` |
| **`(HJLG.5)`**: the conjugated increment is the exact integral of the transported source | `conjugated_increment_eq_integral` | same |
| the integral of a pointwise positive semidefinite matrix curve is positive semidefinite; conjugation and rank-one positivity | `intervalIntegrable_sum_fun`, `dotProduct_integral_nonneg`, `dotProduct_conj_eq`, `dotProduct_smul_vecMulVec_nonneg` | same |
| **`(HJLG.5)`** for an actual frame, and positivity of the boundary Gramian | `ShiftedJacobiFrame.boundaryGramianSource`, `.conjugatedCenteredInverse_increment`, `.boundaryGramian_nonneg` | `RHTower.XiShiftedJacobiFrameToda` |
| **the boundary port is visible to every node**: an eigenvector of an irreducible Jacobi compression has nonzero last coordinate | `jacobiRow_sum_succ`, `jacobiCompression_eigenvector_last_ne_zero` | `HTGeometry.JacobiNodeBoundaryMonotonicity` |
| **a commutator is invisible to an eigenvector** | `dotProduct_commutator_eigenvector` | same |
| **the eigenvalue derivative law**: a differentiable unit eigenvector branch moves its eigenvalue by the Rayleigh quotient of the matrix velocity | `hasDerivAt_finsetSum`, `eigenvalue_hasDerivAt_eq_rayleigh` | same |
| **`(HJLG.6)`**: every differentiable simple node branch of the centered inverse compression is strictly increasing | `ShiftedJacobiFrame.centeredNode_deriv_pos` | `RHTower.XiShiftedJacobiFrameToda` |

`#print axioms` on `laxSum_eq_jacobiEntry`, `jacobiCompression_deriv_eq_riccati`,
`matrixHasDerivAt_inv`, `jacobiCompression_eigenvector_last_ne_zero`,
`eigenvalue_hasDerivAt_eq_rayleigh`, `ShiftedJacobiFrame.covariantRecurrence`,
`ShiftedJacobiFrame.jacobiTodaDeriv`, `ShiftedJacobiFrame.jacobiVelocityLevel_eq`,
`ShiftedJacobiFrame.matrixHasDerivAt_centeredInverseLevel`,
`ShiftedJacobiFrame.conjugatedCenteredInverse_increment`,
`ShiftedJacobiFrame.boundaryGramian_nonneg` and `ShiftedJacobiFrame.centeredNode_deriv_pos`
each returns exactly `[propext, Classical.choice, Quot.sound]`.

### What the formal proof does differently

The paper proof reads the Lax law off "matrix coefficients in the moving orthonormal frame".  The
formal proof makes that step finite and checkable in two stages.

First, the infinite Lax law is shown to be *equivalent* to a closed two-line scalar system for the
coefficient curves.  Writing out `(JA − AJ − J²)` band by band, the `φ_{k±2}` coefficients cancel
identically, and the surviving `φ_k` and `φ_{k±1}` coefficients are precisely

`b_n' = 2(n−1)a_n² − 2(n+1)a_{n+1}² − b_n²`,
`a_{n+1}' = a_{n+1}((n−½)b_n − (n+3/2)b_{n+1})`,

a nonisospectral Toda system.  This replaces an infinite-matrix manipulation by a finite case
analysis on the distance between two indices, and it exposes the boundary term as the *only*
place where the compression differs from the band: `jacobiCompression_riccati_truncation` shows
the three lost products `J_{n-1,n}A_{n,n-1} = −(n−½)a_n²`, `−A_{n-1,n}J_{n,n-1} = −(n−½)a_n²`
and `−J_{n-1,n}J_{n,n-1} = −a_n²` sum to exactly `−2n a_n²`.

Second, the Toda system is *derived* from the frame rather than assumed.  Differentiating the
three-term recurrence and substituting the covariant ladder makes the half-density generator
cancel against the recurrence itself (`covariantRecurrence`), leaving the Riccati source `X²φ_k`;
equating coefficients is then legitimate because `deg φ_k = k`, so three consecutive frame vectors
are independent (`eq_zero_of_smul_three`).  The whole chain from `(HJLG.1)` to `(HJLG.2)` is
therefore free of matrix premises.

The centered-inverse layer is also strengthened.  The paper writes "differentiating `BJ_n = I`
gives `B' = −BJ_n'B`", tacitly assuming that `B` is differentiable.  `matrixHasDerivAt_inv` proves
that instead: Cramer's rule expresses every entry of `J⁻¹` as a quotient of two determinants, both
polynomial in the entries of `J`, so invertibility at a point already forces entrywise
differentiability there, and the product rule then identifies the derivative.  Invertibility is
the *only* side condition of `(HJLG.3)`--`(HJLG.4)` in the formal statement.

For `(HJLG.6)`, the formal proof isolates the three independent ingredients.  A commutator has
vanishing Rayleigh quotient at any eigenvector of a symmetric matrix; a differentiable unit
eigenvector branch moves its eigenvalue by exactly the Rayleigh quotient of the matrix velocity
(the Hellmann--Feynman law, proved here from scratch, using that the branch stays orthogonal to
its own velocity); and an eigenvector of a Jacobi compression with nonvanishing band cannot have
zero last coordinate -- reading the eigenvalue equation from the bottom row upwards, a zero last
coordinate propagates to every coordinate.  Together these give the exact rate

`u_i' = 2n a_n² x_i^{-2} (v_i·e)² > 0`.

`(HJLG.7)` is this same inequality after substituting the classical Christoffel identity for
`a_n²(v_i·e)²`.  That substitution is a change of normalization convention, not additional
content, and the invariant eigenvector-coordinate form above is what is certified; the displayed
`2n h_n/(x_i²γ_i)` depends on which of the monic and orthonormal normalizations `h_n` and `γ_i`
are taken in, and is not separately certified.

The open core of the card is untouched by all of this: `(HJLG.8)` still asks for a quantitative
comparison of the far hard reserve with the future boundary controllability Gramian at
`n ≍ sqrt(y)`, and no step above signs that difference.

## Log

- 2026-08-11 — internal/external audit, conjecture loop, paper proof, and exact remaining
  reserve-minus-Gramian open core completed.
- 2026-08-11 — item 1 formalized. Fixed coefficient truncation was rejected as final producer;
  current orthogonal admission gives a stronger positive three-channel completed source law.
- 2026-08-11 — item 2 formalized in its division-free monic equivalent:
  `V_n=M_n+(n-1/2)beta_n P_(n-1)`.
- 2026-08-16 — items 3 and 4 formalized and the card promoted to stage 3. `(HJLG.2)` is derived
  from the frame structure equations through the nonisospectral Toda system; `(HJLG.3)`--`(HJLG.5)`
  and `(HJLG.6)` follow; five new modules, all axiom-clean.
