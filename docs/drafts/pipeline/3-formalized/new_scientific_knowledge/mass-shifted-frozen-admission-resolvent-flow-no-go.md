# Frozen-admission resolvent-flow no-go

- **ID:** mass-shifted-frozen-admission-resolvent-flow-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / exact route no-go
- **Source:** mass-shifted-canonical-admission-arithmetic-transgression.md
- **Statement:** Positive Hankel chambers and exact shifted-moment transport do not control frozen-admission source sign: a three-atom positive resolvent flow has positive current canonical source but negative source for a nearby frozen canonical admission.

## Goal

Test whether Route U's mixed mass--admission obstruction can be closed from finite moment
positivity, canonical monic admission, and the exact shifted-Xi transport law alone. The theorem
below gives an exact negative answer and identifies the stronger literal input that survives.

## Gates

- [x] 0 → 1 in-progress: exact conjecture and source type isolated
- [x] 1 → 2 fully-proven: dependency-closed symbolic countermodel and positive survivor
- [x] 2 → 3 formalized: `formal/GaloisForLFunctions/RHTower/FrozenAdmissionResolventFlowNoGo.lean`
  formalizes the *literal* three-atom flow (explicit nodes `(t+d_i)⁻¹`, explicit weights
  `1, ε, ε`), not a generic wrapper: no abstract flow, no supplied spectral data, no hypothesis
  standing for an analytic input
- [ ] 3 → 4 publication-ready: external novelty audit and standalone exposition

## 1. Derivative target is odd current, not Christoffel distance

Let \(L_y\) be any differentiable moment flow satisfying

\[
 \frac d{dy}L_y(f)=-L_y\!\left(X(Xf'+f)\right).             \tag{FAR.1}
\]

For a polynomial \(A\), put

\[
 N_y(A)=L_y(A^2),\qquad J_y(A)=L_y(AXA),
\]

and define the adaptive source

\[
 Q_y(A)=2L_y\!\left((XA)X(XA'+A)\right).                   \tag{FAR.2}
\]

The Euler product identity used by the literal completed source gives

\[
 \boxed{\frac d{dy}J_y(A)=-Q_y(A)}                         \tag{FAR.3}
\]

when \(A\) is held fixed. Hence, for fixed polynomials \(P,A\),

\[
 Q_y(A)-Q_y(P)
 =-\frac d{dy}\bigl(J_y(A)-J_y(P)\bigr).                  \tag{FAR.4}
\]

This is the exact differential meaning of arithmetic admission transgression. It is not the
derivative of \(N_y(A)-N_y(P)\): differentiating the latter inserts
\(X(X(A^2)'+A^2)\), a different carrier from (FAR.2).

Let \(P_{n,y}\) be current monic orthogonal admission, \(h_n=L_y(P_{n,y}^2)\), and let
\(a_n(y)\) be its coefficient of \(X^{n-1}\). For a fixed frozen admission \(A\), the corpus's
moving-current identity sharpens (FAR.4) to

\[
 \boxed{
 \frac d{dy}\left(J_y(A)-J_y(P_{n,y})\right)
 =-\bigl(Q_y(A)-Q_y(P_{n,y})\bigr)-2h_n a_n'(y).}          \tag{FAR.5}
\]

Thus even the correct odd-current primitive retains exactly the canonical admission connection.
The conjectural identity “transgression = negative derivative of Christoffel distance” is false
both by carrier type and by (FAR.5).

At one mass, write \(\Delta=A-P_{n,y}\) and
\(\delta=[X^{n-1}]\Delta\). Orthogonality and the monic three-term recurrence give the exact
displacement law

\[
 \boxed{J_y(A)-J_y(P_{n,y})=2h_n\delta+J_y(\Delta).}       \tag{FAR.6}
\]

Admission mismatch is therefore an affine odd-Jacobi displacement, not a nonnegative norm
distance. This explains why Christoffel minimization cannot sign it.

## 2. Three-atom positive resolvent-flow countermodel [PROVED HERE]

Choose \(0<a<y\) and distinct \(d_1,d_2,d_3>0\) such that

\[
 y+d_1<2(a+d_1).                                          \tag{FAR.7}
\]

For \(t>0\), set

\[
 x_i(t)=\frac1{t+d_i},\qquad
 L_{t,\varepsilon}(f)=x_1(t)f(x_1(t))
   +\varepsilon\sum_{i=2}^3x_i(t)f(x_i(t)),               \tag{FAR.8}
\]

where \(\varepsilon>0\). Its moments are

\[
 s_{t,\varepsilon}(k)=x_1(t)^{k+1}
   +\varepsilon\sum_{i=2}^3x_i(t)^{k+1},
\]

so direct differentiation proves exact shifted-moment law

\[
 s_{t,\varepsilon}'(k)=-(k+1)s_{t,\varepsilon}(k+1).       \tag{FAR.9}
\]

For every \(\varepsilon>0\), every \(t>0\), and every nonzero polynomial \(q\) of degree at most
two,

\[
 L_{t,\varepsilon}(q^2)>0.                                \tag{FAR.10}
\]

Indeed, all three weights are positive and a nonzero quadratic cannot vanish at three distinct
nodes. Thus the full \(3\times3\) Hankel block required for degree-one current-source positivity
is positive definite throughout the flow.

Degree-one canonical admission at frozen mass \(a\) is

\[
 P_{a,\varepsilon}(X)=X-\alpha_{a,\varepsilon},\qquad
 \alpha_{a,\varepsilon}
 =\frac{s_{a,\varepsilon}(1)}{s_{a,\varepsilon}(0)}.       \tag{FAR.11}
\]

For \(P=X-\alpha\), (FAR.2) is explicitly

\[
 Q_{y,\varepsilon}(P)
 =2\sum_{i=1}^3 c_i x_i(y)^3
       (x_i(y)-\alpha)(2x_i(y)-\alpha),
 \quad c_1=1,\ c_2=c_3=\varepsilon.                       \tag{FAR.12}
\]

At \(\varepsilon=0\), (FAR.11) gives
\(\alpha_{a,0}=x_1(a)\). Condition (FAR.7) is exactly

\[
 x_1(y)<x_1(a)<2x_1(y),
\]

and therefore

\[
 Q_{y,0}(P_{a,0})
 =2x_1(y)^3(x_1(y)-x_1(a))(2x_1(y)-x_1(a))<0.             \tag{FAR.13}
\]

Both \(\alpha_{a,\varepsilon}\) and (FAR.12) are continuous at
\(\varepsilon=0\), with denominator strictly positive there. Hence (FAR.13) remains strict
for every sufficiently small \(\varepsilon>0\). For each such \(\varepsilon\), (FAR.10) holds,
while current canonical source satisfies

\[
 Q_{y,\varepsilon}(P_{y,\varepsilon})>0                   \tag{FAR.14}
\]

by the finite Jacobi-energy identity in the same positive \(3\times3\) chamber. Equations
(FAR.13)--(FAR.14) prove exact sign reversal between current and nearby frozen canonical
admissions inside a globally positive finite moment flow.

Choice \(y>a\) may be arbitrarily close. Thus compact transport, smooth canonical admission,
strict finite Hankel positivity, and exact moment ODE do not prevent transgression debt from
exceeding current positive source.

## 3. No-go closure

- **Exact killing theorem/mechanism:** (FAR.8)--(FAR.14) satisfy the same finite positivity,
  canonical admission, and moment-transport laws used by the proposed Christoffel/Jacobi proof,
  yet exhibit the forbidden frozen-source sign. Any theorem using only those data is false.
- **Strongest positive survivor:** (FAR.3)--(FAR.6) classify mixed transgression as odd-current
  curvature with nonremovable admission connection. Three-atom theorem proves Route U must exploit
  a property absent from arbitrary positive resolvent flows.
- **New insight:** repeated failure of norm, Jacobi, and bounded-transport arguments is one
  phenomenon: admission minimizes even metric \(L(P^2)\), whereas completed source is mass
  derivative of odd current \(L(PXP)\). Multiplication by \(X\) is missing orientation. Finite
  Hankel positivity does not orient it.
- **Surviving Route U requirement:** use literal labelwise prime--Gamma formation, or a global
  completed-Xi constraint equivalent in strength, to distinguish Xi flow from (FAR.8). Another
  finite-block, Christoffel-distance, generic Riccati, or compact-path inequality cannot close
  route.
- **Lean status:** formalized unconditionally in
  `formal/GaloisForLFunctions/RHTower/FrozenAdmissionResolventFlowNoGo.lean`, for the literal
  three-atom flow only (no abstract moment-flow wrapper, so no Route U formal credit is claimed
  for a generic transport theorem):
  * (FAR.8)/(FAR.9) `farNode`, `farFunctional`, `farMoment`, `hasDerivAt_farMoment`
    (`s'(k) = -(k+1) s(k+1)`);
  * (FAR.10) `farFunctional_sq_pos` — the full degree-two Hankel chamber is positive definite at
    every positive weight and every positive mass;
  * (FAR.2)/(FAR.12) `farSource`, `farSource_eq`; (FAR.11) `farAlpha`; `farNorm`, `farOddCurrent`;
  * (FAR.3) `hasDerivAt_farOddCurrent` (`d/dt J_t(A) = -Q_t(A)`), (FAR.4)
    `hasDerivAt_farOddCurrent_sub`, (FAR.6) `farOddCurrent_sub_farOddCurrent_alpha`
    (affine odd-Jacobi displacement `2 h₁ δ + J(Δ)`);
  * (FAR.5) `hasDerivAt_farAlpha`, `farFunctional_mul_sub_farAlpha`,
    `hasDerivAt_farOddCurrent_moving`, `hasDerivAt_farOddCurrent_displacement` — the moving
    canonical admission keeps the connection term `2 h₁ α'(y)`;
  * (FAR.13) `farSource_frozen_neg_zero` and `eventually_farSource_frozen_neg`, (FAR.14)
    `farSource_current_pos` (proved by the exact split
    `Q/2 = L(X²P²) + (2W)⁻¹ Σ_{i<j} w_i w_j (x_i³-x_j³)(x_i-x_j)`);
  * capstone `exists_frozen_admission_source_sign_reversal`: some `ε > 0` has a positive-definite
    degree-two chamber, positive current canonical source, and negative frozen canonical source.
  Audits `[propext, Classical.choice, Quot.sound]`.

## 4. Conjecture → fail → pivot log

1. **Conjecture:** frozen/current transgression is negative derivative of Christoffel norm
   distance. **Failed:** exact carrier audit gives (FAR.3)--(FAR.5).
2. **Conjecture:** bounded positive admission transport nevertheless preserves source sign.
   **Failed sharply:** three-atom positive resolvent flow (FAR.8) has opposite sign.
3. **Pivot:** seek a label-sensitive prime--Gamma inequality or global completed-Xi law violated
   by finite positive resolvent mixtures. Generic orthogonal-polynomial transport is classified
   out.

## Log

- 2026-08-11 — derived odd-current differential classification and exact affine displacement.
- 2026-08-11 — proved three-atom positive resolvent-flow frozen-source countermodel; retired
  Christoffel-distance and generic bounded-transport sign routes.
