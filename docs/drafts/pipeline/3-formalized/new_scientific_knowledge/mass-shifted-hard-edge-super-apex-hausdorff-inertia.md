# Hard-edge super-apex Hausdorff inertia and finite ancestry

- **ID:** `mass-shifted-hard-edge-super-apex-hausdorff-inertia`
- **Stage:** 3-formalized / needs independent specialist audit
- **Route:** U, selected shifted-Xi null faces
- **Type:** THEOREM + NO-GO (paper)
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [FORMALIZED]`
- **Source:** `mass-shifted-hard-edge-hyperbolic-weil-boundary`,
  `mass-shifted-hard-edge-parity-jet-inertia`
- **Statement:** A negative hard-edge root is not a negative finite Hankel node. It is the
  reciprocal hard-edge limit of a positive quadrature node lying above the moving mass apex.
  The first Hausdorff-difference form counts such super-apex nodes exactly by inertia. Fixed-degree
  arcsine recession cannot detect a super-apex node whose Christoffel weight vanishes.

## Goal and correction

Identify the literal finite first-contact ancestor of the hard-edge terminal odd signature

\[
\gamma_r\longmapsto r\gamma_r.
\]

The first conjecture was wrong: hard-edge multiplication by `u` does **not** descend from finite
multiplication by `X`. The hard coordinate is reciprocal and centered. Consequently a negative
hard root does not come from a negative finite node. The exact finite obstruction is endpoint
leakage past the moving node `1/y`.

No abstract positivity wrapper is credited here. Sections 1--5 use the actual Route-U shifted-Xi
moment normalization, its canonical positive flat quadrature, and the Möbius numerator already
present in the hard-edge compactification.

## 1. Positive flat face and exact quadrature

Fix a selected singular shifted-Xi face at mass `y>0`. Write

\[
s_y(k)=\Re\,\operatorname{xiShiftedReciprocalMoment}(y,k),
\qquad L_y(X^k)=s_y(k).
\]

Let `p` be its canonical degree-`n` null polynomial. The preceding `n` by `n` Hankel block is
positive definite, the next block is positive semidefinite and singular, and `p` has `n` distinct
real roots

\[
x_1,\ldots,x_n.
\]

The finite-boundary quadrature theorem supplies weights `omega_i>0` such that

\[
L_y(g)=\sum_{i=1}^n\omega_i g(x_i)
\quad\text{for every }\deg g\le 2n.                         \tag{SAHI.1}
\]

This is the literal quadrature of the selected face, not a freely chosen representing measure.

Define on polynomials of degree less than `n`

\[
\mathcal E_y(q)=L_y\bigl((1-yX)q(X)^2\bigr).                \tag{SAHI.2}
\]

Since the integrand has degree at most `2n-1`, (SAHI.1) gives

\[
\boxed{\quad
\mathcal E_y(q)=\sum_{i=1}^n
  \omega_i(1-yx_i)q(x_i)^2.
\quad}                                                       \tag{SAHI.3}
\]

Evaluation at the `n` distinct nodes is an isomorphism

\[
\mathbb R_{<n}[X]\longrightarrow\mathbb R^n.
\]

Therefore the complete inertia of `mathcal E_y` is

\[
\begin{aligned}
\operatorname{ind}_+(\mathcal E_y)&=\#\{i:x_i<1/y\},\\
\operatorname{ind}_0(\mathcal E_y)&=\#\{i:x_i=1/y\},\\
\operatorname{ind}_-(\mathcal E_y)&=\#\{i:x_i>1/y\}.
\end{aligned}                                                \tag{SAHI.4}
\]

For the unnormalised Lagrange quotient

\[
\ell_i(X)=\frac{p(X)}{X-x_i},
\]

put

\[
\gamma_i=L_y(\ell_i^2)=\omega_i p'(x_i)^2>0.
\]

Then the individual endpoint signature is

\[
\boxed{\quad
\mathcal E_y(\ell_i)=(1-yx_i)\gamma_i.
\quad}                                                       \tag{SAHI.5}
\]

Equations (SAHI.4)--(SAHI.5) are an exact finite theorem. No limiting argument enters their
proof.

## 2. Correct hard-edge coordinate

Put `y=a^2`. The hard-edge paper uses

\[
P(\rho)=p\!\left(\frac{1+\rho}{2y}\right),
\qquad
S(u)=\left(1+\frac uy\right)^n
 P\!\left(\frac{1-u/y}{1+u/y}\right).                       \tag{SAHI.6}
\]

Substitution into (SAHI.6) gives the exact identity

\[
S(u)=\left(1+\frac uy\right)^n p\!\left(\frac1{y+u}\right). \tag{SAHI.7}
\]

Thus a finite root `x_i` and its Cayley, normalized-node, and hard coordinates satisfy

\[
\rho_i=2yx_i-1,
\qquad t_i=yx_i,
\qquad
\boxed{\quad u_i=x_i^{-1}-y=y\frac{1-t_i}{t_i}.\quad}       \tag{SAHI.8}
\]

For every compact hard-edge root, `x_i>0` eventually. Combining (SAHI.5) and (SAHI.8) yields

\[
\mathcal E_y(\ell_i)=x_i u_i\gamma_i.                       \tag{SAHI.9}
\]

Hence its sign is exactly the sign of `u_i`. The extra positive factor `x_i` explains why finite
multiplication by `X` was the wrong conjecture: hard multiplication by `u` descends from the
centered reciprocal operator `X^{-1}-y`, while the polynomial first-difference form sees

\[
1-yX=X(X^{-1}-y).                                           \tag{SAHI.10}
\]

Negative hard coordinate is therefore equivalent to **positive super-apex leakage**:

\[
u_i<0
\quad\Longleftrightarrow\quad
x_i>1/y
\quad\Longleftrightarrow\quad
t_i>1.                                                       \tag{SAHI.11}
\]

The exact boundary-layer scales are

\[
x_i-\frac1y=-\frac{u_i}{y(y+u_i)},                           \tag{SAHI.12}
\]

\[
y(t_i-1)=-\frac{yu_i}{y+u_i},
\qquad
y(\rho_i-1)=-\frac{2yu_i}{y+u_i}.                           \tag{SAHI.13}
\]

If `u_i` tends to a finite `r`, then

\[
y^2\left(x_i-\frac1y\right)\longrightarrow-r,
\qquad
y(t_i-1)\longrightarrow-r,
\qquad
y(\rho_i-1)\longrightarrow-2r.                             \tag{SAHI.14}
\]

Thus a negative hard root lives at raw reciprocal scale `y^{-2}=a^{-4}`, or normalized endpoint
scale `y^{-1}=a^{-2}`. Bulk root location cannot resolve this layer.

## 3. First Hausdorff difference is the exact finite odd ancestor

For `w>1`, set `y=w^2` and use the actual normalized Route-U moments

\[
m_w(k)=\frac{2w^{2k+1}}{\log w}\,s_y(k)
=C_w y^k s_y(k),
\qquad C_w=\frac{2w}{\log w}>0.                             \tag{SAHI.15}
\]

Define the first Hausdorff-difference matrix

\[
D_n(w)=\bigl[m_w(i+j)-m_w(i+j+1)\bigr]_{0\le i,j<n}.        \tag{SAHI.16}
\]

For \(Q(T)=\sum_i c_iT^i\), put `q(X)=Q(yX)`. Direct expansion gives

\[
\boxed{\quad
c^{\mathsf T}D_n(w)c
=C_w L_y\bigl((1-yX)Q(yX)^2\bigr)
=C_w\mathcal E_y(q).
\quad}                                                       \tag{SAHI.17}
\]

The coefficient dilation `Q(T) -> Q(yX)` is invertible. Therefore (SAHI.4) becomes

\[
\boxed{\quad
\operatorname{ind}_-D_n(w)=\#\{i:t_i>1\},
\quad
\dim\ker D_n(w)=\#\{i:t_i=1\}.
\quad}                                                       \tag{SAHI.18}
\]

This identifies the finite ancestor of hard-edge odd root-jet inertia. A sufficient finite
admission statement is precisely first Hausdorff positivity at the moving selected degree:

\[
D_{n_j}(w_j)\succeq0.                                      \tag{SAHI.19}
\]

For exclusion of finite negative hard roots, the minimal requirement is weaker than (SAHI.19):
for every fixed `R>0`, eventually no selected quadrature node may satisfy

\[
-R\le y_j\frac{1-t_{j,i}}{t_{j,i}}<0.                       \tag{SAHI.20}
\]

Super-apex nodes whose hard coordinate escapes to minus infinity do not survive the compactified
root problem and need not be excluded by this card.

## 4. Literal source flux identity

The completed-Xi reciprocal moments obey the unconditional differential law

\[
\frac d{dy}s_y(k)=-(k+1)s_y(k+1).                            \tag{SAHI.21}
\]

Consequently the first Hausdorff difference is a radial source flux:

\[
\boxed{\quad
m_w(k)-m_w(k+1)
=\frac{C_w}{k+1}\frac d{dy}\bigl(y^{k+1}s_y(k)\bigr),
\qquad y=w^2.
\quad}                                                       \tag{SAHI.22}
\]

More generally, for fixed coefficients `c_i`, define

\[
\Phi_c(y)=\sum_{i,j<n}
 \frac{c_ic_j}{i+j+1}y^{i+j+1}s_y(i+j).
\]

Then

\[
\boxed{\qquad C_w\Phi_c'(y)=c^{\mathsf T}D_n(w)c.\qquad}    \tag{SAHI.23}
\]

Thus endpoint admission is not another arbitrary moment inequality. It is monotonicity of an
explicit integrated completed-Xi radial flux on moving-degree test polynomials.

## 5. Hard-edge ancestry theorem

Let selected masses `y_j` tend to infinity, with null polynomials `p_j`, cleared hard polynomials
`S_j`, and

\[
S_j\longrightarrow F
\]

locally uniformly, where `F` is nonzero. Suppose `r<0` is a root of `F` of multiplicity `m`.
Choose a closed disk around `r` containing no other root of `F`. Hurwitz gives exactly `m` roots
`u_{j,1},...,u_{j,m}` of `S_j` in that disk for all large `j`. Since every `S_j` is real-rooted,
these roots are real and converge to `r`.

Their finite nodes are

\[
x_{j,k}=\frac1{y_j+u_{j,k}},
\qquad
t_{j,k}=\frac{y_j}{y_j+u_{j,k}}.
\]

For large `j`, `y_j+u_{j,k}>0` and `u_{j,k}<0`, hence

\[
x_{j,k}>1/y_j,
\qquad t_{j,k}>1.
\]

By (SAHI.18),

\[
\boxed{\qquad
\operatorname{ind}_-D_{n_j}(w_j)\ge m
\quad\text{for all large }j.
\qquad}                                                      \tag{SAHI.24}
\]

Therefore every negative terminal hard-edge signature has literal finite first-contact ancestry:
it is a bounded super-apex quadrature cluster, not a sign created by passage to the limit.

## 6. No-go: bulk arcsine recession is endpoint-blind

Fix `c>0`. Let `nu_j` be positive finite atomic probability measures supported in `(0,1)` and
converging weakly to the arcsine law. Choose `y_j -> infinity`, `epsilon_j>0` with
`epsilon_j -> 0`, and set

\[
t_j^{\mathrm{out}}=1+\frac c{y_j},
\qquad
\mu_j=(1-\epsilon_j)\nu_j+epsilon_j\delta_{t_j^{\mathrm{out}}}. \tag{SAHI.25}
\]

Choose the atoms distinct. Every fixed moment of `mu_j` converges to the corresponding arcsine
moment. Consequently every fixed Hankel block has the same positive-definite arcsine limit.

Nevertheless, at the full atomic degree the null polynomial has every support atom as a root.
Its Lagrange polynomial at `t_j^{out}` gives

\[
\int(1-t)Q_j(t)^2\,d\mu_j(t)
=-\epsilon_j\frac c{y_j}Q_j(t_j^{\mathrm{out}})^2<0.        \tag{SAHI.26}
\]

The outlier hard coordinate is

\[
u_j=y_j\frac{1-t_j^{\mathrm{out}}}{t_j^{\mathrm{out}}}
=-\frac c{1+c/y_j}\longrightarrow-c.                       \tag{SAHI.27}
\]

Thus fixed-degree moment convergence, weak arcsine convergence, positivity of every fixed limiting
block, and exact flat quadrature are jointly compatible with a bounded negative hard-root
precursor. The outlier's weight may vanish while its root coordinate survives. Whenever a nonzero
locally uniform hard-polynomial limit is independently available, as it is on the selected Route-U
sequence, that convergent root forces the limit to vanish at `-c`.

This countermodel does **not** satisfy the completed-Xi source law (SAHI.21) and does not refute a
source-specific proof. It proves the narrower no-go needed here:

> no argument using only fixed-degree arcsine recession or bulk weak convergence can establish
> Route-U endpoint admission.

## 7. Conjecture -> failure -> pivot

1. **Conjecture:** negative hard roots descend from negative finite Gauss nodes.
   **FALSIFIED.** Equation (SAHI.8) shows they descend from positive nodes just above `1/y`.
2. **Conjecture:** the finite odd ancestor is `L_y(Xq^2)`.
   **FALSIFIED.** The exact polynomial ancestor is `L_y((1-yX)q^2)`; hard multiplication is the
   centered reciprocal operator `X^{-1}-y`.
3. **Conjecture:** fixed-degree arcsine convergence prevents endpoint leakage.
   **FALSIFIED.** Equations (SAHI.25)--(SAHI.27) exhibit a vanishing-weight outlier with a finite
   negative hard limit.
4. **Survivor:** prove a literal completed-Xi no-bounded-super-apex theorem at selected moving
   degree, or prove the sufficient first-Hausdorff flux positivity (SAHI.19). Its input must be
   label-sensitive prime--Gamma structure or another global completed-Xi constraint.

## 8. Scope inside Route U

This theorem sharpens the degenerate/root-sign branch; it does not close all of Route U.

- **Degenerate birth:** negative terminal root signatures have exact finite endpoint ancestry.
  A no-bounded-super-apex theorem would exclude them without assuming full odd-sector positivity.
  Full odd-sector operator admission still requires a form-domain liminf theorem beyond root
  quotients.
- **Simple birth:** the parent radical-jet theorem already shows further root division is theatre.
  The unresolved input remains a new literal prime--Gamma sign or an equivalent global
  completed-Xi law.

Hence (SAHI.19) is a strong sufficient target, not a declared solution and not permission to
replace the source problem by generic Hausdorff moment theory.

## 9. Higher universal principle

Hard-edge parity is endpoint localization of finite moment transport:

\[
\text{finite node }x
\xrightarrow{\ t=yx\ }
\text{moving endpoint }t=1
\xrightarrow{\ u=y(1-t)/t\ }
\text{hard Krein signature}.
\]

The odd terminal factor `r` is the boundary-layer limit of `1-yx`, after removal of the harmless
positive factor `x`. Root sign, first Hausdorff difference, centered reciprocal transport, and odd
Krein inertia are four coordinate shadows of one endpoint flux law.

The reason earlier work stalled is now structural: far-right arcsine theory controls bulk moments,
whereas Route U asks whether a vanishing-weight node crosses a moving endpoint at exactly the scale
that survives reciprocal blow-up.

## 10. Corpus and Lean audit

Corpus search found:

- exact finite positive quadrature through degree `2n` in
  `HTGeometry/FiniteHankelBoundaryQuadrature.lean`;
- signed atomic inertia in `HTGeometry/SignedAtomicMomentInertia.lean`;
- the shifted-Xi moment ODE in `RHTower/SquaredXiCompleteMonotonicity.lean`;
- fixed-degree arcsine recession in `RHTower/XiShiftedHankelFarRightPositiveDefinite.lean`;
- Möbius hard-edge numerator convergence in
  `mass-shifted-hard-edge-hyperbolic-weil-boundary`.

No located card or theorem made the exact identification

\[
u=x^{-1}-y,
\qquad
\operatorname{ind}_-D_n=\#\{yx>1\},
\]

proved bounded super-apex ancestry of negative hard roots, or isolated vanishing-weight endpoint
leakage as the obstruction invisible to arcsine recession. External priority remains unverified.

No Lean declaration is claimed. The finite algebraic ingredients already exist, but formalizing
their abstract composition would add no unconditional completed-Xi theorem. Lean work is deferred
until the literal selected-face estimate (SAHI.19), the minimal leakage exclusion (SAHI.20), or an
equivalent unconditional source theorem is proved. Supplying that estimate as a hypothesis would
repeat theorem laundering.

## Lean status (updated)

Sections 1 and 2 are exact finite theorems, and they are now formal and axiom-clean in
`HTGeometry/HausdorffDifferenceInertia.lean`, on the corpus's Gauss quadrature layer:

    hausdorffDifferenceForm s y q                 `E_y(q) = L((1 - yX) q^2)`
    hausdorffDifferenceForm_eq_gaussSum           **(SAHI.3)**: `E_y(q) = sum_i w_i (1 - y x_i) q(x_i)^2`
                                                  for `deg q <= n`, by Gauss exactness on degree `2n+1`
    lagrangeQuotient s n x0                       the unnormalised Lagrange quotient `p/(X - x0)`
    eval_lagrangeQuotient_eq_zero,
      eval_lagrangeQuotient_self_ne_zero          it vanishes at the other nodes and not at its own,
                                                  the latter from simplicity of the roots
    lagrangeEnergy, lagrangeEnergy_eq,
      lagrangeEnergy_pos                          `gamma_i = w_i l_i(x_i)^2 > 0`
    hausdorffDifferenceForm_lagrangeQuotient      **(SAHI.5)**: `E_y(l_i) = (1 - y x_i) gamma_i`
    hausdorffDifferenceForm_lagrangeQuotient_neg,
      hausdorffDifferenceForm_lagrangeQuotient_pos,
      hausdorffDifferenceForm_nonneg              **(SAHI.4)/(SAHI.11)**: a super-apex node makes its
                                                  own diagonal entry negative, a sub-apex node makes
                                                  it positive, and with no super-apex node the whole
                                                  form is nonnegative
    hardCoordinate, normalizedNode, cayleyNode    the three node coordinates
    one_sub_mul_eq_mul_hardCoordinate             **(SAHI.10)**: `1 - yX = X(X^{-1} - y)`
    hausdorffDifferenceForm_lagrangeQuotient_hard **(SAHI.9)**: `E_y(l_i) = x_i u_i gamma_i`
    hardCoordinate_neg_iff                        **(SAHI.11)**: `u_i < 0` iff `t_i > 1`
    sub_inv_eq_hardCoordinate,
      normalizedNode_sub_one, cayleyNode_sub_one  **(SAHI.12)/(SAHI.13)**: the exact boundary-layer
                                                  scales in the three coordinates

Sections 3-5 remain: the first Hausdorff difference of the actual Route-U normalized moments, the
fixed-degree arcsine recession statement, and the vanishing-Christoffel-weight no-go, all of which
need the literal `xiShiftedReciprocalMoment` normalization rather than a generic moment functional.

### Sections 3 and 4 are formal

    HTGeometry/HausdorffDifferenceInertia.lean (continued)
      momentFunctional_C_mul_X_pow, sq_sum_C_mul_X_pow
      hausdorffDifferenceForm_scaledPoly        **(SAHI.17)**: the quadratic form of the first
                                                Hausdorff-difference matrix of the normalized
                                                moments is `E_y` on the dilated polynomial
      exists_coeff_scaledPoly                   the coefficient dilation `Q(T) -> Q(yX)` is onto
                                                every polynomial of degree at most `n`
      exists_neg_hausdorffDifferenceQuadratic   **(SAHI.18)**: a super-apex node makes the matrix
                                                indefinite, with an explicit witness vector
      hausdorffDifferenceQuadratic_nonneg       **(SAHI.19)**: with no super-apex node the matrix is
                                                positive semidefinite

    HTGeometry/RadialMomentFlux.lean            (axiom-clean, wired, built)
      radialFluxTerm, hasDerivAt_radialFluxTerm the single-index flux law
      radialFlux, hasDerivAt_radialFlux         **(SAHI.23)**: `Phi_c'(y)` is the quadratic form of
                                                the first Hausdorff-difference matrix

    RHTower/XiShiftedSuperApexFlux.lean         (axiom-clean, wired, built)
      xiShiftedMomentTower                      the literal Route-U tower `Re xiShiftedReciprocalMoment`
      hasDerivAt_xiShiftedMomentTower           **(SAHI.21)**: its unconditional first-order law,
                                                from the corpus's `hasDerivAt_re_xiShiftedReciprocalMoment`
      hasDerivAt_xiShiftedRadialFlux            **(SAHI.22)**: the literal first Hausdorff difference
                                                is the derivative of the explicit radial flux
      hasDerivAt_xiShiftedRadialFlux_nonneg,
        exists_neg_xiShiftedRadialFlux_deriv    endpoint admission at a selected mass is exactly the
                                                absence of a quadrature node above the moving apex

Remaining for this card: section 5, the hard-edge ancestry theorem, which needs locally uniform
convergence of the cleared hard polynomials `S_j -> F` and Hurwitz's theorem — the same normal-family
input the hyperbolic-Weil-boundary card needs.  The corpus already has sequential Montel
(`Bottcher/MontelNormal.lean`) and Hurwitz-type zero-locus transfer
(`RHTower/CCMCompactFourierMeanSquareZeroTransfer.lean`).

### Sections 5 and 6

    HTGeometry/HausdorffDifferenceInertia.lean (continued)
      hardCoordinate_eq_normalized       **(SAHI.8)**: `u = y(1-t)/t` in the normalized variable
      hardNode y u, hardCoordinate_hardNode,
        hardNode_pos                     the finite node `1/(y+u)` attached to a hard coordinate,
                                         and that its hard coordinate is `u` again
      normalizedNode_hardNode_gt_one     **(SAHI §5)**: a negative hard coordinate with positive
                                         shifted mass is a super-apex node `t > 1`
      hardCoordinate_outlier,
        tendsto_hardCoordinate_outlier   **(SAHI.27)**: the outlier at `t = 1 + c/y` has hard
                                         coordinate `-c/(1+c/y) -> -c`

    RHTower/XiShiftedSuperApexFlux.lean (continued)
      eventually_exists_hard_root_near   **(SAHI §5)**: the local Hurwitz existence step of the
                                         corpus applied to the cleared hard polynomials — a negative
                                         isolated root of the limit produces approximant roots nearby
      normalizedNode_gt_one_of_near_negative_root
                                         such a root is negative, so its finite node is super-apex;
                                         this is `(SAHI.24)`'s mechanism
      hardCoordinate_of_hard_root        and its hard coordinate is the root itself

Section 6's mechanism is formal: `hausdorffDifferenceForm_lagrangeQuotient_neg` needs only a
positive Christoffel weight, so a vanishing-weight outlier still makes the first Hausdorff
difference negative, and `(SAHI.27)` gives the bounded negative hard limit.  What is not formal is
the packaging of the countermodel as a weakly arcsine-convergent sequence of atomic measures; that
needs the finite-degree positive form (`PositiveMomentFormBelow`) of an explicit perturbed
quadrature, which the corpus's `FiniteGaussQuadrature` layer supports but which has not been built.

## Card status: formalized

Every assertion of sections 1-6 is Lean-proved and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), on the corpus's existing Gauss quadrature layer and
the corpus's own shifted-Xi moment ODE and local Hurwitz step.  Closing additions:

    HTGeometry/HausdorffDifferenceInertia.lean (final)
      cayleyHardArgument, cayleyNode_hardNode  **(SAHI.6)/(SAHI.7)**: the hard substitution, and the
                                               Cayley coordinate of the node attached to `u`
      natDegree_lagrangeCombination_le,
        eval_lagrangeCombination,
        hausdorffDifferenceForm_lagrangeCombination
                                               **(SAHI.4)**: exact diagonalization on the Lagrange
                                               basis of the Gauss nodes, with diagonal entries
                                               `w_i (1 - y x_i)` — the inertia count itself

    HTGeometry/OutlierQuadratureCountermodel.lean  (axiom-clean, wired, built)
      outlierPairing, outlierMoments           the Gauss quadrature perturbed by one atom of weight
                                               `eps` at `t`
      outlierMoments_eq                        **(SAHI.25)**: its moments are the convex combination
                                               up to the exactness degree
      outlierPairing_hausdorff_neg             **(SAHI.26)**: the orthogonal polynomial annihilates
                                               every quadrature node, so only the outlier
                                               contributes and the first Hausdorff difference is
                                               already negative — the Christoffel weight of the
                                               outlier may be arbitrarily small
      tendsto_outlierMoments,
        tendsto_arcsine_outlierMoments         every fixed moment recedes to the unperturbed one, and
                                               with the arcsine (normalized central binomial)
                                               moments to the arcsine moment, so every fixed Hankel
                                               block has the positive-definite arcsine limit

Together with `(SAHI.27)` (`tendsto_hardCoordinate_outlier`) this is exactly the no-go of section 6:
fixed-degree arcsine recession, weak convergence and exact flat quadrature are jointly compatible
with a bounded negative hard-root precursor.

The card moves to stage 3.  What it does **not** claim, and what remains open as the card itself
states, is the survivor target of section 7: a literal completed-Xi no-bounded-super-apex theorem,
or the sufficient first-Hausdorff flux positivity `(SAHI.19)` for the actual selected moving degree.
