# Moving-center Padé worldline and exact source-error law

- **ID:** `mass-shifted-moving-center-pade-worldline-law`
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Route:** U, finite positive chamber preceding the hard edge
- **Type:** THEOREM + EXACT NO-GO (paper)
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [EXTERNAL NOVELTY UNVERIFIED] [LEAN NOT STARTED]`
- **Depends on:** shifted-Xi moment ODE and positive Gauss quadrature
- **Statement:** The canonical degree-`n` Padé resolvent obeys an exact moving-center rational
  flow with one numerator monomial. Every Padé pole is a transverse zero of a literal
  completed-Xi error source, and its residue obeys an exact worldline law. The flow is generic and
  therefore cannot supply Route U's missing absolute anchor.

## 1. Setup

Let

\[
 L_y(X^k)=s_y(k),
 \qquad s_y'(k)=-(k+1)s_y(k+1),                            \tag{MPW.1}
\]

and fix a degree `n` positive Hankel chamber.  Let `p_y` be the monic degree-`n` orthogonal
polynomial, with roots `x_i`, Gauss weights `omega_i`, and norm

\[
 h_n=L_y(p_y^2)>0.
\]

Put

\[
 u_i=x_i^{-1}-y,
 \qquad a_i=-u_i=y-x_i^{-1},
 \qquad \rho_i={\omega_i\over x_i}>0.                     \tag{MPW.2}
\]

For an absolute target mass `Y`, write `Delta=Y-y` and define

\[
 R_y(Y)=\sum_{i=1}^n{\omega_i\over1+\Delta x_i}
       =\sum_{i=1}^n{\rho_i\over Y-a_i},                  \tag{MPW.3}
\]

\[
 D_y(Y)=\prod_{i=1}^n(1+\Delta x_i).                      \tag{MPW.4}
\]

## 2. Exact moving-center equation `[PAPER-PROVED]`

At fixed absolute `Y`, throughout the chamber,

\[
 \boxed{\qquad
 \partial_y R_y(Y)
 ={2n h_n(y)(Y-y)^{2n-1}\over D_y(Y)^2}.
 \qquad}                                                   \tag{MPW.5}
\]

### Proof

Let

\[
 q_k(y)=\sum_i\omega_i(y)x_i(y)^k.
\]

Gauss exactness gives `q_k=s_y(k)` for `0<=k<=2n-1`, while

\[
 s_y(2n)-q_{2n}=h_n.                                      \tag{MPW.6}
\]

Near `Y=y`,

\[
 R_y(y+\Delta)=\sum_{k\ge0}(-1)^kq_k(y)\Delta^k.
\]

Differentiation at fixed `Y` is `partial_y|Delta-partial_Delta`.  By `(MPW.1)`, every
coefficient through `Delta^(2n-2)` cancels.  The coefficient of `Delta^(2n-1)` is

\[
 2n(s_y(2n)-q_{2n})=2nh_n.                                \tag{MPW.7}
\]

On the other hand, `R_y=N_y/D_y`, with `deg_Y N_y<=n-1` and `deg_Y D_y=n`.  Therefore
`partial_y R_y` has denominator `D_y^2` and numerator of degree at most `2n-1`.  Equation
`(MPW.7)` says that numerator has a zero of order `2n-1` at `Y=y`; it must be exactly
`2nh_n(Y-y)^(2n-1)`.  This proves `(MPW.5)`.

The individual node velocity from the parent card follows by comparing double-pole coefficients:

\[
 a_i'=-{2nh_n\over x_i^2\gamma_i}<0,
 \qquad
 \gamma_i=L_y\!\left(\left({p_y\over X-x_i}\right)^2\right).
                                                                    \tag{MPW.8}
\]

Thus every real Padé pole moves strictly left while the positive chamber persists.

## 3. Literal source-error factor `[PAPER-PROVED]`

Let

\[
 G(Y)=s_Y(0)
\]

be the literal completed-Xi resolvent, and define

\[
 \mathcal H_y(Y)
 =L_y\!\left({p_y(X)^2\over1+(Y-y)X}\right).              \tag{MPW.9}
\]

Where both sides are initially analytic, and hence by continuation away from poles,

\[
 \boxed{\qquad
 G(Y)-R_y(Y)
 ={(Y-y)^{2n}\mathcal H_y(Y)\over D_y(Y)^2}.
 \qquad}                                                   \tag{MPW.10}
\]

Indeed, with `z=-1/(Y-y)`, the standard orthogonal-polynomial identity is

\[
 L_y\!\left({1\over z-X}\right)
 -\sum_i{\omega_i\over z-x_i}
 ={1\over p_y(z)^2}
 L_y\!\left({p_y(X)^2\over z-X}\right).                 \tag{MPW.11}
\]

Multiplication by `z`, together with

\[
 p_y(z)^2=(Y-y)^{-2n}D_y(Y)^2,
\]

gives `(MPW.10)`.

Every Padé pole is a simple, oriented zero of the literal source factor:

\[
 \boxed{\qquad
 \mathcal H_y(a_i)=0,
 \qquad
 \mathcal H_y'(a_i)=-x_i^3\gamma_i<0.
 \qquad}                                                   \tag{MPW.12}
\]

For the first identity, at `Y=a_i` one has

\[
 {p_y(X)^2\over1+(a_i-y)X}
 =-x_i(X-x_i)\left({p_y(X)\over X-x_i}\right)^2,
\]

a polynomial of degree `2n-1` whose Gauss values all vanish.  Differentiating `(MPW.9)` and using
Gauss exactness again gives

\[
 \mathcal H_y'(a_i)
 =-x_i^2L_y\!\left(X\left({p_y\over X-x_i}\right)^2\right)
 =-x_i^3\gamma_i.
\]

The Laurent coefficient of `(MPW.10)` at `a_i` is therefore `-rho_i`, exactly cancelling the
Padé pole against the analytic literal resolvent.  Analyticity does not remove the pole; it forces
the source error to carry the opposite pole through one transverse numerator zero.

## 4. Residue transport `[PAPER-PROVED]`

Comparison of simple-pole coefficients in `(MPW.5)` gives

\[
 \boxed{\qquad
 {\rho_i'\over\rho_i}
 =a_i'\left(
 {2n-1\over a_i-y}
 -2\sum_{k\ne i}{1\over a_i-a_k}
 \right).
 \qquad}                                                   \tag{MPW.13}
\]

At infinity, comparison of the `Y^(-1)` coefficients gives the collective law

\[
 \boxed{\qquad
 {d\over dy}\sum_i\rho_i
 ={2nh_n\over(\prod_i x_i)^2}>0.
 \qquad}                                                   \tag{MPW.14}
\]

Thus pole positions move monotonically left while total absolute residue grows.  Positive-axis
mass can disappear only by a pole crossing the origin or by a singular chamber limit; it is not
erased by cancellation between positive residues.

## 5. Exact no-go and positive survivor

Equation `(MPW.5)` uses only `(MPW.1)`, finite Gauss exactness, and positivity of the current
chamber.  The corpus's three-atom positive resolvent-flow countermodel has all those properties
and still reverses the required frozen-source sign.  Therefore the moving-center equation cannot
prove positive-axis local boundedness or endpoint anchoring.

Its strongest nontrivial survivor is `(MPW.10)--(MPW.12)`: each forbidden pole is a transverse
zero of the literal two-mass completed-Xi source `mathcal H_y`.  A successful proof must control
that source factor, its hard limit, or the equivalent hyperbolic capacity from
`mass-shifted-hard-edge-hyperbolic-source-capacity`.  Integrating the generic center flow merely
repackages the same pole worldline.

## 6. Absolute-divisor high-moment no-go `[PAPER-PROVED]`

The most direct source-specific attempt is to dominate a super-apex Gauss weight by the highest
exact moment.  It fails sharply at the Route-U scale.

Let

\[
 \lambda_q(y)={1\over y+\zeta_q},
 \qquad \zeta_q=\text{the squared centered Xi node}.       \tag{MPW.15}
\]

The completed endpoint gap gives `Re zeta_q>81/4`, hence `|lambda_q(y)|<1/y`.  If `a_i` is a
positive-axis Padé pole and `x_i=(y-a_i)^(-1)`, positivity of the Gauss weights and exactness at
degree `2n-2` give

\[
 \begin{aligned}
 \rho_i={\omega_i\over x_i}
 &\le {s_y(2n-2)\over x_i^{2n-1}}\\
 &\le \sum_q
 \left|{y-a_i\over y+\zeta_q}\right|^{2n-1}.
 \end{aligned}                                             \tag{MPW.16}
\]

Every sum in `(MPW.16)` is finite.  Nevertheless, if

\[
 y_j\longrightarrow\infty,
 \qquad {n_j\over y_j}\longrightarrow0,
 \qquad a_{j,i}\longrightarrow a\in\mathbb R,             \tag{MPW.17}
\]

then

\[
 \boxed{\qquad
 \liminf_{j\to\infty}
 \sum_q\left|{y_j-a_{j,i}\over y_j+\zeta_q}\right|^{2n_j-1}
 =+\infty.
 \qquad}                                                   \tag{MPW.18}
\]

Indeed, for every fixed divisor copy `q`,

\[
 (2n_j-1)\left[
 \log\left|1-{a_{j,i}\over y_j}\right|
 -\log\left|1+{\zeta_q\over y_j}\right|
 \right]\longrightarrow0,                                \tag{MPW.19}
\]

so its summand tends to one.  Restricting to any fixed finite set of `M` divisor copies gives
liminf at least `M`; then let `M` grow.  Route U has `n_j asymp sqrt(y_j)`, so `(MPW.17)` applies.

Thus literal spectral-radius separation is real but asymptotically too thin for the available
moment order.  Taking absolute values destroys exactly the collective phase/off-diagonal
information selected by the hard-edge prime--Gamma limit.  No highest-moment, absolute-divisor,
or norm-majorant argument can prove Padé-atom vanishing at this scale.

## 7. Conjecture -> proof/failure -> pivot

1. **Conjecture:** current Padé center variation has uncontrolled rational complexity.
   **FALSIFIED.** It collapses to the one-monomial law `(MPW.5)`.
2. **Conjecture:** this Loewner-type law anchors every pole to the analytic side.
   **FALSIFIED AS AN INFERENCE.** Its sign is only relative to the moving center, and generic
   positive moment flows retain positive-axis pole worldlines.
3. **Conjecture:** analyticity makes a spurious pole disappear from the exact error.
   **FALSIFIED.** The literal source factor has the transverse zero `(MPW.12)`, leaving the exact
   opposite simple pole in `(MPW.10)`.
4. **Positive survivor:** pole velocity, residue transport, and source-error cancellation are one
   exact worldline law.  The remaining discriminator is the literal source capacity, not another
   rational-flow estimate.
5. **Conjecture:** the strict source radius `|lambda_q(y)|<1/y` suppresses every super-apex
   residue through the highest exact moment.  **FALSIFIED AT THE CRITICAL SCALE.**  The resulting
   literal bound diverges by `(MPW.18)` because `n/y->0` leaves every fixed divisor copy
   unsuppressed.  Any successful estimate must retain phase or common-operator correlation.

## 8. Literature and Lean audit

Gauss quadrature error formulas, orthogonal-polynomial Padé denominators, and deformation equations
for orthogonal polynomials are classical parents.  Targeted searches found no exact statement of
`(MPW.5)` or `(MPW.12)` for a moving confluent center under the shifted-moment ODE.  Because the
derivation is short and generic, this card is labeled `[BRIDGE]`, not candidate new scientific
knowledge.  Its Route-U value is the exact no-go and the source-error factor handed to the
capacity theorem.

No Lean declaration is claimed.  Formalizing this generic rational identity before a literal
source bound would not close a Route-U obstruction and would repeat infrastructure-first work.

## Log

- 2026-08-11 — proved the exact moving-center equation, source-error factor, transverse source
  zero, individual residue ODE, and total-residue growth; generic flow closed as an anchoring
  mechanism.
- 2026-08-11 — proved that the literal highest-moment absolute-divisor bound diverges throughout
  the Route-U critical scale; spectral-radius domination closed as a residue-vanishing mechanism.

## Lean status (updated)

The static half of section 3 — the orthogonal-polynomial identity `(MPW.11)` and the transversal
vanishing `(MPW.12)` — is now formal and axiom-clean in
`HTGeometry/GaussResolventError.lean`, on top of the corpus's existing Gauss quadrature layer
(`HTGeometry/GaussQuadrature.lean`, `HTGeometry/FiniteGaussQuadrature.lean`):

    dividedSquare p z                       the polynomial `(p(z)² - p(X)²)/(X - z)`
    dividedSquare_mul, eval_dividedSquare   it really is that quotient
    degree_dividedSquare_lt                 its degree is `2n+1`, so Gauss exactness applies
    momentFunctional_dividedSquare          `L(dividedSquare) = p(z)²·Σ ω_i/(x_i - z)`
    gaussSum_resolvent_eq                   **(MPW.11)**: the quadrature resolvent is
                                            `L(dividedSquare)/p(z)²`, i.e. the `[n/n+1]` Padé
                                            approximant of the moment resolvent
    nodeCofactor, nodeResidual              the removable form `p(X)²/(x₀ - X) = -(X - x₀)(p/(X-x₀))²`
    eval_nodeResidual_mul                   it really is that quotient
    momentFunctional_nodeResidual_eq_zero   **(MPW.12)**: the residual source factor vanishes at
                                            every Gauss node, because away from the node the
                                            cofactor vanishes and at the node the linear factor does

What is still missing is the moving half: the `y`-derivative statements `(MPW.5)`, `(MPW.8)`,
`(MPW.13)` and `(MPW.14)`.  Those need the moment ODE `s_y'(k) = -(k+1)s_y(k+1)` together with
differentiability of the Gauss nodes and weights in `y`, which is an implicit-function argument on
the orthogonal polynomial's simple roots.
