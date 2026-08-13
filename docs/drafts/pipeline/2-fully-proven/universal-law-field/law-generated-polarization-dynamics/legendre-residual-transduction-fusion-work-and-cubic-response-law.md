# Legendre residual transduction, shared-channel fusion, work conservation, and cubic response law

- **ID:** ULF-LGPD-1
- **Stage:** 2-fully-proven
- **Type:** MECHANISM THEOREM / ENDOGENOUS FAILURE-TO-INTERVENTION TRANSDUCTION
- **Parent programme:**
  `../../../1-in-progress/universal-law-field/law-generated-polarization-dynamics/field-programme.md`
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [UNFRAMED PROMOTION NO-GO] [EXACT REPORTER LINEARIZATION]
  [NONPRODUCT CHANNEL FUSION] [WORK CONSERVATION] [CUBIC RESPONSE]
  [COORDINATE-NEUTRAL] [CLASSICAL LEGENDRE/NATURAL-GRADIENT PARENTS]
  [LEAN PENDING] [NOT RH]

## 1. Problem

The whole-corpus Universal Law Field audit repeatedly reaches the same missing arrow:

\[
  \text{exposed response failure}
  \longrightarrow
  \text{next source-admitted intervention}.
  \tag{LRT.1}
\]

A bare residual does not canonically determine a test direction. This card first proves that
impossibility. It then gives the smallest positive mechanism in which a source formation potential
generates reporter, polarization, intervention, work, channel fusion, and the first nonlinear
correction to power decay.

Everything below is finite-dimensional and real. No RH route, zero, Xi specialization, arithmetic
source, or completion theorem is used.

## 2. Unframed transduction no-go

Let `V` be a finite-dimensional real vector space with `dim V >= 2`. The natural action of
`g in GL(V)` on `V*` is

\[
  \alpha\longmapsto (g^{-1})^*\alpha.
  \tag{LRT.2}
\]

### Theorem 2.1 — no nonzero coordinate-free residual promoter

Suppose

\[
  \tau:V^*\setminus\{0\}\longrightarrow V
  \tag{LRT.3}
\]

satisfies

\[
  \tau((g^{-1})^*\alpha)=g\tau(\alpha)
  \qquad
  (g\in GL(V),\ \alpha\ne0).
  \tag{LRT.4}
\]

Then `tau=0`.

#### Proof

Fix nonzero `alpha`. Every element of the stabilizer

\[
  G_\alpha=\{g\in GL(V):(g^{-1})^*\alpha=\alpha\}
  \tag{LRT.5}
\]

fixes `tau(alpha)` by `(LRT.4)`. It suffices to prove that `G_alpha` has no nonzero fixed vector.

Choose `u in V` with `alpha(u)=1` and put `K=ker alpha`, so

\[
  V=\mathbb Ru\oplus K,
  \qquad \dim K\ge1.
  \tag{LRT.6}
\]

Every map

\[
  g_{c,B}(au+k)=au+ac+B k,
  \qquad c\in K,\ B\in GL(K),
  \tag{LRT.7}
\]

lies in `G_alpha`, because `alpha(g_{c,B}(au+k))=a=alpha(au+k)`.

Write a common fixed vector as `x=au+k`. Varying `c` in `(LRT.7)` forces `a=0`. With `a=0`,
varying `B in GL(K)` forces `k=0`. Hence `x=0`. Therefore `tau(alpha)=0`. Since `alpha` was
arbitrary, `tau=0`. QED.

### Corollary 2.2 — source polarization is load-bearing

No nonzero failure-to-intervention rule can be natural under all source reparametrizations when its
only input is a nonzero residual covector. Any nonzero transduction must use additional marked
source structure that reduces the stabilizer: a metric, Hessian, pairing, order, orientation,
integral lattice, or typed partial inverse.

The theorem assumes no regularity of `tau`; continuity, measurability, or linearity cannot repair
the obstruction.

## 3. Legendre source formation

Let `Theta` be a finite-dimensional real vector space and `U subset Theta` a nonempty open convex
set. Let

\[
  A:U\longrightarrow\mathbb R
  \tag{LRT.8}
\]

be `C^3`, with positive-definite Hessian at every point. Write

\[
  \mu(\theta)=dA_\theta\in\Theta^*,
  \qquad
  H_\theta=d^2A_\theta:\Theta\longrightarrow\Theta^*,
  \qquad
  T_\theta=d^3A_\theta.
  \tag{LRT.9}
\]

Assume that `mu` is a `C^2` diffeomorphism from `U` onto an open convex set

\[
  M=\mu(U)\subset\Theta^*.
  \tag{LRT.10}
\]

Let `A*` be the Legendre dual on `M`; then

\[
  dA^*_\eta=\mu^{-1}(\eta),
  \qquad
  d^2A^*_\eta=H_{\mu^{-1}(\eta)}^{-1}.
  \tag{LRT.11}
\]

Fix a target response `m in M`. This target is part of the theorem's marked data; the theorem does
not claim that an arbitrary source supplies one.

For `theta in U`, define residual, promoted intervention, and power

\[
  e(\theta)=m-\mu(\theta),
  \qquad
  X_m(\theta)=H_\theta^{-1}e(\theta),
  \qquad
  P(\theta)=e(\theta)(X_m(\theta)).
  \tag{LRT.12}
\]

Positive definiteness gives

\[
  P(\theta)=H_\theta(X_m(\theta),X_m(\theta))\ge0,
  \tag{LRT.13}
\]

with equality exactly when `theta=theta_*:=mu^{-1}(m)`.

## 4. Exact residual-transduction flow

For initial `theta_0 in U`, define

\[
  \eta(t)=m+e^{-t}(\mu(\theta_0)-m).
  \tag{LRT.14}
\]

Convexity of `M` gives `eta(t) in M` for every `t>=0`. Put

\[
  \theta(t)=\mu^{-1}(\eta(t)).
  \tag{LRT.15}
\]

### Theorem 4.1 — global solution and exact reporter linearization

The curve `(LRT.15)` is the unique `C^1` solution of

\[
  \dot\theta(t)=X_m(\theta(t)),
  \qquad \theta(0)=\theta_0.
  \tag{LRT.16}
\]

Its reporter and residual satisfy

\[
  \boxed{
  \mu(\theta(t))=m+e^{-t}(\mu(\theta_0)-m),
  \qquad
  e(\theta(t))=e^{-t}e(\theta_0).}
  \tag{LRT.17}
\]

In particular `theta(t) -> theta_*` as `t -> infinity`.

#### Proof

The first equation in `(LRT.17)` is `(LRT.14)--(LRT.15)`. Differentiate:

\[
  H_{\theta(t)}\dot\theta(t)
  =\dot\eta(t)
  =m-\eta(t)
  =m-\mu(\theta(t))
  =e(\theta(t)).
  \tag{LRT.18}
\]

Invert `H_theta` to obtain `(LRT.16)`. Conversely every solution of `(LRT.16)` obeys

\[
  \frac d{dt}\mu(\theta(t))
  =H_{\theta(t)}\dot\theta(t)
  =m-\mu(\theta(t)).
  \tag{LRT.19}
\]

The linear initial-value problem `(LRT.19)` has the unique solution `(LRT.17)`, so `theta` is
unique because `mu` is injective. Finally `eta(t)->m`, and continuity of `mu^{-1}` gives
`theta(t)->theta_*`. QED.

### Interpretation

The intervention in source coordinates is state-dependent and nonlinear. The complete response
trajectory is nevertheless an exact straight contraction in mean coordinates. The next legal
intervention is generated by the same source potential that generated the reporter.

## 5. Exact work conservation

For `eta in M`, define the directed dual Bregman work

\[
  W(\eta)=D_{A^*}(m,\eta)
  :=A^*(m)-A^*(\eta)-dA^*_\eta(m-\eta).
  \tag{LRT.20}
\]

### Theorem 5.1 — work is the integrated polarization power

Along `(LRT.15)`,

\[
  \boxed{
  \frac d{dt}W(\mu(\theta(t)))
  =-e(\theta(t))\big(H_{\theta(t)}^{-1}e(\theta(t))\big)
  =-P(\theta(t)).}
  \tag{LRT.21}
\]

Consequently, for every `T>=0`,

\[
  \boxed{
  W(\mu(\theta_0))-W(\mu(\theta(T)))
  =\int_0^T P(\theta(t))\,dt.}
  \tag{LRT.22}
\]

Letting `T->infinity`,

\[
  \boxed{
  W(\mu(\theta_0))
  =\int_0^\infty P(\theta(t))\,dt.}
  \tag{LRT.23}
\]

#### Proof

For a variation `z in Theta*`, differentiation of `(LRT.20)` gives

\[
  dW_\eta(z)
  =-d^2A^*_\eta(z,m-\eta).
  \tag{LRT.24}
\]

Along the flow, `dot eta=m-eta`. Using `(LRT.11)`,

\[
\begin{aligned}
  \dot W
  &=-d^2A^*_\eta(m-\eta,m-\eta)\\
  &=-e(H_\theta^{-1}e)\\
  &=-P.
\end{aligned}
  \tag{LRT.25}
\]

Integrating proves `(LRT.22)`. Since `eta(T)->m`, continuity gives `W(eta(T))->W(m)=0`, proving
`(LRT.23)`. QED.

### Corollary 5.2 — unique selection inside the Legendre chart

`theta_*` is the unique stationary point, the unique zero-work state, and the global limit of every
flow trajectory. This is a genuine finite selection theorem, conditional on the source-supplied
potential and target.

## 6. Shared-channel fusion law

Let `I` be a finite nonempty channel set. For every `i in I`, let

\[
  A_i:U\to\mathbb R
  \tag{LRT.26}
\]

be `C^3` with positive-semidefinite Hessian `H_i(theta)`. Assume

\[
  H(\theta):=\sum_{i\in I}H_i(\theta)
  \tag{LRT.27}
\]

is positive definite for every `theta`. Put

\[
  A=\sum_i A_i,
  \qquad \mu_i=dA_i,
  \qquad \mu=\sum_i\mu_i,
  \qquad T=\sum_i d^3A_i.
  \tag{LRT.28}
\]

Fix channel targets `m_i in Theta*` whose sum `m=sum_i m_i` lies in `mu(U)`. Define

\[
  e_i=m_i-\mu_i(\theta),
  \qquad e=\sum_i e_i=m-\mu(\theta),
  \qquad v=H^{-1}e,
  \qquad j_i=H_i v.
  \tag{LRT.29}
\]

Run the fused source flow `dot theta=v`.

### Theorem 6.1 — nonproduct fusion and exact current conservation

Along the fused flow,

\[
  \boxed{
  \dot e_i=-j_i,
  \qquad
  \sum_i j_i=e,
  \qquad
  \dot e=-e.}
  \tag{LRT.30}
\]

The total source power decomposes without cancellation:

\[
  \boxed{
  e(v)=H(v,v)=\sum_i H_i(v,v),
  \qquad H_i(v,v)\ge0.}
  \tag{LRT.31}
\]

The fused intervention is generally not the sum of local interventions:

\[
  \boxed{
  H^{-1}\sum_i e_i
  \ne
  \sum_iH_i^{-1}e_i}
  \tag{LRT.32}
\]

when the local inverses exist. Thus `(LRT.30)--(LRT.31)` are a genuine shared-source fusion law,
not product packaging.

#### Proof

Differentiate each local residual:

\[
  \dot e_i=-H_i\dot\theta=-H_i v=-j_i.
  \tag{LRT.33}
\]

Summing `(LRT.29)` and using `Hv=e` gives

\[
  \sum_i j_i=\sum_iH_iv=Hv=e.
  \tag{LRT.34}
\]

Summing `(LRT.33)` proves `dot e=-e`. Finally

\[
  e(v)=(Hv)(v)=H(v,v)=\sum_iH_i(v,v),
  \tag{LRT.35}
\]

and every summand is nonnegative. Formula `(LRT.32)` fails already for scalar channels: with
`H_1=H_2=1` and `e_1=e_2=1`, the fused intervention is `1`, while the sum of local interventions is
`2`. QED.

### Corollary 6.2 — three-organ fusion template

For three channels, the current triangle

\[
  j_1+j_2+j_3=e
  \tag{LRT.36}
\]

and positive power identity

\[
  e(v)=H_1(v,v)+H_2(v,v)+H_3(v,v)
  \tag{LRT.37}
\]

are exact. A proposed three-organ realization is valid only if all three Hessians are variations
of source-defined channel potentials on one intervention space. Merely placing three positive
matrices in a sum does not establish source fusion.

## 7. Fourth-order prediction from third response

Let `theta(t)` be the one-potential flow and abbreviate

\[
  e=e(\theta(t)),\quad
  H=H_{\theta(t)},\quad
  v=H^{-1}e,\quad
  T=T_{\theta(t)},\quad
  P=e(v)=H(v,v).
  \tag{LRT.38}
\]

### Theorem 7.1 — cubic response controls correction-power acceleration

Along the flow,

\[
  \boxed{
  \dot P=-2P-T(v,v,v).}
  \tag{LRT.39}
\]

Equivalently,

\[
  \boxed{
  \frac d{dt}(e^{2t}P(t))
  =-e^{2t}T_{\theta(t)}(v(t),v(t),v(t)).}
  \tag{LRT.40}
\]

#### Proof

Theorem 4.1 gives `dot e=-e`. Differentiating `H(theta(t))` gives the bilinear form

\[
  \dot H=T(v,\cdot,\cdot).
  \tag{LRT.41}
\]

Since

\[
  \frac d{dt}H^{-1}=-H^{-1}\dot H H^{-1},
  \tag{LRT.42}
\]

differentiate `P=e(H^{-1}e)`:

\[
\begin{aligned}
  \dot P
  &=\dot e(H^{-1}e)+e(H^{-1}\dot e)
    -e(H^{-1}\dot H H^{-1}e)\\
  &=-2P-T(v,v,v).
\end{aligned}
  \tag{LRT.43}
\]

Multiplying by `e^{2t}` proves `(LRT.40)`. QED.

### Consequences

1. If `A` is quadratic, `T=0` and `P(t)=e^{-2t}P(0)` exactly.
2. If `T(v,v,v)>=0` along a trajectory, `e^{2t}P(t)` is nonincreasing.
3. If `T(v,v,v)<=0`, the scaled power is nondecreasing.
4. No unsigned Hessian/Gram observer can infer this sign without retaining the third response.

This is the theorem predicted in a fourth organ by the residual-fusion mechanism: response
chirality controls the first nonquadratic correction to selection power.

## 8. Coordinate and affine-gauge neutrality

Let `W` be another finite-dimensional real vector space and `g:W->Theta` a linear isomorphism.
Define

\[
  \widetilde A(w)=A(gw),
  \qquad
  \widetilde m=g^*m.
  \tag{LRT.44}
\]

Then

\[
\begin{aligned}
  \widetilde\mu(w)&=g^*\mu(gw),\\
  \widetilde H_w&=g^*H_{gw}g,\\
  \widetilde e(w)&=g^*e(gw),\\
  \widetilde X_{\widetilde m}(w)&=g^{-1}X_m(gw).
\end{aligned}
  \tag{LRT.45}
\]

### Theorem 8.1 — reparametrization is information-neutral

If `w(t)` is the transformed flow, then `g w(t)=theta(t)` for corresponding initial conditions.
Reporter residuals, work, and power satisfy

\[
  \widetilde e(t)=g^*e(t),
  \qquad
  \widetilde W(t)=W(t),
  \qquad
  \widetilde P(t)=P(t).
  \tag{LRT.46}
\]

#### Proof

The chain rule gives the first three identities in `(LRT.45)`. Since

\[
  (g^*Hg)^{-1}g^*=g^{-1}H^{-1},
  \tag{LRT.47}
\]

the fourth follows. Therefore transformed trajectories correspond. Pairing invariance gives

\[
  (g^*e)(g^{-1}v)=e(v),
  \tag{LRT.48}
\]

so power is unchanged. Legendre duality under linear isomorphism gives the same Bregman work. QED.

Now let `ell in Theta*` and `c in R`, and put

\[
  A'(\theta)=A(\theta)+\ell(\theta)+c,
  \qquad m'=m+\ell.
  \tag{LRT.49}
\]

Then

\[
  \mu'=\mu+\ell,
  \quad H'=H,
  \quad e'=e,
  \quad X_{m'}'=X_m,
  \quad P'=P,
  \quad W'=W.
  \tag{LRT.50}
\]

### Corollary 8.2 — functional-equation neutrality

Any functional equation acting on the formation potential by a source reparametrization followed
by an affine gauge lifts through the residual-transduction mechanism and preserves its information
and work exactly, provided the target transforms with the reporter. Such a symmetry is a gauge of
the mechanism, not a selector.

## 9. Properness and cofinal boundary

### Theorem 9.1 — finite Legendre properness

Assume the dual work

\[
  \eta\longmapsto D_{A^*}(m,\eta)
  \tag{LRT.51}
\]

has compact sublevel sets in `M`. Then every bounded-work subset of `U` is compact, every flow
trajectory is contained in one compact subset of `U`, and `theta_*` is the unique attainable
zero-work state.

#### Proof

For `R>=0`, the `R`-sublevel in `M` is compact by hypothesis. Its inverse image under the
homeomorphism `mu^{-1}:M->U` is compact. Theorem 5.1 makes work nonincreasing along trajectories,
so the trajectory from `theta_0` stays in the sublevel of height `W(mu(theta_0))`. Uniqueness of the
zero follows from strict convexity of `A*`. QED.

### Exact cofinal warning

Finite strict convexity does not imply uniform cofinal properness. For

\[
  A_N(x)=\frac{x^2}{2N},
  \qquad m=1,
  \qquad \theta_0=0,
  \tag{LRT.52}
\]

the Hessian is `H_N=1/N`, the initial residual is `1`, and the generated initial intervention is

\[
  X_m^{(N)}(0)=N.
  \tag{LRT.53}
\]

Every finite reporter trajectory is the same contraction `mu_N(t)=1-e^{-t}`, but source velocity
and source endpoint `theta_*^{(N)}=N` escape. Thus global selection needs a uniform inverse-
polarization/properness theorem, not finite positivity.

## 10. Hostile boundaries

1. **Marked target is essential.** The theorem does not manufacture `m`. Choosing `m` after seeing
   an RH endpoint is circular.
2. **Positive definiteness is essential.** A degenerate Hessian gives a family or absence of
   promoters; a pseudoinverse adds a doctrine choice.
3. **Total residual can hide local mismatch.** In the fused theorem, `sum_i e_i=0` does not imply
   every `e_i=0`.
4. **Observation need not preserve native promotion.** A linear observer always sees
   `q dot e=-q e`, but it inherits a natural-gradient promoter only under an additional sufficient-
   statistic or Riemannian-submersion theorem.
5. **Cubic sign is not positive data.** Positive Hessian formation supplies no universal sign for
   `T(v,v,v)`.
6. **Discrete updates are different.** A finite Euler step can leave `U` or increase work.
7. **Infinite-dimensional inversion is not covered.** Closed range, domains, compactness, and
   admission become separate load-bearing laws.
8. **No RH consequence is claimed.** A literal source must still generate the target and prove
   cofinal properness on the RH displacement sector.

## 11. Parent and significance audit

Hessian Riemannian flows, Legendre duality, Bregman divergences, Fisher natural gradient, mirror
descent, Newton flows, and exponential-family information geometry are classical parent
mathematics. The theorem does not claim a new optimizer.

The exact corpus contribution is the coupling:

\[
  \boxed{\text{source formation}}
  \to\boxed{\text{reporter}}
  \to\boxed{\text{typed residual}}
  \to\boxed{\text{source-generated polarization}}
  \to\boxed{\text{next intervention}}
  \to\boxed{\text{fused currents and work}}.
  \tag{LRT.54}
\]

It closes the previously supplied-promoter gap at finite dimension and exposes the exact remaining
RH gate: source production of the target and uniform cofinal inverse-polarization properness.

## 12. Formalization status

Paper proof is dependency-closed. No Lean file was written in this research pass. A later
formalization must be placed only under the Universal Law Field Lean namespace and must first close
the finite-dimensional differential/Legendre API without axioms or project premises.

## Log

- 2026-08-13 — unframed equivariant transduction no-go proved.
- 2026-08-13 — exact Legendre residual flow, work identity, shared-channel fusion, cubic response,
  coordinate neutrality, finite properness, and cofinal escape countermodel closed on paper.
