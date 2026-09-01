# Gauge-covariant resolution action, composition curvature, and detector-transfer law

- **ID:** ULF-TAFM-5
- **Status:** `[PAPER-PROVED]`; `[FORMALIZED]`; `[BRIDGE]`
- **Lane:** topologically admitted formation mechanics
- **Claim:** resolution cost is not an invariant of a formation morphism alone; the invariant budget
  is the source action of the complete formation--detector path, with local costs transforming as a
  gauge potential and composition loss forming a nonnegative cocycle
- **Failure parent:** morphism-only resolution amplification as intrinsic selector
- **Lean:** abstract gauge/path-action and curvature laws are certified in
  `HTGeometry.TopologicallyAdmittedGaugeAction`; exact source price, finite-factor localization,
  genuine prefix ultrametrics, deterministic pullback equality, and the literal Bernoulli
  Neyman--Pearson detector-transfer countermodel are certified in
  `HTGeometry.TopologicallyAdmittedGaugeActionDetectorTransfer`

## 1. Failure that forces the new law

ULF-TAFM-3 fixes the discrete metric on every finite target and proves that the Lipschitz
amplification of exact tensor formation diverges. That theorem is correct in its declared gauge.
The hostile interpretation

\[
 \text{“kernel amplification alone is the intrinsic formation price”}
 \tag{GRA.1}
\]

is false.

For the Bernoulli prefix formation, the finite prefix map has amplification
\(\theta^{-(d-1)}\) when its output has the discrete metric. Give the same prefix its inherited
ultrametric instead: the prefix map is nonexpansive, while the maximizing detector now has
Lipschitz cost \(\theta^{-(d-1)}\). Nothing mathematical changed. Cost moved across the
formation--observer interface.

The replacement primitive is therefore not one edge norm. It is the complete path action

\[
 \boxed{q_X(K^*f),}
 \tag{GRA.2}
\]

where \(f\) is the final detector and \(q_X\) is a source-predeclared effect gauge. Intermediate
edge costs are local coordinates on this action.

## 2. Gauged effect systems

For each object \(X\), let \(E_X\) be a real vector space of bounded effects containing the
constants. Let

\[
 q_X:E_X\to[0,+\infty)
\]

be a seminorm with constants in its null space. The effect space is chosen so this seminorm is
finite. Examples are Lipschitz effects with the Lipschitz seminorm, finite-variation effects,
Sobolev effects, or a finite source graph-norm domain after quotienting its constant sector.

For a Markov kernel \(K:X\rightsquigarrow Y\), assume pullback sends \(E_Y\) into \(E_X\):

\[
 K^*f(x)=\int_Y f(y)K(x,dy).
\]

Define the operator amplification without dividing by null vectors:

\[
 \alpha_q(K)
 =\inf\left\{a\in[0,+\infty]:
 q_X(K^*f)\le a q_Y(f)\text{ for every }f\in E_Y\right\}.
 \tag{GRA.3}
\]

The infimum is \(+\infty\) if no finite \(a\) works.

For a path

\[
 X_0\xrightsquigarrow{K_1}X_1
 \xrightsquigarrow{K_2}\cdots
 \xrightsquigarrow{K_n}X_n
\]

and a detector \(f\in E_{X_n}\), define its exact source action

\[
 \mathscr A_q(K_1,\ldots,K_n;f)
 =q_{X_0}(K_1^*\cdots K_n^*f).
 \tag{GRA.4}
\]

## 3. Path budget and gauge covariance

### Theorem 3.1 -- compositional resolution budget

Every composable path satisfies

\[
 \boxed{
 \mathscr A_q(K_1,\ldots,K_n;f)
 \le
 \left(\prod_{j=1}^n\alpha_q(K_j)\right)q_{X_n}(f).}
 \tag{GRA.5}
\]

In particular,

\[
 \alpha_q(L\circ K)\le\alpha_q(K)\alpha_q(L).
 \tag{GRA.6}
\]

#### Proof

If an amplification is infinite, the bound is immediate in the extended nonnegative reals. If it
is finite, every \(a>\alpha_q(K)\) is admissible in `(GRA.3)`; letting \(a\downarrow\alpha_q(K)\)
shows that the infimum itself is admissible. Apply this inequality successively to
\(f,K_n^*f,\ldots,K_2^*\cdots K_n^*f\). The two-edge case is `(GRA.6)`. QED.

Now rescale every local gauge by a positive constant:

\[
 q'_{X_j}=c_jq_{X_j},
 \qquad c_j>0.
 \tag{GRA.7}
\]

### Theorem 3.2 -- local gauge transformation law

For every edge,

\[
 \boxed{
 \alpha_{q'}(K_j)=\frac{c_{j-1}}{c_j}\alpha_q(K_j).}
 \tag{GRA.8}
\]

Consequently,

\[
 \boxed{
 \left(\prod_{j=1}^n\alpha_{q'}(K_j)\right)q'_{X_n}(f)
 =c_0
 \left(\prod_{j=1}^n\alpha_q(K_j)\right)q_{X_n}(f).}
 \tag{GRA.9}
\]

If the source gauge is fixed, \(c_0=1\), every intermediate and target rescaling cancels exactly.

#### Proof

The defining inequality for \(\alpha_{q'}(K_j)\) is

\[
 c_{j-1}q_{X_{j-1}}(K_j^*f)
 \le a c_jq_{X_j}(f).
\]

Thus the least admissible \(a\) is \((c_{j-1}/c_j)\alpha_q(K_j)\), including the zero and
infinite cases. Multiplication telescopes, and the final factor \(c_n\) cancels. QED.

Equation `(GRA.8)` is the precise sense in which edge price is a local gauge potential rather than
an invariant scalar. Equation `(GRA.9)` identifies the endpoint-fixed path budget.

## 4. Composition curvature is a cocycle

Assume in this section that all displayed amplifications are finite and strictly positive. Define
edge tension

\[
 t_q(K)=\log\alpha_q(K)
 \tag{GRA.10}
\]

and composition defect

\[
 \kappa_q(K,L)
 =t_q(K)+t_q(L)-t_q(L\circ K).
 \tag{GRA.11}
\]

### Theorem 4.1 -- nonnegative gauge-invariant curvature cocycle

For composable kernels,

\[
 \boxed{\kappa_q(K,L)\ge0.}
 \tag{GRA.12}
\]

It is invariant under every scalar gauge change `(GRA.7)`. For three composable kernels,

\[
 \boxed{
 \kappa_q(K,L)+\kappa_q(L\circ K,M)
 =\kappa_q(L,M)+\kappa_q(K,M\circ L).}
 \tag{GRA.13}
\]

#### Proof

Nonnegativity is the logarithm of `(GRA.6)`. Under `(GRA.8)`, edge tension changes by

\[
 t_{q'}(K_j)=t_q(K_j)+\log c_{j-1}-\log c_j.
\]

The endpoint terms cancel in `(GRA.11)`, proving gauge invariance. Expanding both sides of
`(GRA.13)` gives

\[
 t(K)+t(L)+t(M)-t(M\circ L\circ K)
\]

on each side. QED.

The cocycle is not metaphorical curvature imported from differential geometry. It is the exact
associativity law obeyed by resolution lost when two legal formation steps are compressed into one.
It may vanish even when individual tensions are nonzero; positive curvature means the separate
worst cases cannot be simultaneously realized after composition.

## 5. Information forces path action

Let \(\mu_0,\mu_1\) be probability laws on \(X_0\). For \([0,1]\)-valued source effects define
the gauge price curve

\[
 \mathcal R^q_\mu(r)
 =\inf\left\{q_{X_0}(e):
 \int e\,d(\mu_1-\mu_0)\ge r\right\}.
 \tag{GRA.14}
\]

Suppose the composite path \(K=K_n\circ\cdots\circ K_1\) exactly forms target laws
\(p_0,p_1\) on \(X_n\). Let \(f\in[0,1]\) be any target effect and set

\[
 r=\int f\,d(p_1-p_0).
\]

### Theorem 5.1 -- exact formation--detector action law

\[
 \boxed{
 \mathcal R^q_\mu(r)
 \le
 \mathscr A_q(K_1,\ldots,K_n;f)
 \le
 \left(\prod_{j=1}^n\alpha_q(K_j)\right)q_{X_n}(f).}
 \tag{GRA.15}
\]

#### Proof

Exact pushforward gives

\[
 \int K^*f\,d(\mu_1-\mu_0)=r.
\]

Thus \(K^*f\) is admissible in `(GRA.14)`, proving the first inequality. The second is Theorem
3.1. QED.

For a depth-\(d\) tensor target and a Neyman--Pearson detector \(f_d\),

\[
 r_d=\operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})\ge1-A^d.
\]

Hence

\[
 \boxed{
 \mathcal R^q_\mu(1-A^d)
 \le
 \left(\prod_{j=1}^{n_d}\alpha_q(K_{d,j})\right)
 q_{X_{n_d}}(f_d).}
 \tag{GRA.16}
\]

If the source price diverges, some part of every legal formation--detector path must pay it. For a
path with \(n_d\) edges and finite positive factors,

\[
 \max\{\alpha_q(K_{d,1}),\ldots,\alpha_q(K_{d,n_d}),q(f_d)\}
 \ge
 \mathcal R^q_\mu(1-A^d)^{1/(n_d+1)}.
 \tag{GRA.17}
\]

This is a route-independent localization theorem: divergence cannot disappear under refactoring;
it can only migrate into an edge, the detector, or increasing path length.

## 6. Exact detector--morphism transfer countermodel

Let \(Y=\{0,1\}\), choose \(0<a_0<a_1<1\), and let \(p_i(1)=a_i\). Put

\[
 X=Y^{\mathbb N},
 \qquad
 \mu_i=p_i^{\otimes\mathbb N}.
\]

For \(0<\theta<1\), equip \(X\) with

\[
 d_\theta(x,x')=\theta^{m(x,x')},
\]

where \(m(x,x')\) is the first differing coordinate. Let
\(\pi_d:X\to Y^d\) retain the first \(d\) coordinates.

On each metric space take the effect space of real-valued Lipschitz functions and gauge it by the
Lipschitz seminorm.

For any deterministic map \(T:(X,d_X)\to(Y,d_Y)\), when both effect spaces are the bounded
Lipschitz functions, this pullback amplification is exactly its Lipschitz constant:

\[
 \alpha_{\operatorname{Lip}}(T)=\operatorname{Lip}(T).
 \tag{GRA.17a}
\]

The upper bound is the usual composition estimate
\(\operatorname{Lip}(f\circ T)\le\operatorname{Lip}(T)\operatorname{Lip}(f)\). For the reverse
bound, fix \(x\ne x'\), put \(R=d_Y(T(x),T(x'))\), and take the bounded \(1\)-Lipschitz function
\(f_{x,x'}(y)=\min\{d_Y(y,T(x')),R\}\). Then

\[
 \frac{|f_{x,x'}(T(x))-f_{x,x'}(T(x'))|}{d_X(x,x')}
 =\frac{d_Y(T(x),T(x'))}{d_X(x,x')}.
\]

Taking the supremum over \(x\ne x'\) proves the equality, including the extended value
\(+\infty\).

Give \(Y^d\) first the discrete metric \(\delta_d\). Then

\[
 \boxed{\alpha_{\delta_d}(\pi_d)=\theta^{-(d-1)}.}
 \tag{GRA.18}
\]

Indeed, different prefixes have output distance one, while two inputs first differing at coordinate
\(d-1\) have distance \(\theta^{d-1}\); no smaller input distance can change the prefix.

Now give \(Y^d\) its inherited prefix ultrametric

\[
 \bar d_{\theta,d}(z,z')=\theta^{m(z,z')}.
\]

Then

\[
 \boxed{\alpha_{\bar d_{\theta,d}}(\pi_d)=1.}
 \tag{GRA.19}
\]

The map preserves distance whenever the prefix changes and collapses only tails.

Let \(B_d\) be a Neyman--Pearson event for \(p_0^{\otimes d},p_1^{\otimes d}\), and
\(f_d=\mathbf1_{B_d}\). The likelihood ratio is strictly increasing in the number of ones. It is
less than one on the all-zero word and greater than one on the all-one word. Therefore

\(B_d\) is a nontrivial threshold event. Two words differing only in their last coordinate cross
the threshold, so

\[
 \operatorname{Lip}_{\delta_d}(f_d)=1,
 \qquad
 \operatorname{Lip}_{\bar d_{\theta,d}}(f_d)=\theta^{-(d-1)}.
 \tag{GRA.20}
\]

In both gauges the pulled-back source detector is the same cylinder effect and

\[
 \boxed{
 \operatorname{Lip}_{d_\theta}(f_d\circ\pi_d)
 =\theta^{-(d-1)}.}
 \tag{GRA.21}
\]

Thus the exact budget is allocated in two incompatible-looking but equivalent ways:

\[
 \underbrace{\theta^{-(d-1)}}_{\text{morphism}}
 \underbrace{1}_{\text{detector}}
 =
 \underbrace{1}_{\text{morphism}}
 \underbrace{\theta^{-(d-1)}}_{\text{detector}}.
 \tag{GRA.22}
\]

This explicitly falsifies `(GRA.1)` and proves the positive survivor `(GRA.15)` is the correct
invariant law.

## 7. Cross-organ interpretation

The exact mechanism has four executors:

| organ | local gauge reading |
|---|---|
| packet formation | Markov pullback edge amplification |
| positive decision / Gram reporter | final detector seminorm |
| recurrence / finite observer | cheap visible orbit can transfer cost into unresolved detector scale |
| analytic realization | derivative, variation, graph norm, or normal-family modulus is another effect gauge |
| functional equation | an isometric involution has unit amplification and zero added tension |

Hypertranscendence remains a separate formation-channel-rank coordinate. Resolution action says how
fine a distinction must become; channel rank says how many algebraically independent directions are
needed. Neither determines the other.

## 8. Hostile parent-theory and corpus audit

### 8.1 What is rediscovered

- Operator norm submultiplicativity is classical.
- Dobrushin coefficients are operator norms on effect seminorms; abstract cone versions appear in
  Gaubert--Qu, <https://arxiv.org/abs/1302.5226>.
- Markov/Feller pullback composition is standard.
- The logarithmic defect cocycle is an elementary consequence of associativity.

Accordingly this card is labelled `[BRIDGE]`, not new scientific knowledge.

### 8.2 What changes in the corpus

The exact hostile countermodel `(GRA.18)`--`(GRA.22)` invalidates interpreting the amplification
coordinate of ULF-TAFM-3 without its target detector gauge. The source action lower bound
`(GRA.15)` survives every such reallocation. This changes the RH producer obligation from

\[
 \sup_d\alpha(K_d)<\infty
\]

in an arbitrary finite-target metric to the endpoint-fixed requirement

\[
 \boxed{
 \sup_d
 \left(\prod_j\alpha(K_{d,j})\right)q_d(f_d)<\infty,}
 \tag{GRA.23}
\]

with every gauge and detector fixed by source structure before the desired conclusion is known.

`scripts/formal_tools.py research` found Wasserstein/Dobrushin estimates, observer-fibre current
conservation, finite TV conflict coloring, formation capital, and equicontinuity receivers. It did
not find the exact detector-transfer countermodel or the corpus-facing path law `(GRA.15)`.

### 8.3 Significance attack

The cocycle alone is not an RH producer. It becomes leverage only when a route proves bounded local
factors from source laws while target information forces the left side of `(GRA.16)` to diverge.
Without such bounds, calling \(\kappa\) curvature would be theatre.

## 9. Corrected RH gate

The sufficient architecture is now representation-safe:

1. construct literal, zero-independent arithmetic formation paths;
2. predeclare effect gauges and final decision detectors from source structure;
3. prove the complete path budget `(GRA.23)` is uniformly bounded;
4. prove an off-centre completed error forces a nonneutral tensor target;
5. contradict `(GRA.16)`.

The first open theorem is not “bound one convenient kernel norm.” It is:

`[OPEN CORE]` Prove a source-generated bound on the complete arithmetic formation--detector action
that is invariant under legal refactorization and cannot transfer its divergence into observer
resolution, analytic derivatives, or path length.

## Gates

- [x] 0 -> 1: exact metric-transfer falsifier and stronger invariant
- [x] 1 -> 2: dependency-closed proofs of `(GRA.5)`--`(GRA.22)`
- [x] 2 -> 3: invariant path-action core and exact detector-transfer realization Lean-certified
- [ ] 3 -> 4: publication-ready synthesis and independent significance audit

## Log

- 2026-08-31 -- hostile target-metric audit falsified morphism-only price; proved gauge covariance,
  nonnegative composition cocycle, exact formation--detector action budget, and Bernoulli detector
  transfer.
- 2026-08-31 -- Lean-certified abstract gauge/path-action and curvature-cocycle core; concrete
  detector-transfer countermodel remains paper-only.
- 2026-09-01 -- Lean-certified `(GRA.15)`--`(GRA.22)`: source-price/action sandwich, tensor
  Hellinger admission, exact geometric-mean localization, deterministic bounded-Lipschitz
  pullback equality, genuine binary prefix ultrametrics, exact discrete/inherited prefix costs,
  literal quarter/three-quarter Bernoulli Neyman--Pearson detector, unchanged source-cylinder
  cost, and hypothesis-free half-ratio transfer certificate. Promoted to Stage 3.
