# Resolution-price formation conservation, prefix localization, and Feller escape law

- **ID:** ULF-TAFM-3
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ULF-TAFM-2 compact-effect escape; full-frontier cofinal equicontinuity gate;
  hostile test of Feller admission as a selector
- **Statement:** Exact formation conserves target decision contrast while forcing the formation
  kernel's Lipschitz pullback amplification to pay a source-defined resolution price; that price is
  compositional, diverges at perfect separation for full-support laws, admits an exact finite-prefix
  lower bound on product sources, and can diverge exponentially in an all-depth Feller formation.
- **Status:** `[PROVED HERE] [DEPENDENCY-CLOSED ON PAPER] [UNCONDITIONAL] [ROUTE-INDEPENDENT]`
  `[EXACT COUNTERMODEL] [FUNCTIONAL-EQUATION NEUTRAL] [BRIDGE/CORPUS FUSION]`
  `[NOT RH] [LEAN OPEN: CURRENT RESEARCH PHASE FORBIDS LEAN WRITES/BUILDS]`

## 1. Result and field correction

ULF-TAFM-2 proves a qualitative alternative: unbounded nonneutral exact formation forces escape
from every compact source-effect family. That statement leaves two defects.

1. Compact versus noncompact is binary and does not measure how much source resolution a formation
   spends.
2. It can be misread as saying Feller continuity itself blocks all-depth formation.

The second claim is false. The correct primitive is a price attached to a **morphism**, not only a
topology attached to its source:

\[
 \boxed{
 \text{formation depth creates target decision contrast, and the pullback morphism must pay for
 it in source resolution.}}
 \tag{RP.1}
\]

The price composes under kernels. This turns the compactness obstruction into a quantitative
formation law and gives an explicit hostile countermodel in which every finite formation is
deterministic Feller but its price grows exponentially.

## 2. Source resolution price

Let \((X,d_X)\) be a nonempty compact metric space and let \(\mu_0,\mu_1\) be Borel probability
measures on \(X\). For an effect \(e:X\to[0,1]\), put

\[
 \Delta_\mu(e)=\int_X e\,d\mu_1-\int_Xe\,d\mu_0.
 \tag{RP.2}
\]

Write \(\operatorname{Lip}(e)\in[0,+\infty]\) for its least global Lipschitz constant. For
\(r\in[0,1]\), define the **resolution price curve**

\[
 \mathcal R_\mu(r)
 =\inf\left\{\operatorname{Lip}(e):
       e:X\to[0,1],\ \Delta_\mu(e)\ge r\right\},
 \tag{RP.3}
\]

with \(\inf\varnothing=+\infty\). Finite-price effects are automatically continuous.

### Theorem 2.1 -- price properness and singular exhaustion

The curve \(\mathcal R_\mu\) is nondecreasing and \(\mathcal R_\mu(0)=0\). If both laws have full
topological support, then

\[
 \boxed{
 \mathcal R_\mu(1)=+\infty,
 \qquad
 \lim_{r\uparrow1}\mathcal R_\mu(r)=+\infty.}
 \tag{RP.4}
\]

If, in addition, \(\mu_0\perp\mu_1\), then

\[
 \boxed{
 \mathcal R_\mu(r)<+\infty\quad(0\le r<1),
 \qquad
 \mathcal R_\mu(1)=+\infty.}
 \tag{RP.5}
\]

Thus a singular full-support pair has every finite confidence level at finite resolution, but its
perfect measurable separator lies at infinite resolution.

#### Proof

Monotonicity follows because the admissible effect set decreases as \(r\) increases. Constant
effects give \(\mathcal R_\mu(0)=0\).

If a continuous \([0,1]\)-valued effect had contrast one, then it would have integral one under
\(\mu_1\) and zero under \(\mu_0\). Full support would force it to be simultaneously the constant
one and the constant zero. Hence \(\mathcal R_\mu(1)=+\infty\).

Suppose the limit assertion failed. Then there would be \(r_n\uparrow1\), one finite \(M\), and
effects \(e_n\) with

\[
 0\le e_n\le1,
 \qquad \operatorname{Lip}(e_n)\le M+1,
 \qquad \Delta_\mu(e_n)\ge r_n.
\]

Arzela--Ascoli gives a uniformly convergent subsequence. Its limit is a continuous
\([0,1]\)-valued effect with contrast one, contradiction.

Now assume mutual singularity. Choose a Borel separator \(S\) with
\(\mu_1(S)=1\) and \(\mu_0(S)=0\). Given \(\varepsilon>0\), Radon inner regularity supplies
disjoint compact sets

\[
 F\subset S,\qquad G\subset S^c,
 \qquad \mu_1(F)>1-\varepsilon,
 \qquad \mu_0(G)>1-\varepsilon.
\]

Their distance \(\delta=d(F,G)\) is positive. The effect

\[
 e(x)=\min\{1,d(x,G)/\delta\}
 \tag{RP.6}
\]

is \(\delta^{-1}\)-Lipschitz, equals one on \(F\), and equals zero on \(G\). Therefore

\[
 \Delta_\mu(e)>1-2\varepsilon.
\]

Choose \(\varepsilon<(1-r)/2\) to obtain finite price for every \(r<1\). QED.

## 3. Morphism resolution amplification

Let \((Z,d_Z)\) be another compact metric space and let

\[
 K:X\rightsquigarrow Z
\]

be a Feller Markov kernel. Its effect pullback is

\[
 K^*f(x)=\int_Z f(z)K(x,dz).
 \tag{RP.7}
\]

Define its **resolution amplification** by the extended operator seminorm

\[
 \alpha(K)=
 \sup_{\operatorname{Lip}(f)>0}
 {\operatorname{Lip}(K^*f)\over\operatorname{Lip}(f)}
 \in[0,+\infty].
 \tag{RP.8}
\]

Feller continuity does not imply \(\alpha(K)<\infty\). When finite, \(\alpha(K)\) is the exact
Lipschitz pullback cost. By Kantorovich--Rubinstein duality it is equivalently

\[
 \alpha(K)=
 \sup_{x\ne x'}
 {W_1(K(x,\cdot),K(x',\cdot))\over d_X(x,x')}.
 \tag{RP.9}
\]

### Theorem 3.1 -- compositional price law

For Feller kernels \(K:X\rightsquigarrow Z\) and \(L:Z\rightsquigarrow W\),

\[
 \boxed{\alpha(L\circ K)\le\alpha(K)\alpha(L).}
 \tag{RP.10}
\]

If \(h:X\to Z\) is an isometry and \(K(x,\cdot)=\delta_{h(x)}\), then \(\alpha(K)=1\) whenever
\(X\) has at least two points.

#### Proof

If both amplifications are finite, then for every nonconstant Lipschitz \(f\),

\[
 \operatorname{Lip}(K^*L^*f)
 \le\alpha(K)\operatorname{Lip}(L^*f)
 \le\alpha(K)\alpha(L)\operatorname{Lip}(f).
\]

Take the supremum. If one amplification is infinite and the other is positive, the extended-real
inequality is automatic. If \(\alpha(K)=0\), then all transition measures \(K(x,\cdot)\) agree:
their integrals agree on every Lipschitz function, and Lipschitz functions determine finite Borel
measures on a compact metric space. Hence \(K^*g\) is constant for every continuous \(g\), so the
composite has amplification zero. The case \(\alpha(L)=0\) is immediate because \(L^*f\) is
constant. This also resolves the zero-times-infinity cases. Pullback by an isometry preserves the
Lipschitz seminorm exactly. QED.

Equation `(RP.10)` is the formation grammar missing from qualitative compactness: sequential legal
operations multiply resolution prices. A chain of uniformly nonexpansive operations cannot hide
an unbounded price in its composite.

## 4. Exact formation conservation with price

Let \(Y\) be a nonempty finite set, equipped with the discrete metric, and let \(p_0,p_1\) be
probability masses on \(Y\). Put

\[
 A=\sum_{y\in Y}\sqrt{p_0(y)p_1(y)}.
 \tag{RP.11}
\]

Let \(K_d:X\rightsquigarrow Y^d\) be an exact depth-\(d\) formation:

\[
 (K_d)_*\mu_i=p_i^{\otimes d}\qquad(i=0,1).
 \tag{RP.12}
\]

Equip \(Y^d\) with the discrete metric. Choose a Neyman--Pearson event \(B_d\subseteq Y^d\) such
that

\[
 p_1^{\otimes d}(B_d)-p_0^{\otimes d}(B_d)
 =\operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d}),
\]

and put \(e_d=K_d^*\mathbf1_{B_d}\).

### Theorem 4.1 -- resolution-price formation law

Every exact formation satisfies

\[
 \boxed{
 \Delta_\mu(e_d)
 =\operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d}),
 \qquad
 \alpha(K_d)\ge\operatorname{Lip}(e_d)
 \ge\mathcal R_\mu\!\left(
    \operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})\right).}
 \tag{RP.13}
\]

Since Hellinger affinity tensorizes,

\[
 \boxed{
 \alpha(K_d)
 \ge\mathcal R_\mu(1-A^d).}
 \tag{RP.14}
\]

If \(\mu_0,\mu_1\) have full support and \(0<A<1\), every all-depth exact Feller formation obeys

\[
 \boxed{\alpha(K_d)\longrightarrow+\infty.}
 \tag{RP.15}
\]

#### Proof

Exact pushforward gives

\[
 \Delta_\mu(e_d)
 =p_1^{\otimes d}(B_d)-p_0^{\otimes d}(B_d)
 =\operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d}).
\]

The indicator of any event in a discrete metric space is one-Lipschitz. Hence
\(\operatorname{Lip}(e_d)\le\alpha(K_d)\). Definition `(RP.3)` gives the other price inequality.
Finally,

\[
 \operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})
 \ge1-\sum_{y\in Y^d}\sqrt{p_0^{\otimes d}(y)p_1^{\otimes d}(y)}
 =1-A^d.
\]

Apply monotonicity of \(\mathcal R_\mu\) and Theorem 2.1. QED.

This is stronger than “effects become non-equicontinuous.” It identifies an unavoidable numerical
cost attached to the formation morphism and proves that the cost is compositional.

### Corollary 4.2 -- coordinate-free uniform escape

Let the compact space \(X\), its full-support laws, and an all-depth exact nonneutral formation
family be fixed. For **every** metric \(d\) compatible with the topology of \(X\), let
\(\alpha_d(K_d)\) denote the amplification computed in that metric. Then

\[
 \boxed{\alpha_d(K_d)\longrightarrow+\infty
 \quad\text{for every compatible metric }d.}
 \tag{RP.15a}
\]

Moreover, the maximizing pulled-back decision effects escape every equicontinuous subset of the
unique compatible uniformity of compact \(X\).

#### Proof

Every compatible metric makes \(X\) a compact metric space with the same full-support laws. Apply
Theorem 4.1 separately in each metric. If the maximizing decision effects were equicontinuous,
their \([0,1]\) range and Arzela--Ascoli would give a uniformly convergent subsequence. Its
contrasts tend to one, so its limit would be a continuous perfect separator, contradicting full
support. QED.

The numerical growth rate is metric-dependent; the escape is not. Thus \(\alpha_d\) is a local
gauge for one coordinate-free uniform obstruction. Any arithmetic use of a numerical rate must
derive its metric from source structure rather than choose it after seeing the desired conclusion.

## 5. Coordinate-free observer-fibre localization

The metric price is a gauge. The underlying current split needs no metric.

Let \(\pi:X\to Q\) be any surjective measurable observer with nonempty finite discrete target
\(Q\). For a measurable effect \(e:X\to[0,1]\), define its within-fibre oscillation

\[
 \Omega_\pi(e)
 =\sup\{|e(x)-e(x')|:\pi(x)=\pi(x')\}.
 \tag{RP.16a}
\]

### Theorem 5.1 -- observer-fibre current budget and reconstruction

For every effect \(e\),

\[
 \boxed{
 \Delta_\mu(e)
 \le\operatorname{TV}(\pi_*\mu_0,\pi_*\mu_1)+2\Omega_\pi(e).}
 \tag{RP.16b}
\]

More precisely, after choosing one section \(s:Q\to X\), put

\[
 e^{\mathrm{vis}}=e\circ s\circ\pi,
 \qquad
 e^{\mathrm{hid}}=e-e^{\mathrm{vis}}.
\]

Then the source decision current has the exact reconstruction

\[
 \boxed{
 \Delta_\mu(e)
 =\Delta_\mu(e^{\mathrm{vis}})+\Delta_\mu(e^{\mathrm{hid}}),
 \qquad
 \|e^{\mathrm{hid}}\|_\infty\le\Omega_\pi(e).}
 \tag{RP.16c}
\]

Consequently, for the maximizing effect of every exact formation,

\[
 \boxed{
 \Omega_\pi(e_d)\ge {1\over2}
 \left(
 \operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})
 -\operatorname{TV}(\pi_*\mu_0,\pi_*\mu_1)
 \right)_+.}
 \tag{RP.16d}
\]

#### Proof

The displayed decomposition is an identity. Points \(x\) and \(s\pi(x)\) lie in the same observer
fibre, so \(|e^{\mathrm{hid}}(x)|\le\Omega_\pi(e)\). Because
\(e^{\mathrm{vis}}\) is the pullback of one \([0,1]\)-valued function on finite \(Q\),

\[
 \Delta_\mu(e^{\mathrm{vis}})
 \le\operatorname{TV}(\pi_*\mu_0,\pi_*\mu_1).
\]

The difference of the two hidden integrals is at most \(2\|e^{\mathrm{hid}}\|_\infty\), proving
`(RP.16b)`. Apply the result to \(e_d\), use exact decision-current conservation, and rearrange.
QED.

Equation `(RP.16c)` is the coordinate-free closed-observer/open-history law. The observer quotient
reconstructs the visible effect exactly; any decision current it cannot finance survives as a
within-fibre history, rather than disappearing.

### Theorem 5.2 -- serial observer-descent composition

Let \(\pi:X\to Q\) and \(\rho:Q\to R\) be surjective finite observers. Choose sections
\(s_\pi\) and \(s_\rho\), and use the compatible composite section
\(s_{\rho\pi}=s_\pi\circ s_\rho\). Define

\[
 P_\pi e=e\circ s_\pi\circ\pi,
 \qquad
 \mathcal V_{\mu,\pi}(e)=\Delta_\mu(e-P_\pi e).
\]

If \(f=e\circ s_\pi:Q\to[0,1]\), then

\[
 \boxed{
 \mathcal V_{\mu,\rho\circ\pi}(e)
 =\mathcal V_{\mu,\pi}(e)
 +\mathcal V_{(\pi_*\mu_0,\pi_*\mu_1),\rho}(f).}
 \tag{RP.16e}
\]

#### Proof

Insert and subtract \(P_\pi e\):

\[
 e-P_{\rho\circ\pi}e
 =(e-P_\pi e)+(P_\pi e-P_{\rho\circ\pi}e).
\]

The second summand is the pullback along \(\pi\) of
\(f-f\circ s_\rho\circ\rho\). Integrating a pullback against \(\mu_i\) equals integrating the
original function against \(\pi_*\mu_i\). Apply linearity of the two contrasts. QED.

Thus decision-effect fibre currents add through observer chains, while formation resolution prices
multiply through kernel chains. This is the same observer-descent grammar as the corpus's earlier
KL-chirality fibre conservation, but in a different executor: positive decision effects and total
variation rather than directed relative entropy.

### 5.3 Product-prefix metric gauge

Let \(X_n\) be nonempty finite sets and

\[
 X=\prod_{n\ge0}X_n.
\]

Fix \(0<\theta<1\). For distinct \(x,x'\), let \(m(x,x')\) be their first differing coordinate and
put

\[
 d_\theta(x,x')=\theta^{m(x,x')},
 \qquad d_\theta(x,x)=0.
 \tag{RP.16}
\]

Let \(\pi_N\) retain coordinates \(0,\ldots,N-1\), and write
\(\mu_i^{<N}=(\pi_N)_*\mu_i\).

### Theorem 5.3 -- prefix localization inequality

For every \([0,1]\)-valued \(L\)-Lipschitz effect \(e\),

\[
 \boxed{
 \Delta_\mu(e)
 \le\operatorname{TV}(\mu_0^{<N},\mu_1^{<N})+2L\theta^N.}
 \tag{RP.17}
\]

Consequently every exact formation satisfies

\[
 \boxed{
 \operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})
 \le\operatorname{TV}(\mu_0^{<N},\mu_1^{<N})
      +2\alpha(K_d)\theta^N,}
 \tag{RP.18}
\]

and hence

\[
 \boxed{
 \alpha(K_d)\ge
 {\left(
 \operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})
 -\operatorname{TV}(\mu_0^{<N},\mu_1^{<N})
 \right)_+\over2\theta^N}.}
 \tag{RP.19}
\]

#### Proof

Choose one section \(s_N\) of \(\pi_N\), and define

\[
 e_N=e\circ s_N\circ\pi_N.
\]

The points \(x\) and \(s_N\pi_Nx\) share their first \(N\) coordinates, so

\[
 \|e-e_N\|_\infty\le L\theta^N.
\]

The function \(e_N\) depends only on the finite prefix and takes values in \([0,1]\). Therefore

\[
 \Delta_\mu(e_N)\le\operatorname{TV}(\mu_0^{<N},\mu_1^{<N}).
\]

Changing each of the two integrals from \(e\) to \(e_N\) costs at most \(L\theta^N\), proving
`(RP.17)`. Apply it to the maximizing pulled-back decision effect and use
\(\operatorname{Lip}(e_d)\le\alpha(K_d)\). QED.

### Corollary 5.4 -- product-affinity lower bound

Suppose

\[
 \mu_i=\bigotimes_{n\ge0}q_{i,n},
 \qquad
 a_n=\sum_{x\in X_n}\sqrt{q_{0,n}(x)q_{1,n}(x)},
 \qquad
 A_{s,N}=\prod_{n<N}a_n.
\]

Then

\[
 \boxed{
 \alpha(K_d)\ge
 {\left(1-A^d-\sqrt{1-A_{s,N}^2}\right)_+
  \over2\theta^N}.}
 \tag{RP.20}
\]

#### Proof

For finite probability vectors \(u,v\), Cauchy--Schwarz gives

\[
 \begin{aligned}
 2\operatorname{TV}(u,v)
 &=\sum_j|\sqrt{u_j}-\sqrt{v_j}|(\sqrt{u_j}+\sqrt{v_j})\\
 &\le\sqrt{2-2A(u,v)}\sqrt{2+2A(u,v)},
 \end{aligned}
\]

so \(\operatorname{TV}(u,v)\le\sqrt{1-A(u,v)^2}\). Prefix affinity tensorizes to
\(A_{s,N}\), while target TV is at least \(1-A^d\). Insert both estimates into `(RP.19)`. QED.

Equation `(RP.20)` is a finite-horizon law. It measures exactly how much target information cannot
be financed by the first \(N\) source coordinates and therefore must be paid by sensitivity to the
unresolved tail.

## 6. Hostile countermodel: all-depth Feller formation exists

Let \(Y=\{0,1\}\). Choose distinct Bernoulli laws \(q_0,q_1\) with parameters strictly between zero
and one. Put

\[
 X=Y^{\mathbb N},
 \qquad \mu_i=q_i^{\otimes\mathbb N},
\]

with the ultrametric `(RP.16)`. Let \(K_d\) be deterministic prefix projection:

\[
 K_d(x,\cdot)=\delta_{(x_0,\ldots,x_{d-1})}.
 \tag{RP.21}
\]

### Theorem 6.1 -- exact Feller escape countermodel

For every \(d\ge1\):

1. both \(\mu_0,\mu_1\) have full support;
2. \(\mu_0\perp\mu_1\);
3. \(K_d\) is deterministic Feller and exactly forms \(q_i^{\otimes d}\) from \(\mu_i\);
4. its resolution amplification is exactly

\[
 \boxed{\alpha(K_d)=\theta^{-(d-1)}.}
 \tag{RP.22}
\]

#### Proof

Every nonempty finite cylinder has positive probability under both product laws, proving full
support. By the strong law of large numbers, the limiting empirical one-frequency is almost surely
the parameter of \(q_i\); the two distinct limit events separate the laws, proving singularity.

Prefix projection is locally constant and has the stated exact pushforward. If two source points
first differ at coordinate \(j<d\), their outputs differ in the discrete target and

\[
 {d_{Y^d}(K_dx,K_dx')\over d_\theta(x,x')}
 =\theta^{-j}\le\theta^{-(d-1)}.
\]

If the first difference occurs at or after \(d\), the outputs agree. Hence
\(\alpha(K_d)\le\theta^{-(d-1)}\). For the reverse inequality, take the target effect reading only
coordinate \(d-1\) and source points differing only at that coordinate. Its target Lipschitz
constant is one and its pullback Lipschitz constant is \(\theta^{-(d-1)}\). QED.

This falsifies the proposed selector

\[
 \text{“exact Feller formation from full-support singular laws has bounded depth.”}
\]

The true statement is `(RP.15)`: all-depth formation is possible, but its morphism price must
escape. The example shows the law is not merely qualitative and that exponential escape can be
exact.

## 7. Functional-equation action is price-neutral

Let \(\tau:X\to X\) be an involutive homeomorphism. Starting from any compatible metric \(d\), put

\[
 d_\tau(x,y)=d(x,y)+d(\tau x,\tau y).
 \tag{RP.23}
\]

This is a compatible metric and \(\tau\) is an isometry because \(\tau^2=\mathrm{id}\).

### Theorem 7.1 -- information-neutral functional lift

With respect to \(d_\tau\), pushforward by \(\tau\) preserves the entire resolution price curve:

\[
 \boxed{
 \mathcal R_{(\tau_*\mu_0,\tau_*\mu_1)}(r)
 =\mathcal R_{(\mu_0,\mu_1)}(r)\qquad(0\le r\le1).}
 \tag{RP.24}
\]

Transporting a formation kernel by \(\tau\) also preserves \(\alpha\). Therefore it preserves
`(RP.13)`--`(RP.20)` exactly.

#### Proof

The correspondence \(e\mapsto e\circ\tau\) is a bijection of \([0,1]\)-valued effects, preserves
their Lipschitz constants because \(\tau\) is an isometry, and preserves integral contrast by
change of variables. The same pullback isometry preserves the operator seminorm `(RP.8)`. QED.

Functional equation can relabel or reflect the price, but it cannot pay it.

## 8. Cross-organ consequences

This theorem does not identify all route organs. It imposes one common mechanism on them.

| organ | exact consequence of the resolution law |
|---|---|
| product occupancy / prime-Gamma source | finite prefixes finance at most `(RP.18)`; tail singularity appears as diverging resolution price |
| positive decision / Gram effects | target TV is conserved as one positive source effect `(RP.13)` |
| functional equation / common symmetry | involutive transport is an isometric, information-neutral price action `(RP.24)` |
| recurrence / compact observer | a closed target orbit can coexist with an open source history because `alpha(K_d)` diverges |
| analytic realization | any fixed-domain differentiable realization must carry the same divergence in derivative or modulus bounds |
| Wold inverse-depth receiver | its cofinal equicontinuity statement has the correct *type* for a bounded-price comparison, but no comparison theorem is supplied here |

The theorem also kills one proposed universal identification:

> Hypertranscendence is not, by itself, the source of every noncompact history.

The Bernoulli prefix countermodel has exact noncompact resolution escape with no differential
hypertranscendence. Conversely, the already-proved source-formation harmonic theorem identifies
hypertranscendence with unbounded independent channel rank. ULF-TAFM-5 later shows that target
gauge can transfer resolution cost exactly between the formation morphism and its detector. The
universal field therefore needs at least two independent constitutive coordinates:

\[
 \boxed{\text{formation-channel rank}\quad\text{and}\quad
 \text{endpoint-fixed formation--detector action}.}
 \tag{RP.25}
\]

The amplification in this card is the local coordinate obtained after fixing the discrete target
metric. It is not an invariant of the ungauged kernel alone. Conflating rank, local amplification,
and complete path action recreates the tunnel view this programme is meant to avoid.

## 9. Exact RH producer exposed

The abstract compact-hull gate of ULF-TAFM-2 can now be sharpened. Fix source-generated gauges on
the formation path and its final Neyman--Pearson detector \(f_d\). A sufficient source theorem for
selection would construct literal, zero-independent formation paths and prove

\[
 \sup_d\left(\prod_j\alpha(K_{d,j})\right)q_d(f_d)<+\infty
 \tag{RP.26}
\]

from arithmetic source laws, while an off-centre completed error forces a fixed nonneutral target.
Then the endpoint-fixed action law of ULF-TAFM-5 and `(RP.15)` give a contradiction. The original
single-edge bound \(\sup_d\alpha(K_d)<\infty\) is the special case in which the discrete target
gauge makes \(q_d(f_d)=1\).

This is not yet an RH proof. The open work is not another equivalent Wold or compactness receiver.
It is a comparison theorem that identifies the actual arithmetic formation pullback and bounds its
complete formation--detector action before divisor specialization. Assuming `(RP.26)` only for Xi
zeros would rename RH and is rejected.

## 10. Hostile audit and parent mathematics

### 10.1 Claims deliberately not made

1. Feller admission does not imply finite formation depth; Theorem 6.1 disproves it.
2. Mutual singularity does not imply bounded or unbounded price at a fixed subunit contrast without
   the chosen metric.
3. Resolution amplification is not differential-transcendence rank.
4. The Wold cofinal-equicontinuity classifier is not yet derived from this theorem.
5. No Xi occurrence, completed-zero formation, or source price bound is proved.
6. Numerical price rates are not topological invariants. Only escape through every compatible
   metric/equicontinuous gauge is coordinate-free; an arithmetic rate needs a source-generated
   metric.
7. A chosen visible/hidden representative split depends on its observer sections. The total
   current, intrinsic fibre oscillation, budget inequality, and compatible-chain additivity are
   exact; no canonical section is asserted.
8. Kernel amplification depends on both endpoint gauges. Only the complete source-fixed
   formation--detector action survives target-gauge transfer; ULF-TAFM-5 supplies the exact law.

### 10.2 External boundary

The components are occupied mathematics:

- integral probability metrics and their binary-classification interpretation:
  Sriperumbudur--Fukumizu--Gretton--Schoelkopf--Lanckriet,
  <https://arxiv.org/abs/0901.2698>;
- Wasserstein contraction coefficients for Markov kernels:
  Ollivier, <https://arxiv.org/abs/math/0701886>;
- distinguishability as a compositional resource:
  Wang--Wilde, <https://arxiv.org/abs/1905.11629>;
- information loss under constrained statistical channels:
  Pensia--Jog--Loh, <https://arxiv.org/abs/2206.02765>;
- current finite-product TV tensorization bounds:
  Kontorovich, <https://arxiv.org/abs/2409.10368>.

No component novelty is asserted or required. The corpus-level contribution is the exact fusion of
source price, Markov pullback composition, tensor formation conservation, prefix localization,
functional-equation neutrality, and the hostile Feller countermodel.

ULF-TAFM-5 is the hostile successor: it preserves every fixed-gauge theorem here while falsifying
the interpretation of morphism amplification as an ungauged invariant.

### 10.3 Internal collision audit

`scripts/formal_tools.py research` found:

- `PrimeDepthBVWoldCofinalSourceNormalEquicontinuity`, an RH-equivalent route-specific receiver,
  but no morphism-level resolution amplification or composition theorem;
- `kantorovichRubinstein` and one soft-reporter transport estimate, but no formation-price law;
- qualitative compactness/equicontinuity escape in ULF-TAFM-2 and Law Saturation Mechanics, but no
  curve `(RP.3)`, prefix inequality `(RP.18)`, or exact countermodel price `(RP.22)`;
- `ConstitutiveObserverFibreChirality`, which already proves exact KL-chirality descent through
  observer fibres. Theorem 5.2 is its decision-effect/TV sibling and is presented as executor
  fusion, not as discovery of generic observer-current conservation;
- `ConstitutiveTVConflictColoring`, which already gives exact TV loss inside fibres for finite
  source tasks. Theorem 5.1 instead controls one formation-pulled effect on an arbitrary compact
  source by intrinsic fibre oscillation and connects that loss to tensor depth and morphism price.

## Gates

- [x] 0 -> 1: source-pure mechanism, exact falsifier, no Xi divisor premise
- [x] 1 -> 2: dependency-closed proofs of `(RP.4)`--`(RP.24)`
- [ ] 2 -> 3: Lean definitions and unconditional closed proofs; infrastructure must be built if
  absent, but current research phase explicitly forbids Lean writes/builds
- [ ] 3 -> 4: publication-ready synthesis and priority audit

## Log

- 2026-08-31 -- hostile compactness audit falsified Feller-only selection; introduced compositional
  resolution amplification, proved exact formation and prefix lower bounds, and built the iid
  Bernoulli all-depth Feller countermodel with exact exponential price.
