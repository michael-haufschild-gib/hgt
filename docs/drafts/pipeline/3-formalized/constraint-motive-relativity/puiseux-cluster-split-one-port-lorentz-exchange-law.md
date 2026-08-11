# Puiseux cluster-split one-port Lorentz exchange law

- **ID:** `cmr-puiseux-cluster-split-one-port-lorentz-exchange`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / STRUCTURAL-INTERVENTION CALIBRATION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [STOKES STRUCTURAL INTERVENTION]`
  `[BRIDGE] [NOT EULER/GAMMA LANDING] [NOT RH] [LEAN-FORMALIZED UNCONDITIONALLY]`
- **Formalized companion:** `puiseux-cluster-split-one-port-lorentz-exchange-law-formalized.md`
- **Parent:**
  `../../4-publication-ready/polarized-stokes-microlocal-witt-law/main.tex`.
- **Statement:** activating one higher Puiseux coefficient between two coefficient clusters transfers
  an exact Lorentzian quadratic term from the common rank port to the centered cluster contrast;
  the determinant exponent remains fixed. Smooth coefficient motion inside a contact stratum has
  zero inertia response, while a contact collision has a constructible jump.

## 1. Cluster-split intervention

Let a finite unramified Puiseux spectrum split as

\[
 A=U\sqcup V.
\tag{1}
\]

Assume every cross pair `a in U`, `b in V` has base contact `ell`. Choose an integer `k>ell` and
put

\[
 q_a^{(u)}=q_a^{(0)}+\alpha u w^{-k}\quad(a\in U),
 \qquad
 q_b^{(u)}=q_b^{(0)}+\beta u w^{-k}\quad(b\in V),
\tag{2}
\]

where `alpha ne beta`. The additions are constant inside each cluster. For `u ne 0`, every cross
contact is `k`, while all within-cluster contacts remain unchanged.

For a real dimension vector `x in R^A`, set

\[
 X_U=\sum_{a\in U}x_a,
 \qquad
 X_V=\sum_{b\in V}x_b,
 \qquad
 M=X_U+X_V,
 \qquad
 \Delta=k-\ell>0.
\tag{3}
\]

## 2. Exact Lorentz exchange

### Theorem 2.1

Let `Q_0` and `Q_(u ne 0)` be the coefficient Cartan/coarea forms before and after activation.
Then

\[
 \boxed{
 Q_{u\ne0}(x)-Q_0(x)
 =-2\Delta X_UX_V
 =\frac{\Delta}{2}\bigl((X_U-X_V)^2-M^2\bigr).}
\tag{4}
\]

Consequently,

\[
 \left.(Q_{u\ne0}-Q_0)\right|_{\ker M}
 =2\Delta X_U^2\ge0.
\tag{5}
\]

The physical-rank port `M` is unchanged. When `x` is an integral or virtual-integral dimension
vector, its determinant character

\[
 \lambda\longmapsto\lambda^{M(x)}
\tag{6}
\]

is unchanged. Both endpoint forms obey the published bound

\[
 \operatorname{ind}_{-}(Q)+\dim\operatorname{Rad}(Q)\le1.
\tag{7}
\]

### Proof

Only ordered cross-contact terms change. The contact pairing therefore increases by

\[
 \Delta\sum_{a\in U,b\in V}x_ax_b
 +\Delta\sum_{a\in V,b\in U}x_ax_b
 =2\Delta X_UX_V.
\tag{8}
\]

The contact pairing occurs subtractively in the coefficient Cartan form, proving the first
equality in `(4)`. The second is

\[
 -2AB=\frac12\bigl((A-B)^2-(A+B)^2\bigr).
\tag{9}
\]

On `M=0`, one has `X_V=-X_U`, giving `(5)`. The intervention changes neither ranks nor the
dimension vector, so `M` and `(6)` stay fixed. Bound `(7)` is the dependency-closed coefficient
Witt theorem from the parent paper. QED.

The event has an exact interpretation: `Delta/2` units of quadratic coupling move from the common
port `M` into the centered contrast `X_U-X_V`. This is a change of constitutive law, not smooth
motion of a fixed quadratic form.

## 3. Sharp two-branch wall

For `U={1}`, `V={2}`, common contact `j`, `t=x_1+x_2`, and `z=x_1-x_2`, the form is

\[
 Q_j
 =2x_1^2+2x_2^2+2(1-j)x_1x_2
 =\frac{1+j}{2}z^2+\frac{3-j}{2}t^2.
\tag{10}
\]

Hence

\[
 \Omega_j=\frac{3-j}{2},
 \qquad
 \det C_j=(1+j)(3-j),
\tag{11}
\]

and

\[
 \operatorname{ind}_{-}(Q_j)=
 \begin{cases}
 0,&j<3,\\
 0\text{ with nullity }1,&j=3,\\
 1,&j>3.
 \end{cases}
\tag{12}
\]

For example, take `q_1^(u)=0` and `q_2^(u)=w^(-1)+u w^(-4)`. Then

\[
 u=0:\quad \Omega=1,\quad\det C=4,\quad\operatorname{ind}_{-}=0,
\tag{13}
\]

whereas

\[
 u\ne0:\quad \Omega=-\frac12,\quad\det C=-5,
 \quad\operatorname{ind}_{-}=1.
\tag{14}
\]

The determinant exponent remains `x_1+x_2` on both sides. Thus determinant holonomy and Stokes
inertia are independent constitutive receivers even when they use the same rank port.

## 4. Smooth phase versus constructible law event

For a cross pair, let the activated leading difference be

\[
 \gamma(u)=(\alpha-\beta)u.
\tag{15}
\]

On a local argument lift away from `u=0`, its directed Stokes walls have angles

\[
 \theta_{r,\varepsilon}
 =\frac{\arg\gamma-\tau_\varepsilon}{k}+\frac{2\pi r}{k}.
\tag{16}
\]

Along any differentiable nonzero path,

\[
 \boxed{
 \dot\theta_{r,\varepsilon}
 =\frac1k\operatorname{Im}\frac{\dot u}{u}},
 \qquad
 \boxed{
 \frac d{dt}\log|f'(\theta_{r,\varepsilon})|
 =\operatorname{Re}\frac{\dot u}{u}}.
\tag{17}
\]

At `u=0`, the grade-`k` walls disappear and contact drops; no ordinary derivative exists. Hence:

- `u=e^(it)` rotates phase walls while `Q`, `Omega`, and inertia stay fixed;
- `u=t>0` with `t downarrow 0` changes `Q`, `Omega`, and inertia without phase winding.

No universal phase-to-inertia response law can hold.

## 5. General rank-one crossing form

Let

\[
 Q_t=P_t-\lambda_t r_tr_t^T,
 \qquad P_t>0,
 \qquad r_t\ne0,
\tag{18}
\]

be a `C^1` finite-dimensional real family, and define

\[
 c_t=r_t^TP_t^{-1}r_t,
 \qquad
 \Omega_t=c_t^{-1}-\lambda_t,
 \qquad
 u_t=P_t^{-1}r_t.
\tag{19}
\]

If `Omega_0=0`, then `ker Q_0=R u_0` and

\[
 \boxed{u_0^T\dot Q_0u_0=c_0^2\dot\Omega_0.}
\tag{20}
\]

Indeed, `Q_0x=0` implies

\[
 P_0x=\lambda_0r_0(r_0^Tx),
\]

so `x in R P_0^(-1)r_0=R u_0`; conversely `Omega_0=0` gives
`lambda_0c_0=1`, hence `Q_0u_0=0`. Moreover,

\[
 u_t^TQ_tu_t=c_t-\lambda_tc_t^2=c_t^2\Omega_t.
\tag{21}
\]

Differentiate at zero. The terms containing `dot u_0` vanish because `Q_0u_0=0`, and the term
`2c_0 dot c_0 Omega_0` vanishes because `Omega_0=0`. This proves `(20)`.

At a simple crossing `dot Omega_0 ne 0`, choose `epsilon>0` small enough that zero is the only
crossing on `[-epsilon,epsilon]`. With the convention that a negative-to-positive eigenvalue
crossing contributes `+1`, real spectral-flow orientation and inertia jump are

\[
 \operatorname{sf}_{[-\epsilon,\epsilon]}(Q_t)=\operatorname{sgn}\dot\Omega_0,
 \qquad
 \operatorname{ind}_{-}(Q_{\epsilon})-\operatorname{ind}_{-}(Q_{-\epsilon})
 =-\operatorname{sgn}\dot\Omega_0.
\tag{22}
\]

Thus the correctly typed signed response is the crossing form `(20)`, not a derivative of the
integer-valued inertia.

## 6. Arithmetic central-twist separation

The published arithmetic twist is common to every Stokes block:

\[
 \lambda_i=\delta_n(s).
\tag{23}
\]

It fixes exponential differences, analytic Stokes skeleton, coefficient cuts, coarea form,
capacity, corona quotients, and Rees specializations. Consequently the port gap and inertia are
constant functions of this literal central parameter:

\[
 \boxed{\Omega(s)\equiv\Omega_0,\qquad
 \operatorname{ind}_{-}(Q(s))\equiv\operatorname{ind}_{-}(Q_0)}
\tag{24}
\]

for this literal central twist. For integral or virtual-integral `x`, determinant holonomy changes
by

\[
 \operatorname{Hol}_{\det}=\delta_n(s)^{M(x)}.
\tag{25}
\]

This is the decisive withheld-observer result: the published Euler/Gamma contribution, when
implemented by the literal common central twist `(23)`, cannot create a Stokes inertia crossing.
An arbitrary Mellin coefficient intervention currently has no source-defined map to Puiseux
contacts, so its `Omega` response is undefined, not merely unknown.

## 7. Projective-score loop and its failure

Positive blockwise scalar twists do carry ordinary exponential-family geometry. Put

\[
 m_i=r_ix_i>0,\quad M=\sum_i m_i,\quad q_i=m_i/M,
 \quad \lambda_i=e^{a_i},
\tag{26}
\]

\[
 Z=\sum_iq_ie^{a_i},\qquad
 p_i=\frac{q_ie^{a_i}}Z,qquad
 J(a)=\log Z-\sum_iq_ia_i.
\tag{27}
\]

Then

\[
 J=D_{\rm KL}(q\Vert p)\ge0,
 \qquad
 D^2J=\operatorname{diag}(p)-pp^T,
\tag{28}
\]

\[
 v^TD^2Jv=\frac12\sum_{i,j}p_ip_j(v_i-v_j)^2.
\tag{29}
\]

This exact projective geometry sees relative scalar twists `a_j-a_i`. It is not the coefficient
coarea geometry: its Hessian is a difference Laplacian, whereas Stokes coarea uses cluster sums and
terminal positive squares.

For the common arithmetic twist, all relative scalar-twist coordinates satisfy `a_i-a_j=0`,
so the induced relative scalar-twist response vanishes, `p=q`, and `J=0` for every `s`, while
`(25)` varies. This does not say the pre-existing relative Stokes channels vanish.
Projectivization kills exactly the arithmetic central port. This conjecture loop is therefore
closed as `[BRIDGE]`, not a source producer.

## 8. Consequence for the field program

A non-theatrical source-to-Stokes dynamics must be constructible or logarithmic:

1. smooth coefficient tangents carry phase and normalization response;
2. collision conormals carry Lorentz exchange tensors such as `(4)`;
3. ramification and determinant rank form a locally constant integral system;
4. a source intervention predicts inertia only after a literal pre-divisor map to a collision
   conormal or continuously metrized port-gap family is constructed.

Current corpus has no ordinary Euler/Gamma-to-Puiseux collision functor. This card proves the exact
target law and proves the current central twist cannot realize it. It does not supply source
landing, source null-homology, or RH.

## Literature boundary

Crossing forms, real spectral flow, Stokes moduli, wall crossing, Malgrange forms, exponential
families, and Fisher geometry are parent mathematics. Relevant current parents include
[Porta--Teyssier](https://arxiv.org/abs/2504.05360),
[Hiroe--Yamakawa](https://arxiv.org/abs/2511.01221),
[Douçot--Hohl](https://arxiv.org/abs/2402.05108), and
[Bourne--Carey--van den Dungen--Rennie](https://arxiv.org/abs/2606.31322).
The exact contribution claimed here is only the dependency-closed source-specific cluster
calibration and its separation from the existing arithmetic central twist.

## Gates

- [x] exact cluster-split quadratic exchange
- [x] two-branch inertia-changing example
- [x] smooth phase/jump separation
- [x] correctly typed rank-one crossing form
- [x] central arithmetic twist no-response theorem
- [x] projective-score collision/failure audit
- [x] no RH or source-landing claim
- [ ] literal Euler/Gamma-to-collision functor
- [x] Lean formalization of §§2–7 (unconditional, no sorry, no axiom)

## Log

- 2026-08-09 — created after withheld Stokes response test proved ordinary inertia differentiation
  ill-typed and the literal central arithmetic twist static on the Stokes port gap.
- 2026-08-09 — hostile re-audit accepted after integral determinant scope, local spectral-flow,
  kernel, argument-lift, and common-central-twist repairs.
