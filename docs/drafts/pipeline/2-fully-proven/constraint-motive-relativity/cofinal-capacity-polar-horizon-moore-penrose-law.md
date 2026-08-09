# Cofinal capacity-polar horizon and Moore--Penrose law

- **ID:** `cmr-cofinal-capacity-polar-horizon-moore-penrose`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [COORDINATE-FREE FINITE DUAL-PAIR LAW]`
  `[METRIC-COMETRIC-RELATION POLARITY] [NOT RH]`
  `[NO LEAN WRITTEN OR BUILT]`
- **Parent theorem:** `cofinal-inverse-capacity-vertical-fibre-law.md`.
- **Parent field:**
  `../../1-in-progress/constraint-motive-relativity/polarized-constraint-duality-geometry.md`.
- **Statement:** For every increasing finite-dimensional positive metric family, bounded direct-
  capacity histories are exactly the annihilator of the limiting cometric kernel, equivalently
  the cometric range. In a Hilbert realization their orthogonal complement is simultaneously the
  limiting cometric kernel and the multivalued fibre of the closed port relation. The surviving
  metric is the reduced inverse form, represented in Hilbert coordinates by the Moore--Penrose
  inverse; off its effective domain direct capacities diverge to infinity.

## 1. Setup

Let `V` be a finite-dimensional real vector space. Let

\[
 g_n:V\longrightarrow V^*
\]

be positive symmetric isomorphisms, increasing in the sense that

\[
 (g_{n+1}-g_n)(x,x)\geq0
 \qquad(x\in V).
\tag{CPH.1}
\]

Let `q_n=g_n^(-1):V^*->V`. Regard each `q_n` as the symmetric form
`q_n(alpha,beta)=beta(q_n alpha)` on `V^*`. Inversion reverses order, so `(q_n)` decreases and
converges to a positive-semidefinite symmetric map

\[
 q:V^*\longrightarrow V.
\tag{CPH.2}
\]

Indeed, choose any auxiliary basis and norm. For every `alpha`, the nonnegative numbers
`q_n(alpha,alpha)` decrease, hence converge. Polarization gives convergence of every matrix
coefficient, and finite dimension gives norm convergence to a positive symmetric map. The limit
is independent of the auxiliary basis and norm.

Define

\[
 K=\ker q\subset V^*,
 \qquad W=\operatorname{ran}q\subset V,
\tag{CPH.3}
\]

and the bounded direct-capacity set

\[
 W_{\rm cap}
 =\left\{x\in V:\sup_n g_n(x,x)<\infty\right\}.
\tag{CPH.4}
\]

Write `K^circle={x in V:alpha(x)=0 for every alpha in K}` for the annihilator.

## 2. Main theorem

### Theorem 2.1 — capacity-polar horizon law

One has the exact coordinate-free identities

\[
 \boxed{W_{\rm cap}=W=\operatorname{ran}q=K^\circ}.
\tag{CPH.5}
\]

For `x=q beta` and `y=q gamma` in `W`, define the reduced inverse bilinear form

\[
 g_{\rm red}(q\beta,q\gamma)=q(\beta,\gamma).
\]

This is well-defined because `K=ker q` is the radical of the positive-semidefinite form `q`. In
particular `g_red(x,x)=q(beta,beta)`. For every `x in V`,

\[
 \lim_ng_n(x,x)
 =
 \begin{cases}
  g_{\rm red}(x,x),&x\in W,\\
  +\infty,&x\notin W.
 \end{cases}
\tag{CPH.6}
\]

By polarization, `g_n|W` converges to the reduced inverse form `g_red`. Thus the extended limiting
metric

\[
 g_\infty(x)=
 \begin{cases}
  g_{\rm red}(x,x),&x\in W,\\
  +\infty,&x\notin W
 \end{cases}
\tag{CPH.7}
\]

and the limiting cometric `q` determine one another, including effective domain and kernel.

After choosing a Hilbert inner product and identifying `V^*=V`, write `q=Q_infinity`. Then

\[
 W=\operatorname{ran}Q_\infty=(\ker Q_\infty)^\perp,
 \qquad
 g_{\rm red}(x,x)=\langle Q_\infty^\dagger x,x\rangle.
\tag{CPH.7a}
\]

### Corollary 2.2 — relation-valued horizon

Set `V=Y` and assume `Y` is the finite-dimensional **real** Hilbert output of the parent theorem.
Identify `g_n=G_n` and `q_n=Q_n`. Suppose `(G_n)` is the Gram family `G_n=T_nT_n^*`, with
compatible surjective maps on a nested dense domain, and put `M=ker Q_infinity`. Then

\[
 \boxed{
 Y=W_{\rm cap}\oplus
 \operatorname{mul}\overline{\Gamma(T)},
 \qquad
 \operatorname{mul}\overline{\Gamma(T)}=W_{\rm cap}^\perp.}
\tag{CPH.8}
\]

The same port direction cannot simultaneously remain a nonzero finite-cost direction and become
vertical ambiguity. The split is exhaustive and orthogonal.

## 3. Proof

For every positive symmetric isomorphism `q_n:V^*->V`, completing the square gives the variational
identity

\[
 g_n(x,x)
 =\sup_{\alpha\in V^*}
 \left(2\alpha(x)-q_n(\alpha,\alpha)\right).
\tag{CPH.9}
\]

Taking suprema over `n` and `alpha` in either order gives

\[
 \sup_ng_n(x,x)
 =\sup_{\alpha\in V^*}
 \left(2\alpha(x)-q(\alpha,\alpha)\right),
\tag{CPH.10}
\]

because `q_n(alpha,alpha)` decreases pointwise to `q(alpha,alpha)`. Symmetry gives
`ran q subset K^circle`. Rank-nullity gives equal dimensions, hence

\[
 \operatorname{ran}q=K^\circ.
\tag{CPH.11}
\]

If `x notin K^circle`, choose `alpha in K` with `alpha(x)!=0`. Substituting `t alpha` into
`(CPH.10)` makes the supremum infinite.

If `x in ran q`, write `x=q beta`. Then

\[
 2\alpha(x)-q(\alpha,\alpha)
 =q(\beta,\beta)-q(\alpha-\beta,\alpha-\beta)
 \leq q(\beta,\beta),
\tag{CPH.12}
\]

with equality at `alpha=beta`. Replacing `beta` by `beta+k`, `k in K`, does not change
`q(beta,beta)`, so the reduced inverse is well-defined. This proves `(CPH.5)--(CPH.6)`.
Conversely, completing the same square gives the reverse polar identity

\[
 q(\alpha,\alpha)
 =\sup_{x\in V}\bigl(2\alpha(x)-g_\infty(x)\bigr)
 =\sup_{x\in W}\bigl(2\alpha(x)-g_{\rm red}(x,x)\bigr).
\tag{CPH.12a}
\]

Thus `g_infinity` and `q` determine one another. Polarization gives the bilinear statement. The
Hilbert formula `(CPH.7a)` is the standard
Moore--Penrose realization of the reduced inverse. Corollary 2.2 follows from the parent identity
`mul closure Gamma(T)=ker Q_infinity`.

## 4. Interpretation: exact horizon, scoped claim

In this Hilbert doctrine the cofinal limit is a singular metric/cometric pair:

- `W` is the finite direct-capacity observer sector;
- `M` is infinitely costly for the direct metric;
- the inverse metric collapses exactly on `M`;
- graph closure turns the same `M` into relation-valued law ambiguity.

This is the precise content of a **constraint horizon**. It is analogous to an infinite-redshift
surface only at the level of metric/cometric degeneration. No Lorentzian spacetime, black-hole
interior, entropy, or wormhole length is constructed by this theorem.

The theorem also gives one rigorous form of the corpus's apparent precision complementarity.
Making direct filling cost cofinally coercive along `M` makes the inverse observer resolution zero
there; retaining finite inverse resolution forces the direction into `W`. This is an identity,
not a philosophical uncertainty principle.

## 5. Integral and recurrence interface

If `Y` also carries a full lattice `Lambda`, the theorem does not force `M` to be lattice-rational.
The linked finite lattice-direction theorem gives a sufficient condition and a counterexample:

- finitely many fixed lattice directions force `M=span_R(M intersect Lambda)`;
- cofinally rotating rational directions can produce an irrational `M`.

When `M` is rational, `Lambda_M=Lambda intersect M` gives the Pontryagin exact sequence

\[
 0\to\widehat{\Lambda/\Lambda_M}
 \to\widehat\Lambda
 \to\widehat{\Lambda_M}\to0.
\tag{CPH.13}
\]

Thus the capacity horizon determines a compact recurrence factor only after integral provenance
has been proved. Topological phase data are not manufactured from the Hilbert metric alone.

## 6. Conjecture/proof/failure loops

### Loop A — the inverse-capacity kernel is only a formal nullspace

**Failed.** `(CPH.5)--(CPH.6)` recover it intrinsically as the polar complement of every history
whose direct capacity remains bounded.

**Survivor.** Metric, cometric, and relation-valued output share one exact horizon subspace.

### Loop B — bounded direct energy might survive partly inside the vertical fibre

**Failed.** `(CPH.5)--(CPH.6)` prove divergence for every vector with a nonzero vertical component
in the Hilbert splitting.

**Survivor.** The decomposition `(CPH.8)` is exhaustive, not merely a rank inequality.

### Loop C — every corpus obstruction is a capacity horizon

**Failed as an inference.** Affine Mass successors, differential HT rank, nonpositive Stokes
inertia, source normalization, and physical reconstruction need not admit an increasing Gram
chart. Calling them horizons without constructing `(CPH.1)` is theatre.

**Survivor.** Any proposed Hilbert-capacity realization has exact, falsifiable consequences
`(CPH.5)--(CPH.12)`.

### Loop D — the horizon itself selects RH

**Failed.** The theorem classifies every monotone Gram degeneration, including explicit
off-critical and non-arithmetic models. It supplies geometry, not the missing source equation.

## 7. Sharp boundary countermodels

### 7.1 Vector convergence does not follow

Let `t_n decrease 0` and

\[
 Q_t=\begin{pmatrix}1+t&t^2/2\\t^2/2&t^3/3\end{pmatrix}
 =\begin{pmatrix}1&0\\0&0\end{pmatrix}
 +\int_0^t(1,s)^T(1,s)\,ds.
\]

Then `Q_(t_n)` decreases to `diag(1,0)` and `G_n=Q_(t_n)^(-1)` increases. For `x=e_1` in the
finite-cost sector,

\[
 \langle G_nx,x\rangle=\frac4{4+t_n}\longrightarrow1,
 \qquad
 G_nx=\left(\frac4{4+t_n},-\frac6{t_n(4+t_n)}\right).
\]

Thus the reduced quadratic/bilinear form converges, while the uncompressed vectors `G_nx` need
not. No stronger operator convergence is claimed.

### 7.2 Monotonicity is essential

For `0<c_n<1` with `c_n decrease 0`, set

\[
 Q_n=\begin{pmatrix}
 1&\sqrt{c_n(1-c_n)}\\
 \sqrt{c_n(1-c_n)}&c_n
 \end{pmatrix}.
\]

Their determinants are `c_n^2>0`, so they are positive definite and converge to `diag(1,0)`, but
they are not Loewner ordered. Although `e_1` lies in the limiting range,
`<Q_n^(-1)e_1,e_1>=1/c_n->infinity`. Hence convergence of cometrics without monotonicity does not
imply `(CPH.5)--(CPH.6)`.

### 7.3 Finite dimension is essential

On `ell^2(N)`, take `Q=diag(k^(-2))`, `Q_n=Q+n^(-1)1`, and `G_n=Q_n^(-1)`. Then `Q_n` decreases to
the injective operator `Q`, but the bounded-energy domain is

\[
 \operatorname{ran}Q^{1/2}
 =\left\{x:\sum_k k^2|x_k|^2<\infty\right\},
\]

a proper dense subspace of `ell^2`, not `ran Q` and not `(ker Q)^perp=ell^2`. For example
`x_k=k^(-2)` lies in `ran Q^(1/2)` but not `ran Q`. Infinite-dimensional extension requires
closed quadratic-form/domain geometry and is an open PCDG chart, not a corollary of this card.

The domain claim follows directly from monotone convergence for nonnegative series:

\[
 \sup_n\langle G_nx,x\rangle
 =\lim_n\sum_k\frac{|x_k|^2}{k^{-2}+n^{-1}}
 =\sum_k k^2|x_k|^2.
\]

## 8. Predictions and falsifiers

1. In any increasing Gram chart, a claimed bounded-capacity vector outside `ran Q_infinity` is
   impossible.
2. On `ran Q_infinity`, the limiting direct metric is uniquely `Q_infinity^dagger`; any different
   claimed finite limit is false.
3. In any nested port realization, vertical rank equals codimension of the finite-capacity sector.
4. A regularization making `Q_infinity` positive definite removes every vertical relation and
   makes the extended metric finite on all of `Y`.
5. A physical horizon interpretation must construct its Gram maps, source inner product, and
   observer port before applying this theorem; matching only a nullity is insufficient.

## 9. No-go closure

- **Failed conjecture:** inverse-capacity collapse, direct-cost blow-up, and relation verticality
  are three unrelated pathologies.
- **Exact killing mechanism:** Fenchel duality `(CPH.9)` forces all three to share the polar split
  `(CPH.5)--(CPH.8)`.
- **Strongest positive survivor:** intrinsic extended metric `g_infinity` and cometric `q` form a
  finite dual-pair polar geometry; a Hilbert realization adds the closed relation as its third
  exact face.
- **Scope:** unconditional finite-dimensional theorem; no Lean written or built; no RH claim.

## Log

- 2026-08-09 — proved capacity-polar decomposition by variational duality.
- 2026-08-09 — identified exact Moore--Penrose metric on the surviving sector.
- 2026-08-09 — connected inverse collapse to graph verticality and separated physical analogy
  from theorem.
