# Cofinal inverse-capacity and vertical-fibre law

- **ID:** `cmr-cofinal-inverse-capacity-vertical-fibre`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [CROSS-DOCTRINE BRIDGE]`
  `[PRIME-PORT INSTANTIATION] [POINTED-CARTAN INSTANTIATION] [NOT RH]`
  `[NO LEAN WRITTEN OR BUILT]`
- **Parent field:**
  `../../1-in-progress/constraint-motive-relativity/polarized-constraint-duality-geometry.md`.
- **Corpus parents:** `weighted-port-capacity-admission-recurrence-law.md`;
  `prime-port-algebraic-continuous-separation-law.md`;
  `../../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`.
- **Statement:** For a nested exhaustion by finite-dimensional port problems, the limiting quotient
  seminorm vanishes exactly on the multivalued vertical fibre of the closed graph. In Hilbert
  charts it is represented by the limit of inverse-capacity operators.

## 1. The theorem

Let `X` be a normed space, let

\[
 X_1\subset X_2\subset\cdots\subset X
\]

be finite-dimensional subspaces, put `D=union_n X_n`, and assume `D` is dense in `X`. Let `Y` be a
finite-dimensional normed space and let `T:D->Y` be linear. Write `T_n=T|X_n` and assume that
`T_n` is surjective for every `n>=n_0`.

For `n>=n_0` define the quotient norm and minimum squared filling energy

\[
 q_n(y)=\inf\{\|x\|:x\in X_n,\ T_nx=y\},
 \qquad E_n(y)=q_n(y)^2.
\tag{IC.1}
\]

Let `q_infinity(y)=lim_n q_n(y)`, which exists because the sequence decreases. Let
`Gamma(T)={(x,Tx):x in D}` and take its closure in `completion(X) direct-sum Y`. The
multivalued part is

\[
 \operatorname{mul}\overline{\Gamma(T)}
 =\{y\in Y:(0,y)\in\overline{\Gamma(T)}\}.
\tag{IC.2}
\]

### Theorem 1.1 — quotient-seminorm/vertical-fibre identity

The function `q_infinity` is a seminorm on `Y`, and

\[
 \boxed{\operatorname{mul}\overline{\Gamma(T)}=\ker q_\infty.}
\tag{IC.3}
\]

Consequently, `T` is closable exactly when `q_infinity` is a norm.

If `X=H` and `Y` are Hilbert spaces, let `H_n=X_n` and define

\[
 G_n=T_nT_n^*,
 \qquad Q_n=G_n^{-1}.
\tag{IC.4}
\]

Then `(G_n)` is increasing in the Loewner order, `(Q_n)` is decreasing to a positive
semidefinite operator `Q_infinity`, and

\[
 E_n(y)=\langle Q_ny,y\rangle,
 \qquad x_n(y)=T_n^*Q_ny
\tag{IC.5}
\]

with `x_n(y)` the unique minimum-norm lift. In this chart,

\[
 \boxed{\operatorname{mul}\overline{\Gamma(T)}=\ker Q_\infty.}
\tag{IC.6}
\]

Thus `T` is closable exactly when `Q_infinity` is positive definite, meaning
`ker Q_infinity=0`, and vertical-fibre dimension
is `nullity(Q_infinity)`.

## 2. Proof

Since `X_n` increases, `q_n` decreases pointwise. It is a norm on `Y`: it is the quotient norm of
the finite-dimensional normed space `X_n/ker T_n`, transported through the isomorphism induced by
`T_n`. Pointwise decreasing limits of seminorms are seminorms, so `q_infinity` is a seminorm.

Suppose first that `q_infinity(y)=0`. Choose `x_n in X_n` with

\[
 Tx_n=y,
 \qquad \|x_n\|\leq q_n(y)+1/n.
\]

Then `x_n->0`, so `(x_n,y)->(0,y)` and `y in mul closure Gamma(T)`.

Conversely, suppose `y in mul closure Gamma(T)`. There are `z_j in D` with

\[
 z_j\longrightarrow0,
 \qquad Tz_j\longrightarrow y.
\tag{IC.7}
\]

Choose `m_j>=n_0` with `z_j in X_{m_j}`. Because all norms on finite-dimensional `Y` are
equivalent, the fixed quotient norm `q_(n_0)` obeys

\[
 q_n(v)\leq q_{n_0}(v)\leq C\|v\|_Y
 \qquad(n\geq n_0)
\tag{IC.8}
\]

for some `C`. Hence

\[
 q_{m_j}(y)
 \leq q_{m_j}(Tz_j)+q_{m_j}(y-Tz_j)
 \leq\|z_j\|+C\|y-Tz_j\|\longrightarrow0.
\tag{IC.9}
\]

Since `q_infinity<=q_(m_j)`, this gives `q_infinity(y)=0` and proves `(IC.3)`. An operator is
closable exactly when its closed graph relation has zero multivalued part.

Now assume the Hilbert hypotheses. Fix `m>=n>=n_0`. Let `P_n:H_m->H_n` be the orthogonal
projection. Since `T_m|H_n=T_n`,

\[
 T_n^*=P_nT_m^*.
\]

Therefore

\[
 G_m-G_n
 =T_m(1-P_n)T_m^*\succeq0.
\tag{IC.10}
\]

Every `G_n` is positive definite because `T_n` is surjective. Inversion reverses the positive
definite Loewner order, so

\[
 0\prec Q_m\preceq Q_n\preceq Q_{n_0}.
\tag{IC.11}
\]

Finite dimensionality of `Y` gives a positive semidefinite operator-norm limit
`Q_n -> Q_infinity`.

For the minimum-energy formula, put `x_n=T_n^*Q_ny`. Then

\[
 T_nx_n=T_nT_n^*Q_ny=G_nQ_ny=y.
\]

If `T_nx=y`, then `x-x_n in ker T_n`, while `x_n in im T_n^*=(ker T_n)^perp`. Hence

\[
 \|x\|^2=\|x_n\|^2+\|x-x_n\|^2
 \geq\|x_n\|^2.
\]

Finally,

\[
 \|x_n\|^2
 =\langle Q_nT_nT_n^*Q_ny,y\rangle
 =\langle Q_ny,y\rangle,
\]

proving `(IC.4)--(IC.5)`. Since `q_n(y)^2=<Q_ny,y>`, the already proved identity `(IC.3)` becomes
`(IC.6)`, completing the proof.

## 3. Scalar capacity corollary

In the scalar Hilbert case `Y=C`, write

\[
 C_n=G_n>0.
\]

Then `Q_n=C_n^{-1}` and

\[
 \operatorname{mul}\overline{\Gamma(T)}
 =\begin{cases}
 0,&\sup_n C_n<\infty,\\
 \mathbb C,&C_n\to\infty.
 \end{cases}
\tag{IC.12}
\]

Thus divergent filling capacity is not only an estimate failure. After graph closure it becomes a
vertical relation-valued output.

## 4. Literal prime-port instantiation

Enumerate the primes `p_1,p_2,...`. Take

\[
 H=\ell^2(\mathcal P),\qquad
 H_n=\operatorname{span}\{e_{p_1},\ldots,e_{p_n}\},\qquad
 T(x)=\sum_p x_p.
\]

Then `G_n=n` and `Q_n=1/n`. Therefore

\[
 \operatorname{mul}\overline{\Gamma(T)}=\mathbb C.
\tag{IC.13}
\]

The minimizing lift of `1` is the uniform vector `(1/n,...,1/n)`, whose squared norm is `1/n`.
This recovers the dense prime-augmentation kernel and the disappearance of the continuous
one-port quotient in the unweighted Hilbert completion.

For the weighted port from the parent capacity card, assume `w_p>0`, `a` is not identically zero,
take `H=ell_w^2(supp(a))`, and use a nested finite exhaustion of `supp(a)`. Then the algebraic
union of the cutoff spaces is dense in `H`, and

\[
 T(x)=\sum_pa_px_p,
 \qquad\|x\|_w^2=\sum_pw_p|x_p|^2,
\]

the finite capacity is

\[
 G_F=\sum_{p\in F}\frac{|a_p|^2}{w_p}.
\]

The theorem reproduces the exact phase transition: finite total capacity gives a closable bounded
port; divergent total capacity gives a full scalar vertical fibre.

## 5. Literal pointed-Cartan instantiation

The publication-ready Hellinger--Hodge--Green paper proves the following source-independent
Pointed Cartan law. A seminormed source has transports `V_t`, a covector `L`, and a nonzero `u` such
that, for `z=mu+i tau` with `mu!=0`,

\[
 u_n=e^{-n\mu z}V_{n\mu}u,
 \qquad L(u_n)=L(u)=c\ne0,
 \qquad p(u_n)=e^{-n\mu^2}p(u)\longrightarrow0.
\tag{IC.14}
\]

Let `W=span{u_n:n>=1}`. Let `q:W->X_p` be the Hausdorff seminorm-completion map and form the
algebraic relation

\[
 \mathcal R_0=\{(qv,Lv):v\in W\}\subset X_p\oplus\mathbb C.
\tag{IC.15}
\]

There are two exact cases.

1. If `L(ker q)!=0`, then `mul R_0!=0`; scalar linearity already gives
   `mul R_0=C`, before closure.
2. If `L(ker q)=0`, put `X=closure(q(W))` inside `X_p`. Then
   `D=q(W)=union_n X_n` is dense in `X`, `L` descends to a well-defined operator
   `T:D->C`, and

   \[
   X_n=\operatorname{span}\{q(u_1),\ldots,q(u_n)\}.
   \]

   Every restriction `T_n` is surjective, and `q(u_n)/c` is a lift of `1`. Therefore its quotient
   norm satisfies

   \[
   q_n(1)\leq\frac{p(u_n)}{|c|}
   =\frac{e^{-n\mu^2}p(u)}{|c|}\longrightarrow0.
   \tag{IC.16}
   \]

   Theorem 1.1 gives `mul closure_Xdirect-sumC Gamma(T)=C`. This graph closure equals the closure
   of `R_0` in `X_p direct-sum C`: every first-coordinate limit lies in `X=closure(q(W))`, so
   passing from `X` to its ambient space adds no graph limits.

Thus the closed relation is maximally vertical in either case. This recovers the paper's
graph-null conclusion as the zero limiting quotient-seminorm law. When an additional Hilbert
structure represents that quotient norm, `(IC.16)` is equivalently collapse of scalar inverse
capacity; the publication's canonical half-density completion itself is Banach, so no Hilbert
representation is asserted there.

For the Xi specialization, the paper sets `z=rho-1/2`. The present theorem explains the
capacity-to-relation mechanism off the critical line. It does not prove that every Xi zero has
`mu=0`; the global RH equivalence remains exactly where the publication places it.

## 6. What this explains

The theorem is a genuine cross-doctrine comparison:

\[
 \text{finite quotient metric}
 \quad\longrightarrow\quad
 \text{limiting quotient seminorm / Hilbert inverse capacity}
 \quad\longrightarrow\quad
 \text{multivalued closed relation}.
\]

It explains why finite observer surjectivity can coexist with total loss of a single-valued
cofinal law. Horizontal decoding becomes arbitrarily cheap in the source norm, so the same output
survives over a vanishing input and reappears as vertical ambiguity.

It does not identify every route obstruction with capacity. Route E has directed incidence and
nonlinear resource constraints; Mass has an affine first-unseen moment; recurrence has an integral
lattice; HT has differential rank. Those require their native doctrines.

## 7. Falsifiers and predictions

1. If `Q_infinity` is positive definite, any claimed nonzero vertical fibre is false.
2. If a fixed nonzero port has lifts with norms tending to zero, any claimed closable extension
   retaining that port is false.
3. For vector-valued Hilbert ports, only `ker Q_infinity` becomes multivalued. After quotienting
   the output by this kernel, the induced closed relation is single-valued. This predicts partial
   verticality rather than an all-or-nothing phase; boundedness is not asserted.
4. A regularization that keeps inverse capacities uniformly positive removes the vertical fibre;
   it must pay a nonzero minimum filling cost.
5. Rank of `ker Q_infinity` is the exact output rank transmuted from horizontal decoding into
   vertical ambiguity.

## 8. No-go closure

- **Failed conjecture:** cofinal finite surjectivity should produce a well-defined limiting
  observer.
- **Exact killing mechanism:** inverse capacity may collapse to zero, producing arbitrarily small
  lifts of fixed outputs and hence a multivalued graph closure.
- **Strongest positive survivor:** `(IC.3)` classifies the vertical fibre exactly, direction by
  direction, by `ker Q_infinity`.
- **Status:** dependency-closed paper proof; no Lean written or built.

## Log

- 2026-08-09 — proved monotone capacity, minimum-energy, and exact vertical-fibre identity.
- 2026-08-09 — instantiated on prime augmentation and published Pointed Cartan graph-null law.
