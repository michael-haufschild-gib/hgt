Below is the clean lemma. It is **not** a proof of RH. It proves only the last implication:

[
Q_0[p]\ge0\ \forall p\in\mathbb R[y]
\quad\Longrightarrow\quad
RH
]

for the **actual folded reciprocal zero divisor**. The open bridge theorem would still be the hard source-built step proving (Q_0\ge0) from completion + explicit formula + canonical boundary, not from zero locations. The uploaded bridge file states exactly this distinction: the reciprocal (Q_0) positivity is the “last theorem before RH,” while deriving it from source data is the open part.

---

# 1. Definitions

Let

[
\Xi(w)=\xi!\left(\frac12+w\right).
]

Then (\Xi) is even:

[
\Xi(w)=\Xi(-w).
]

Let (w_\rho=\rho-\frac12) be a zero of (\Xi), with multiplicity (m_\rho). Since (\Xi) is even, zeros occur in pairs

[
w,,-w.
]

Since (\Xi) is real on the real axis, zeros are also conjugation-symmetric.

Define the reciprocal seam-squared coordinate

[
\boxed{
y_\rho=-w_\rho^{-2}=-(\rho-\tfrac12)^{-2}.
}
]

The pair (w,-w) maps to the same (y), so we fold the divisor by the involution (w\mapsto-w). Write the folded divisor as

[
\mathcal Y={(y_\alpha,M_\alpha)},
]

where (M_\alpha) is the total multiplicity of all zeros mapping to the same (y_\alpha). Thus

[
M_\alpha\in\mathbb N,
\qquad
y_\alpha\ne0,
]

and if (y_\alpha\notin\mathbb R), then (\overline{y_\alpha}\in\mathcal Y) with the same multiplicity.

For (k\ge1), define

[
\boxed{
T_k=\sum_{\alpha}M_\alpha y_\alpha^k.
}
]

This is absolutely convergent for (k\ge1). Indeed, the zeros satisfy (N(T)=O(T\log T)), so

[
\sum_\rho |w_\rho|^{-2}<\infty,
]

and therefore all higher reciprocal-square sums converge absolutely.

For a real polynomial

[
p(y)=\sum_{i=0}^d c_i y^i,
\qquad c_i\in\mathbb R,
]

define

[
\boxed{
Q_0[p]
======

\sum_{i,j=0}^d c_i c_j T_{i+j+1}.
}
]

Because of the definition of (T_k),

[
\begin{aligned}
Q_0[p]
&=
\sum_{i,j}c_i c_j
\sum_\alpha M_\alpha y_\alpha^{i+j+1} \
&=
\sum_\alpha M_\alpha y_\alpha
\left(\sum_i c_i y_\alpha^i\right)^2 \
&=
\boxed{
\sum_\alpha M_\alpha y_\alpha p(y_\alpha)^2.
}
\end{aligned}
]

Since the folded divisor is conjugation-symmetric and (p) has real coefficients, (Q_0[p]\in\mathbb R).

---

# 2. The theorem

## Theorem

For the actual folded reciprocal zero divisor of (\Xi),

[
\boxed{
Q_0[p]\ge0\quad\forall p\in\mathbb R[y]
}
]

implies

[
\boxed{
y_\alpha\in\mathbb R_{>0}\quad\forall\alpha.
}
]

Consequently every zero satisfies

[
\rho=\frac12+i\gamma,
]

so RH follows.

---

# 3. Proof

Assume

[
Q_0[p]\ge0
\quad
\forall p\in\mathbb R[y].
]

Define the shifted moment sequence

[
m_n:=T_{n+1},
\qquad n\ge0.
]

Then

[
Q_0[p]
======

\sum_{i,j}c_i c_j m_{i+j}.
]

So the linear functional

[
L!\left(\sum_n b_n y^n\right)
=============================

\sum_n b_n m_n
]

satisfies

[
L[p^2]\ge0
\quad
\forall p\in\mathbb R[y].
]

By the Hamburger/Riesz moment theorem, there is a positive finite Borel measure (\mu) on (\mathbb R) such that

[
\boxed{
m_n=\int_{\mathbb R} x^n,d\mu(x)
}
]

for every (n\ge0).

This is the only classical moment-theory input. Everything after this uses the actual folded divisor.

---

## Step 1 — the representing measure is compactly supported

Let

[
R:=\sup_\alpha |y_\alpha|<\infty.
]

This is finite because (\Xi(0)=\xi(1/2)\ne0), so the zeros (w_\rho) stay a positive distance away from (0), and (y_\rho=-w_\rho^{-2}) is bounded.

Also

[
S:=\sum_\alpha M_\alpha |y_\alpha|<\infty.
]

Therefore

[
|m_n|
=====

|T_{n+1}|
\le
\sum_\alpha M_\alpha |y_\alpha|^{n+1}
\le
S R^n.
]

If (\mu) had positive mass outside ([-R-\varepsilon,R+\varepsilon]), then for even (n=2N),

[
m_{2N}
======

\int x^{2N},d\mu(x)
\ge
\mu(|x|>R+\varepsilon)(R+\varepsilon)^{2N},
]

contradicting

[
|m_{2N}|\le S R^{2N}
]

as (N\to\infty). Hence

[
\boxed{
\operatorname{supp}\mu\subseteq[-R,R].
}
]

---

## Step 2 — compare generating functions

Define the moment generating function

[
G(z)=\sum_{n=0}^\infty m_n z^n.
]

For (|z|<1/R), using the divisor definition,

[
\begin{aligned}
G(z)
&=
\sum_{n=0}^\infty T_{n+1}z^n \
&=
\sum_{n=0}^\infty
\sum_\alpha M_\alpha y_\alpha^{n+1}z^n \
&=
\sum_\alpha M_\alpha y_\alpha
\sum_{n=0}^\infty (y_\alpha z)^n \
&=
\boxed{
\sum_\alpha \frac{M_\alpha y_\alpha}{1-y_\alpha z}.
}
\end{aligned}
]

From the positive representing measure (\mu),

[
\boxed{
G(z)=
\int_{[-R,R]}
\frac{d\mu(x)}{1-xz}.
}
]

These two analytic functions agree near (z=0).

---

## Step 3 — non-real atoms are impossible

Suppose some folded atom (y_0) is non-real.

Then the divisor-side expression

[
\sum_\alpha \frac{M_\alpha y_\alpha}{1-y_\alpha z}
]

has a simple pole at

[
z_0=\frac1{y_0}.
]

The residue is nonzero:

[
\operatorname{Res}*{z=1/y_0}
\frac{M*{y_0}y_0}{1-y_0z}
=========================

-M_{y_0}\ne0.
]

But (z_0\notin\mathbb R). The positive-measure expression

[
\int_{[-R,R]}\frac{d\mu(x)}{1-xz}
]

is holomorphic near every non-real (z_0), because (1-xz_0\ne0) for all real (x).

Contradiction.

Therefore

[
\boxed{
y_\alpha\in\mathbb R
\quad\forall\alpha.
}
]

---

## Step 4 — negative real atoms are impossible

Now all (y_\alpha) are real.

Define the finite signed measure

[
\nu
===

\sum_\alpha M_\alpha y_\alpha,\delta_{y_\alpha}.
]

Its moments are

[
\int x^n,d\nu(x)
================

# \sum_\alpha M_\alpha y_\alpha^{n+1}

# T_{n+1}

m_n.
]

But (\mu) is a positive finite measure on the compact interval ([-R,R]) with the same moments:

[
\int x^n,d\mu(x)
================

# m_n

\int x^n,d\nu(x).
]

Therefore

[
\int P(x),d\mu(x)
=================

\int P(x),d\nu(x)
]

for every polynomial (P).

By Weierstrass approximation, polynomials are dense in (C[-R,R]), so

[
\boxed{
\mu=\nu.
}
]

Since (\mu) is positive, (\nu) must be a positive measure. But the mass of (\nu) at (y_\alpha) is

[
M_\alpha y_\alpha.
]

Because (M_\alpha>0), positivity of (\nu) forces

[
M_\alpha y_\alpha>0,
]

hence

[
\boxed{
y_\alpha>0
\quad\forall\alpha.
}
]

Thus

[
\boxed{
\operatorname{supp}\mathcal Y\subset\mathbb R_{>0}.
}
]

---

## Step 5 — positive (y_\rho) means RH

For each zero,

[
y_\rho=-(\rho-\tfrac12)^{-2}.
]

If

[
y_\rho>0,
]

then

[
(\rho-\tfrac12)^2=-\frac1{y_\rho}<0.
]

So

[
\rho-\frac12
]

is purely imaginary. Therefore

[
\boxed{
\rho=\frac12+i\gamma.
}
]

Thus every zero lies on the critical line.

Hence

[
\boxed{
Q_0[p]\ge0\ \forall p\in\mathbb R[y]
\quad\Longrightarrow\quad
RH.
}
]

---

# 4. Why this is stronger than the source-forgotten Stieltjes test

For an arbitrary real moment sequence, to prove support in ([0,\infty)), one normally needs both Hankel towers:

[
[T_{i+j+1}]\succeq0,
\qquad
[T_{i+j+2}]\succeq0.
]

That is the standard Stieltjes moment condition.

Here, however, (Q_0) alone is enough because we are **not** dealing with an arbitrary moment sequence. We are dealing with the actual folded divisor

[
y_\rho=-(\rho-\tfrac12)^{-2}
]

with positive integer multiplicities, conjugation symmetry, finite shifted moments, and a meromorphic generating function whose poles are exactly at (z=1/y_\rho).

That extra divisor structure is what the proof uses.

So the logical chain is:

[
Q_0\ge0
\Longrightarrow
\text{positive real representing measure}
\Longrightarrow
\text{non-real divisor atoms impossible by poles}
\Longrightarrow
\text{negative real divisor atoms impossible by measure positivity}
\Longrightarrow
y_\rho>0
\Longrightarrow
RH.
]

The uploaded bridge file phrases this as the “source-aware refinement”: for the actual zero divisor, all-order (Q_0[p]\ge0) alone forces (y_\rho\in\mathbb R_{>0}); the companion (Q_1) is only needed in the source-forgotten abstract moment problem.

---

# 5. Roleplaying audit

What is proven here:

[
\boxed{
Q_0[p]\ge0\ \forall p
\Rightarrow RH
}
]

for the actual folded divisor.

What is **not** proven here:

[
\boxed{
\text{completion + explicit formula + Γ-boundary}
\Rightarrow
Q_0[p]\ge0\ \forall p.
}
]

That second implication is the actual open bridge theorem. The corpus repeatedly warns that naming an RH-equivalent positivity criterion is not progress unless the object is source-built, completed, faithful, fake-family separating, and no-margin compatible.

So this lemma passes the “not roleplaying” test only in the modest sense: it is a precise, checkable reduction. It does not pretend to cross the wall.

The genuinely hard theorem remains:

[
\boxed{
\text{prove }Q_0[p]\ge0\text{ from source data without reading the zeros.}
}
]

That is still open.
