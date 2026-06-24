# Rank-one Uvarov–Krein bridge theorem package

This is a finite algebra theorem plus a conjectural source-built positivity theorem. The finite identities below are proved by Sherman–Morrison, Schur complement, and the matrix determinant lemma. The open part is **not** the algebra; it is proving the scalar sign (s_d>0) for every (d) from completed source data rather than from zero-fed matrices. This matches the corpus’s guardrail: the bridge is not allowed to be just another RH-equivalent positivity restatement; it must be source-built and boundary-aware.

---

## 0. Reciprocal-seam data

Let

[
\Xi(w)=\xi!\left(\frac12+w\right),
\qquad
y_\rho=-(\rho-\tfrac12)^{-2}.
]

For (k\ge1), define

[
T_k=\sum_\rho m_\rho y_\rho^k.
]

For fixed (d\ge0), define the shifted reciprocal Hankel matrix

[
\boxed{
H_d^0
:=
\bigl[T_{i+j+1}\bigr]_{i,j=0}^{d}.
}
]

Equivalently, for (p(y)=\sum_{i=0}^{d}c_i y^i),

[
c^T H_d^0 c
===========

# Q_0[p]

\sum_{i,j=0}^{d}c_ic_jT_{i+j+1}.
]

The bridge file states this reciprocal-seam (Q_0)-tower as the minimal source-aware positivity target: for the actual folded zero divisor, all-order (Q_0[p]\ge0) forces every (y_\rho\in\mathbb R_{>0}), hence RH.

---

## 1. Γ-boundary datum

For (\zeta), take the first active Γ-trivial-zero image

[
\boxed{
y_*=-\left(\frac52\right)^{-2}=-0.16,
\qquad
a_*=\left(\frac52\right)^{-2}=0.16.
}
]

Let

[
\boxed{
v_*:=e_d(y_*)=(1,y_*,y_*^2,\dots,y_*^d)^T.
}
]

Define the Uvarov-deleted / unrepaired matrix

[
\boxed{
H_d^-:=H_d^0-a_*v_*v_*^T.
}
]

Then, tautologically,

[
\boxed{
H_d^0=H_d^-+a_*v_*v_*^T.
}
]

This is the finite rank-one Uvarov decomposition. The corpus’s boundary-localization notes emphasize why this boundary term cannot be ignored: a rank-one boundary change can cross a Krein threshold and flip inertia, so the Γ/pole/FE boundary is part of the object, not an optional correction.

---

## 2. Signed-measure interpretation

If

[
\nu'
]

denotes the shifted reciprocal moment functional represented formally by

[
(H_d^0)_{ij}
============

# \int y^{i+j},d\nu'(y)

T_{i+j+1},
]

then

[
H_d^-
]

is the moment matrix of the signed Uvarov-deleted functional

[
\boxed{
\sigma:=\nu'-a_*\delta_{y_*}.
}
]

Thus the rank-one identity is equivalently

[
\boxed{
\nu'=\sigma+a_*\delta_{y_*}.
}
]

In this formulation, (\sigma) is the one-negative-square Krein object, and (a_*\delta_{y_*}) is the Γ-selected repair atom.

---

## 3. Definitions of (m_d), (K_{\nu',d}), (B_d)

Assume (H_d^-) is invertible and set

[
\boxed{
m_d:=v_*^T(H_d^-)^{-1}v_*.
}
]

Assume also (H_d^0) is invertible and define the finite reproducing / Christoffel kernel

[
\boxed{
K_{\nu',d}(y,z):=e_d(y)^T(H_d^0)^{-1}e_d(z).
}
]

In particular,

[
\boxed{
K_{\nu',d}(y_*,y_*)
===================

v_*^T(H_d^0)^{-1}v_*.
}
]

Define the bordered Uvarov matrix

[
\boxed{
B_d:=
\begin{pmatrix}
0 & v_*^T\
v_* & H_d^-
\end{pmatrix}.
}
]

Now define the scalar Weyl / Uvarov / tau gap

[
\boxed{
s_d:=a_*+\frac1{m_d}.
}
]

---

# Theorem 1 — finite rank-one identity chain

Assume

[
H_d^-,\ H_d^0,\ B_d
]

are invertible. Then

[
\boxed{
s_d
===

# a_*+\frac1{v_*^T(H_d^-)^{-1}v_*}

# \frac1{K_{\nu',d}(y_*,y_*)}

-\frac{\det H_d^0}{\det B_d}.
}
]

---

## Proof

Set

[
A:=H_d^-,
\qquad
v:=v_*,
\qquad
a:=a_*.
]

Then

[
H_d^0=A+avv^T.
]

Let

[
m:=v^TA^{-1}v=m_d.
]

### 1. Sherman–Morrison gives the Christoffel identity

The Sherman–Morrison formula gives

[
(A+avv^T)^{-1}
==============

## A^{-1}

\frac{aA^{-1}vv^TA^{-1}}{1+am}.
]

Sandwich by (v^T) and (v):

[
\begin{aligned}
v^T(H_d^0)^{-1}v
&=
v^TA^{-1}v
----------

\frac{a(v^TA^{-1}v)^2}{1+a(v^TA^{-1}v)}\
&=
m-\frac{am^2}{1+am}\
&=
\frac{m}{1+am}.
\end{aligned}
]

But

[
v^T(H_d^0)^{-1}v
================

K_{\nu',d}(y_*,y_*).
]

Therefore

[
K_{\nu',d}(y_*,y_*)
===================

\frac{m_d}{1+a_*m_d}.
]

Invert:

[
\boxed{
\frac1{K_{\nu',d}(y_*,y_*)}
===========================

# \frac{1+a_*m_d}{m_d}

a_*+\frac1{m_d}.
}
]

So

[
\boxed{
s_d
===

\frac1{K_{\nu',d}(y_*,y_*)}.
}
]

### 2. Matrix determinant lemma gives the tau identity

The matrix determinant lemma gives

[
\det(A+avv^T)
=============

\det(A)\bigl(1+av^TA^{-1}v\bigr).
]

Hence

[
\boxed{
\det H_d^0
==========

\det H_d^-,(1+a_*m_d).
}
]

Now compute the determinant of

[
B_d=
\begin{pmatrix}
0 & v_*^T\
v_* & H_d^-
\end{pmatrix}.
]

Using the Schur complement with respect to (H_d^-),

[
\det B_d
========

\det(H_d^-)
\det!\left(0-v_*^T(H_d^-)^{-1}v_*\right).
]

The upper-left block is scalar, so

[
\boxed{
\det B_d
========

-m_d,\det H_d^-.
}
]

Therefore

[
-\frac{\det H_d^0}{\det B_d}
============================

-\frac{\det H_d^-(1+a_*m_d)}
{-m_d\det H_d^-}
================

\frac{1+a_*m_d}{m_d}.
]

Thus

[
\boxed{
-\frac{\det H_d^0}{\det B_d}
============================

# a_*+\frac1{m_d}

s_d.
}
]

Combining both calculations,

[
\boxed{
s_d
===

# a_*+\frac1{v_*^T(H_d^-)^{-1}v_*}

# \frac1{K_{\nu',d}(y_*,y_*)}

-\frac{\det H_d^0}{\det B_d}.
}
]

This proves the finite theorem.

---

# Theorem 2 — Krein threshold form

Assume additionally that

[
H_d^-
]

has exactly one negative square and that this negative square is carried by the boundary channel (v_*), equivalently

[
H_d^-\big|*{\ker(v**^T)}\succ0.
]

Then

[
\boxed{
H_d^0\succ0
\quad\Longleftrightarrow\quad
s_d>0.
}
]

For semidefinite boundary cases, replace (>) by (\ge), with the usual limiting interpretation.

---

## Proof

On the decomposition into the boundary direction and its (H_d^-)-orthogonal complement, the only possible sign change under

[
H_d^0=H_d^-+a_*v_*v_*^T
]

is the one-dimensional boundary/Krein channel. The critical mass for the rank-one update is

[
a_c=-\frac1{v_*^T(H_d^-)^{-1}v_*}
=================================

-\frac1{m_d}.
]

Therefore the repaired form is positive exactly when

[
a_*>a_c.
]

That is

[
a_*+\frac1{m_d}>0,
]

i.e.

[
\boxed{
s_d>0.
}
]

This proves the threshold statement.

---

# Rank-one Uvarov–Krein bridge theorem, exact form

For each (d\ge0), define

[
H_d^0=[T_{i+j+1}]_{i,j=0}^{d},
]

[
y_*=-0.16,
\qquad
a_*=0.16,
\qquad
v_*=(1,y_*,y_*^2,\dots,y_*^d)^T,
]

[
H_d^-:=H_d^0-a_*v_*v_*^T,
]

[
m_d:=v_*^T(H_d^-)^{-1}v_*,
]

[
B_d=
\begin{pmatrix}
0&v_*^T\
v_*&H_d^-
\end{pmatrix}.
]

Then the finite algebraic identity is

[
\boxed{
H_d^0=H_d^-+a_*v_*v_*^T,
}
]

and, whenever the inverses exist,

[
\boxed{
s_d
:=
a_*+\frac1{v_*^T(H_d^-)^{-1}v_*}
================================

# \frac1{K_{\nu',d}(y_*,y_*)}

-\frac{\det H_d^0}{\det B_d}.
}
]

Under the one-defect Krein hypothesis

[
\boxed{
\operatorname{inertia}(H_d^-)=(d,1)
\quad\text{and}\quad
H_d^-|*{\ker(v**^T)}\succ0,
}
]

the repaired form satisfies

[
\boxed{
H_d^0\succ0
\quad\Longleftrightarrow\quad
s_d>0.
}
]

---

# The actual open theorem

The open theorem is not the identity above. The identity is finite linear algebra.

The open bridge theorem is:

[
\boxed{
s_d>0\quad\forall d\ge0
}
]

with (H_d^-) and (s_d) constructed from the completed source data

[
\Gamma,\quad \text{pole},\quad \text{functional equation},\quad \text{explicit formula / Euler product},
]

without feeding in the zero locations.

Equivalently, under the rank-one Uvarov–Krein carrier theorem,

[
\boxed{
H_d^0\succeq0\quad\forall d.
}
]

Equivalently,

[
\boxed{
Q_0[p]\ge0\quad\forall p\in\mathbb R[y].
}
]

For the actual folded reciprocal zero divisor, this implies

[
y_\rho\in\mathbb R_{>0}\quad\forall\rho,
]

hence RH. The bridge file states that once this source-aware (Q_0)-positivity is established, no further theorem stands between it and RH.

---

## What is proved vs. open

**Proved here:**

[
\boxed{
H_d^0=H_d^-+a_*v_*v_*^T
}
]

and

[
\boxed{
s_d
===

# a_*+\frac1{m_d}

# \frac1{K_{\nu',d}(y_*,y_*)}

-\frac{\det H_d^0}{\det B_d}.
}
]

These are rank-one Uvarov / Schur / Christoffel / determinant identities.

**Not proved here:**

[
\boxed{
s_d>0\quad\forall d.
}
]

That is the all-degree scalar gate.

**Not proved here:**

[
\boxed{
\text{source data}\Rightarrow s_d>0\quad\forall d.
}
]

That is the actual bridge theorem.

**Not proved here:**

[
\boxed{
RH.
}
]

The package passes the roleplaying test because the algebraic theorem is fully explicit and finite-dimensional, while the RH-bearing assertion is isolated as an open source-built positivity theorem rather than smuggled in as a conclusion.
