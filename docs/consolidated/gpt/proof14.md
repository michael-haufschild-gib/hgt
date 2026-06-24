Below is the finite lemma exactly. It is **standard rank-one linear algebra**, not a new RH theorem. What is project-specific is the instantiation:

[
y_*=-0.16,\qquad a_*=0.16,
\qquad
H_d^0=[T_{i+j+1}],
\qquad
H_d^-=H_d^0-a_*v_*v_*^T.
]

The uploaded bridge notes define the reciprocal-seam coordinate and the shifted (Q_0) tower as the proposed “last bridge” coordinate; they also explicitly warn that naming equivalent positivity is not a proof of RH.

---

# Rank-one Uvarov / Weyl identities

Fix (d\ge0). Let

[
e_d(y)=(1,y,y^2,\dots,y^d)^T.
]

Let

[
H_d^0=[T_{i+j+1}]_{i,j=0}^d.
]

This is the shifted reciprocal Hankel matrix associated to

[
Q_0[p]=\sum_{i,j=0}^d c_i c_jT_{i+j+1}.
]

Let the first Γ-trivial boundary point be

[
y_*=-a_*,
\qquad
a_*=(5/2)^{-2}=0.16,
\qquad
y_*=-0.16.
]

Define

[
v_*:=e_d(y_*)=(1,y_*,y_*^2,\dots,y_*^d)^T.
]

Define the unrepaired / boundary-deleted matrix

[
\boxed{
H_d^-:=H_d^0-a_*v_*v_*^T.
}
]

Then immediately

[
\boxed{
H_d^0=H_d^-+a_*v_*v_*^T.
}
]

This is the first identity.

---

# Measure interpretation

Let the folded reciprocal divisor be

[
\mathcal Y={(y_\alpha,M_\alpha)},
\qquad
y_\alpha=-(\rho-\tfrac12)^{-2}.
]

Define the shifted signed moment functional

[
\nu'=\sum_\alpha M_\alpha y_\alpha,\delta_{y_\alpha}.
]

Then

[
(H_d^0)_{ij}
============

# T_{i+j+1}

# \sum_\alpha M_\alpha y_\alpha^{i+j+1}

\int y^{i+j},d\nu'(y).
]

Now define the Uvarov-deleted signed measure

[
\boxed{
\sigma:=\nu'-a_*\delta_{y_*}.
}
]

Then

[
(H_d^-)_{ij}
============

\int y^{i+j},d\sigma(y).
]

So the identity

[
H_d^0=H_d^-+a_*v_*v_*^T
]

is exactly the statement

[
\nu'=\sigma+a_*\delta_{y_*}.
]

No RH is used here.

---

# Define (m_d), (K_{\nu'}), and (B_d)

Assume (H_d^-) and (H_d^0) are invertible. Define

[
\boxed{
m_d:=v_*^T(H_d^-)^{-1}v_*.
}
]

Define the finite Christoffel / reproducing kernel of (H_d^0) by

[
\boxed{
K_{\nu',d}(y,z):=
e_d(y)^T(H_d^0)^{-1}e_d(z).
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
B_d=
\begin{pmatrix}
0 & v_*^T\
v_* & H_d^-
\end{pmatrix}.
}
]

We will prove

[
\boxed{
s_d
:=
a_*+\frac1{m_d}
===============

# \frac1{K_{\nu',d}(y_*,y_*)}

-\frac{\det H_d^0}{\det B_d}.
}
]

---

# 1. Sherman–Morrison identity

Start from

[
H_d^0=H_d^-+a_*v_*v_*^T.
]

Set

[
A=H_d^-,
\qquad
v=v_*,
\qquad
a=a_*.
]

Then

[
H_d^0=A+avv^T.
]

The Sherman–Morrison formula gives

[
(A+avv^T)^{-1}
==============

## A^{-1}

\frac{aA^{-1}vv^TA^{-1}}{1+a,v^TA^{-1}v}.
]

Since

[
m_d=v^TA^{-1}v,
]

we get

[
(H_d^0)^{-1}
============

## (H_d^-)^{-1}

\frac{a_*(H_d^-)^{-1}v_*v_*^T(H_d^-)^{-1}}
{1+a_*m_d}.
]

Now sandwich by (v_*^T) and (v_*):

[
\begin{aligned}
K_{\nu',d}(y_*,y_*)
&=
v_*^T(H_d^0)^{-1}v_*\
&=
m_d-\frac{a_*m_d^2}{1+a_*m_d}\
&=
\frac{m_d(1+a_*m_d)-a_*m_d^2}{1+a_*m_d}\
&=
\frac{m_d}{1+a_*m_d}.
\end{aligned}
]

Therefore

[
\frac1{K_{\nu',d}(y_*,y_*)}
===========================

# \frac{1+a_*m_d}{m_d}

a_*+\frac1{m_d}.
]

So

[
\boxed{
a_*+\frac1{m_d}
===============

\frac1{K_{\nu',d}(y_*,y_*)}.
}
]

This proves the Weyl/Christoffel identity.

---

# 2. Determinant identity

The matrix determinant lemma gives

[
\det(A+avv^T)
=============

\det(A)(1+a,v^TA^{-1}v).
]

Thus

[
\boxed{
\det H_d^0
==========

\det H_d^-(1+a_*m_d).
}
]

Now compute the determinant of the bordered matrix

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

\det(H_d^-),
\det!\left(0-v_*^T(H_d^-)^{-1}v_*\right).
]

Since the upper-left block is scalar,

[
\det!\left(-v_*^T(H_d^-)^{-1}v_*\right)
=======================================

-m_d.
]

Therefore

[
\boxed{
\det B_d
========

-m_d,\det H_d^-.
}
]

Now divide:

[
-\frac{\det H_d^0}{\det B_d}
============================

-\frac{\det H_d^-(1+a_*m_d)}
{-m_d\det H_d^-}.
]

Cancel (\det H_d^-):

[
-\frac{\det H_d^0}{\det B_d}
============================

# \frac{1+a_*m_d}{m_d}

a_*+\frac1{m_d}.
]

Hence

[
\boxed{
-\frac{\det H_d^0}{\det B_d}
============================

a_*+\frac1{m_d}.
}
]

Combining with the previous section,

[
\boxed{
s_d
===

# a_*+\frac1{m_d}

# \frac1{K_{\nu',d}(y_*,y_*)}

-\frac{\det H_d^0}{\det B_d}.
}
]

That proves the full rank-one identity chain.

---

# 3. Sign interpretation

If

[
\operatorname{inertia}(H_d^-)=(d,1),
]

then (H_d^-) has exactly one negative square. The rank-one update

[
H_d^0=H_d^-+a_*v_*v_*^T
]

repairs that one negative direction precisely when

[
\boxed{
s_d=a_*+\frac1{m_d}>0.
}
]

Equivalently,

[
\boxed{
K_{\nu',d}(y_*,y_*)>0
}
]

in the repaired presentation, or

[
\boxed{
-\frac{\det H_d^0}{\det B_d}>0
}
]

in the tau/determinant presentation.

So, under the one-defect hypothesis, the scalar (s_d) is the exact boundary-Weyl gate.

---

# 4. What is actually proven here

This proves only the finite algebra:

[
\boxed{
H_d^0=H_d^-+a_*v_*v_*^T,
}
]

[
\boxed{
s_d
===

# a_*+\frac1{m_d}

# \frac1{K_{\nu',d}(y_*,y_*)}

-\frac{\det H_d^0}{\det B_d}.
}
]

It does **not** prove

[
s_d>0\quad\forall d.
]

It does **not** prove RH.

It does **not** construct (H_d^-) from the completed explicit formula without zero-feeding.

The open theorem remains the source-built positivity step: construct the completed object from Euler product, Γ, pole, and functional equation data, and prove the scalar gate remains positive at every degree. The theorem-chain notes state this as the required “source-built faithful index” obligation, rather than another RH-equivalent restatement.

---

# 5. Why this is not role-playing

The lemma is falsifiable by direct calculation:

Given any invertible real symmetric matrix (H^-), any vector (v), and any scalar (a), set

[
H^0=H^-+avv^T,
\qquad
m=v^T(H^-)^{-1}v,
\qquad
B=
\begin{pmatrix}
0&v^T\
v&H^-
\end{pmatrix}.
]

Then, whenever the inverses exist,

[
a+\frac1m
=========

# \frac1{v^T(H^0)^{-1}v}

-\frac{\det H^0}{\det B}.
]

The ζ-specific content is only the substitution

[
v=v_*=(1,-0.16,(-0.16)^2,\dots)^T,
\qquad
a=a_*=0.16,
\qquad
H^0=[T_{i+j+1}].
]

Everything else is finite-dimensional algebra. The identity is real; its positivity is the open wall.
