Below is the cleanest “paper-math” version I think is defensible.

The key correction is this:

[
\mathcal Q_{\max}-\mathcal Q_{\min}
]

is a **Hermitian quadratic boundary term**, while the usual Green identity

[
\langle S_{\max}f,g\rangle-\langle f,S_{\max}g\rangle
=====================================================

## \langle \Gamma_1f,\Gamma_0g\rangle

\langle \Gamma_0f,\Gamma_1g\rangle
]

is **skew-Hermitian / symplectic**. So the rank-one repair

[
a_*p(y_*)\overline{q(y_*)}
]

is not literally the skew Green form. It is the **quadratic form of a self-adjoint boundary extension** selected by the Green identity. That distinction matters.

So the correct target is:

[
\boxed{
\text{Green identity at the seam}
\quad\Longrightarrow\quad
\text{self-adjoint boundary parameter }\Theta=a_*
\quad\Longrightarrow\quad
H_d^0=H_d^-+a_*v_*v_*^{*}.
}
]

For ζ,

[
y_*=-0.16=-(5/2)^{-2},
\qquad
a_*=0.16=(5/2)^{-2}.
]

This matches the source-built Γ-boundary atom already isolated in the bridge theorem / archimedean square-sum picture.

---

# Local seam Green identity: rank-one Γ-boundary model

## 1. Seam variable and singular pullback

Let

[
\Xi(w)=\xi!\left(\frac12+w\right),
\qquad
y=-w^{-2}.
]

For a polynomial

[
p(y)=\sum_{i=0}^{d}c_i y^i,
]

define the singular seam section

[
F_p(w):=p(-w^{-2}).
]

Then

[
F_p(w)
======

\sum_{i=0}^{d}c_i(-1)^i w^{-2i}.
]

The zero-side shifted reciprocal form is obtained by pairing the bilinear singular test

[
h_{p,q}(w):=-w^{-2}p(-w^{-2})\overline{q(-w^{-2})}
==================================================

y,p(y)\overline{q(y)}
]

against the completed zero divisor:

[
Q_0[p,q]
========

\sum_{\rho}m_\rho y_\rho p(y_\rho)\overline{q(y_\rho)}.
]

For (p=q),

[
Q_0[p]=\sum_{\rho}m_\rho y_\rho |p(y_\rho)|^2.
]

The bridge theorem’s reciprocal coordinate is exactly this (y_\rho=-(\rho-\frac12)^{-2}), and all-order positivity of (Q_0) forces the folded zero divisor onto (\mathbb R_{>0}), hence RH.

---

## 2. The local seam jet space

Let

[
\mathcal J_d
============

\left{
F_p(w)=p(-w^{-2}) : \deg p\le d
\right}.
]

This is the finite Laurent-jet sector at the seam (w=0):

[
F_p(w)
======

\sum_{i=0}^{d} a_iw^{-2i},
\qquad
a_i=c_i(-1)^i.
]

Therefore

[
c_i=(-1)^ia_i.
]

The first Γ-trivial image is

[
y_*=-a_*,
\qquad
a_*=|y_*|=(5/2)^{-2}=0.16.
]

Define the seam boundary trace

[
\boxed{
\Gamma_0F_p:=p(y_*).
}
]

In terms of Laurent coefficients,

[
\Gamma_0F_p
===========

# \sum_{i=0}^{d}c_i y_*^i

# \sum_{i=0}^{d}(-1)^ia_i y_*^i

\sum_{i=0}^{d}a_i a_*^i.
]

So (\Gamma_0) is a genuine **local seam-jet functional**: it only reads the Laurent coefficients of (F_p) at (w=0).

Equivalently,

[
\boxed{
\Gamma_0F_p
===========

\sum_{i=0}^{d}
a_*^i [w^{-2i}]F_p(w).
}
]

This proves the “trace collapse”:

[
\boxed{
F_p\longmapsto \Gamma_0F_p=p(y_*).
}
]

The vector form is

[
v_*=(1,y_*,y_*^2,\dots,y_*^d)^T,
]

so for coefficient vector (c=(c_0,\dots,c_d)^T),

[
\Gamma_0F_p
===========

c^Tv_*.
]

Thus the boundary trace is exactly the evaluation vector already observed numerically.

---

## 3. The abstract seam Green identity

Let (\mathcal K_{\max}) be the finite-part maximal seam domain containing the singular jet space (\mathcal J_d). Let (\mathcal K_{\min}\subset\mathcal K_{\max}) be the minimal domain obtained by killing the seam boundary trace.

Assume the seam finite-part operator (S_{\max}) has a one-dimensional boundary space

[
\mathcal E=\mathbb C
]

with boundary maps

[
\Gamma_0,\Gamma_1:\mathcal K_{\max}\to\mathbb C.
]

The local Green identity is

[
\boxed{
[S_{\max}f,g]-[f,S_{\max}g]
===========================

## \Gamma_1f,\overline{\Gamma_0g}

\Gamma_0f,\overline{\Gamma_1g}.
}
]

This is the ordinary boundary-triple / Lagrange identity.

It says: the obstruction to symmetry of the maximal seam operator is completely carried by the two boundary traces at (w=0).

The minimal domain is

[
\mathcal K_{\min}
=================

\ker\Gamma_0\cap\ker\Gamma_1.
]

A self-adjoint boundary extension is obtained by imposing

[
\boxed{
\Gamma_1 f=\Theta\Gamma_0 f
}
]

with real (\Theta). In our rank-one Γ-boundary case,

[
\Theta=a_*.
]

Then the boundary contribution to the associated closed quadratic form is

[
\boxed{
\mathfrak b_\Theta[f,g]
=======================

\Theta,\Gamma_0f,\overline{\Gamma_0g}.
}
]

For the singular pullbacks (F_p,F_q),

[
\mathfrak b_{a_*}[F_p,F_q]
==========================

a_*p(y_*)\overline{q(y_*)}.
]

This is the desired rank-one boundary term.

So the precise relation is:

[
\boxed{
\text{Green identity}
\Rightarrow
\text{self-adjoint boundary parameter }a_*
\Rightarrow
\mathcal Q_{a_*}[F_p,F_q]
=========================

\mathcal Q_{0}[F_p,F_q]
+
a_*p(y_*)\overline{q(y_*)}.
}
]

Again: the skew Green identity produces the boundary triple; the rank-one positive term is the quadratic form of the chosen self-adjoint extension.

---

## 4. Source selection of (y_*) and (a_*)

The Γ-factor supplies the archimedean square-sum

[
Q_{\mathrm{arch}}[p]
====================

-4p(-4)^2
+
\sum_{j\ge1}
(2j+\tfrac12)^{-2}
p!\left(-(2j+\tfrac12)^{-2}\right)^2.
]

Write

[
y_j=-(2j+\tfrac12)^{-2},
\qquad
a_j=(2j+\tfrac12)^{-2}.
]

Then

[
Q_{\mathrm{arch}}[p]
====================

-4p(-4)^2
+
\sum_{j\ge1}a_jp(y_j)^2.
]

The first active trivial-zero atom is

[
j=1:
\qquad
y_*=y_1=-(5/2)^{-2}=-0.16,
\qquad
a_*=a_1=(5/2)^{-2}=0.16.
]

So the Γ-factor selects both:

[
\boxed{
\Gamma_0F_p=p(y_*),
\qquad
\Theta=a_*.
}
]

This is source-built: (y_*) and (a_*) come from the first Γ-trivial-zero term, not from the nontrivial zeros.

The files already identify the Γ-factor as the archimedean boundary-condition operator in the completed transport system, and the RH-bearing form as the faithful archimedean positivity / Krein index rather than a prime-side amplitude.

---

## 5. The finite matrix identity follows

Define the completed shifted reciprocal form

[
H_d^0[p,q]
==========

Q_0[p,q].
]

Split off the first Γ-boundary atom:

[
H_d^-[p,q]
:=
H_d^0[p,q]
----------

a_*p(y_*)\overline{q(y_*)}.
]

Using the boundary trace,

[
p(y_*)=\Gamma_0F_p,
\qquad
q(y_*)=\Gamma_0F_q,
]

we get

[
\boxed{
H_d^0[p,q]
==========

H_d^-[p,q]
+
a_*,\Gamma_0F_p,\overline{\Gamma_0F_q}.
}
]

In coefficient form,

[
p(y_*)=c^Tv_*,
\qquad
q(y_*)=d^Tv_*.
]

Therefore

[
a_*p(y_*)\overline{q(y_*)}
==========================

c^T(a_*v_*v_*^*)\overline d.
]

Thus,

[
\boxed{
H_d^0
=====

H_d^-
+
a_*v_*v_*^*.
}
]

This is exactly the finite matrix identity, now expressed as the quadratic-form consequence of a rank-one self-adjoint boundary extension.

---

## 6. The scalar Weyl gap

Assume the one-defect bulk theorem:

[
\operatorname{inertia}(H_d^-)=(d,1).
]

Define the Weyl (m)-quantity

[
m_d
===

v_*^*(H_d^-)^{-1}v_*.
]

Then the rank-one extension

[
H_d^0=H_d^-+a_*v_*v_*^*
]

is positive semidefinite iff

[
\boxed{
s_d:=a_*+\frac1{m_d}>0.
}
]

This is the rank-one Krein/Weyl threshold. The critical mass is

[
a_c(d)=-\frac1{m_d}.
]

So

[
H_d^0\succeq0
\quad\Longleftrightarrow\quad
a_*>a_c(d)
\quad\Longleftrightarrow\quad
a_*+\frac1{m_d}>0.
]

By Sherman–Morrison,

[
v_*^*(H_d^0)^{-1}v_*
====================

\frac{m_d}{1+a_*m_d},
]

so

[
\boxed{
\frac1{v_*^*(H_d^0)^{-1}v_*}
============================

# a_*+\frac1{m_d}

s_d.
}
]

But

[
v_*^*(H_d^0)^{-1}v_*
====================

K_{\nu'}(y_*,y_*),
]

the exterior Christoffel kernel of the shifted reciprocal zero measure at (y_*). Hence

[
\boxed{
s_d
===

\frac1{K_{\nu'}(y_*,y_*)}.
}
]

For ζ,

[
\boxed{
s_d
===

# 0.16+\frac1{m_d}

\frac1{K_{\nu'}(-0.16,-0.16)}.
}
]

This is the scalar boundary-Weyl gap.

---

## 7. The local Green theorem, stated cleanly

Here is the theorem in final form.

### Theorem — local seam Green identity and Γ-boundary repair

Let

[
F_p(w)=p(-w^{-2})
]

be the singular seam pullback of a polynomial (p). Let (\mathcal K_{\max}) be a finite-part seam domain containing these Laurent jets, and suppose (S_{\max}) has boundary maps

[
\Gamma_0,\Gamma_1:\mathcal K_{\max}\to\mathbb C
]

satisfying the local Green identity

[
[S_{\max}f,g]-[f,S_{\max}g]
===========================

## \Gamma_1f,\overline{\Gamma_0g}

\Gamma_0f,\overline{\Gamma_1g}.
]

Define the seam trace on singular pullbacks by

[
\Gamma_0F_p=p(y_*),
\qquad
y_*=-0.16.
]

Then the Γ-factor selects the self-adjoint boundary parameter

[
\Theta=a_*=0.16.
]

The associated self-adjoint boundary form satisfies

[
\mathcal Q_{\Theta}[F_p,F_q]
============================

\mathcal Q_{\mathrm{bulk}}[F_p,F_q]
+
a_*p(y_*)\overline{q(y_*)}.
]

Consequently, in the polynomial coefficient basis,

[
\boxed{
H_d^0
=====

H_d^-
+
a_*v_*v_*^*,
\qquad
v_*=(1,y_*,y_*^2,\dots,y_*^d)^T.
}
]

If additionally

[
\operatorname{inertia}(H_d^-)=(d,1),
]

then positivity of the completed form is equivalent to the scalar Weyl inequality

[
\boxed{
a_*+\frac1{v_*^*(H_d^-)^{-1}v_*}>0.
}
]

Equivalently,

[
\boxed{
\frac1{K_{\nu'}(y_*,y_*)}>0.
}
]

---

## 8. Proof

The proof is now short.

First, (F_p(w)=p(-w^{-2})) has Laurent expansion

[
F_p(w)=\sum_{i=0}^{d}c_i(-1)^iw^{-2i}.
]

Thus the map

[
\Gamma_0F_p
===========

# \sum_{i=0}^{d}c_i y_*^i

p(y_*)
]

is a local seam-jet trace. This proves the trace collapse.

Second, the Γ-factor’s archimedean square-sum contains the first trivial-zero term

[
a_*p(y_*)\overline{q(y_*)},
]

with

[
y_*=-0.16,
\qquad
a_*=0.16.
]

So the boundary parameter selected by the Γ-factor is (\Theta=a_*).

Third, a one-dimensional boundary triple with Green identity gives self-adjoint extensions parametrized by real (\Theta), and the corresponding quadratic forms differ by

[
\Theta,\Gamma_0F_p,\overline{\Gamma_0F_q}.
]

Therefore, for (\Theta=a_*),

[
H_d^0[p,q]
==========

H_d^-[p,q]
+
a_*p(y_*)\overline{q(y_*)}.
]

In matrix form this is

[
H_d^0
=====

H_d^-
+
a_*v_*v_*^*.
]

Finally, the rank-one Weyl / Schur complement computation gives

[
H_d^0\succeq0
\Longleftrightarrow
a_*+\frac1{v_*^*(H_d^-)^{-1}v_*}>0
]

under the one-defect hypothesis. Sherman–Morrison identifies the same scalar with the inverse exterior Christoffel kernel:

[
a_*+\frac1{m_d}
===============

\frac1{K_{\nu'}(y_*,y_*)}.
]

This completes the local Green-to-boundary-repair proof.

---

## 9. What this proves, and what it does not prove yet

This proves the **local operator-domain form** of the finite matrix identity:

[
\boxed{
H_d^0=H_d^-+0.16,v_{-0.16}v_{-0.16}^*.
}
]

It also proves that the trace

[
p\mapsto p(-0.16)
]

is a seam-jet boundary trace of the singular pullback (p(-w^{-2})).

It does **not** yet prove RH, and it does not yet construct the full global de Branges/Krein finite-part space. The remaining analytic work is:

[
\boxed{
\text{construct }\mathcal K_{\max}\text{ canonically from the completed explicit formula,}
}
]

[
\boxed{
\text{prove the finite-part seam distribution equals the Hankel tail }\mu_E,
}
]

[
\boxed{
\text{prove }\operatorname{inertia}(H_d^-)=(d,1)\text{ and }s_d>0\text{ for all }d.
}
]

That is exactly the “source-built object” obligation emphasized in the theorem-chain files: merely naming an RH-equivalent positivity is not progress; the object must be completed, faithful, source-built, fake-family separating, and no-margin compatible.

So the local Green identity gives the right operator-domain language. The global proof still needs the canonical finite-part construction that turns the observed Hankel tail into the actual seam-centre boundary distribution.
