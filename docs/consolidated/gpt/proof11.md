# Kernel theorem from comp70

The clean finite theorem is a **Christoffel/Uvarov boundary-removal identity**.

Let

[
e_d(y)=(1,y,\dots,y^d)^T,
]

and let

[
H_d^0=[T_{i+j+1}]_{i,j=0}^d
]

be the shifted reciprocal Hankel form of the folded zero divisor. In the bridge notation,

[
H_d^0[p,q]=Q_0[p,q],
\qquad
\nu'=\sum_\rho 2y_\rho,\delta_{y_\rho},
\qquad
y_\rho=-(\rho-\tfrac12)^{-2}.
]

The corpus already identifies (H_d^0) as the moment matrix of (\nu'), with the Christoffel kernel

[
K_{\nu',d}(y,z)=e_d(y)^T(H_d^0)^{-1}e_d(z),
]

and records the inverse-Christoffel identity at the coarsest trivial-zero boundary point (y_*=-0.16).

Set

[
v_*=e_d(y_*),
\qquad
y_*=-0.16,
\qquad
a_*=0.16.
]

Define

[
K_{**}:=K_{\nu',d}(y_*,y_*)=v_*^T(H_d^0)^{-1}v_*,
]

and

[
s_d:=\frac1{K_{**}}.
]

Then comp70’s identity is exactly

[
\boxed{
K_d^{\mathrm{crit}}(y,y)
========================

## K_{\nu',d}(y,y)

s_d\left(e_d(y)^T(H_d^0)^{-1}v_*\right)^2.
}
]

Equivalently,

[
\boxed{
K_d^{\mathrm{crit}}(y,z)
========================

## K_{\nu',d}(y,z)

\frac{K_{\nu',d}(y,y_*)K_{\nu',d}(y_*,z)}
{K_{\nu',d}(y_*,y_*)}.
}
]

This is the exact reproducing-kernel formula for **removing the boundary evaluation at (y_*)**.

---

## The finite-dimensional theorem

### Theorem — boundary Christoffel projection

Assume (H_d^0) is nonsingular. Let (\mathcal P_d) be the space of polynomials of degree (\le d), with inner product

[
\langle p,q\rangle_0
====================

c^T H_d^0 \overline d,
]

where (c,d) are coefficient vectors of (p,q). Define

[
K_{\nu',d}(y,z)=e_d(y)^T(H_d^0)^{-1}e_d(z).
]

Then the kernel of the codimension-one subspace

[
\mathcal P_d^{0}
================

{p\in \mathcal P_d: p(y_*)=0}
]

is

[
\boxed{
K_d^{\mathrm{crit}}(y,z)
========================

## K_{\nu',d}(y,z)

\frac{K_{\nu',d}(y,y_*)K_{\nu',d}(y_*,z)}
{K_{\nu',d}(y_*,y_*)}.
}
]

In diagonal form,

[
\boxed{
K_d^{\mathrm{crit}}(y,y)
========================

## K_{\nu',d}(y,y)

s_d\left(e_d(y)^T(H_d^0)^{-1}v_*\right)^2,
\qquad
s_d=\frac1{K_{\nu',d}(y_*,y_*)}.
}
]

This is exactly the comp70 identity.

---

## Proof

Let

[
k_z(y):=K_{\nu',d}(y,z).
]

By construction,

[
k_z(\cdot)
\quad\text{has coefficient vector}\quad
(H_d^0)^{-1}e_d(z).
]

Therefore, for any (p(y)=c^Te_d(y)),

[
\langle p,k_z\rangle_0
======================

# c^TH_d^0(H_d^0)^{-1}e_d(z)

# c^Te_d(z)

p(z).
]

So (k_z) is the reproducing vector for evaluation at (z).

Now take the boundary point (y_*). Its reproducing vector is (k_*=k_{y_*}), with norm

[
|k_*|_0^2
=========

# K_{\nu',d}(y_*,y_*)

K_{**}.
]

The orthogonal projection of (k_z) onto the complement of the boundary-evaluation direction is

[
k_z^\perp
=========

## k_z

\frac{\langle k_z,k_*\rangle_0}{|k_*|*0^2}k**.
]

But

[
\langle k_z,k_*\rangle_0
========================

K_{\nu',d}(y_*,z).
]

Thus

[
k_z^\perp(y)
============

## K_{\nu',d}(y,z)

\frac{K_{\nu',d}(y,y_*)K_{\nu',d}(y_*,z)}
{K_{\nu',d}(y_*,y_*)}.
]

This is the reproducing kernel of the subspace orthogonal to (k_*), which is precisely the subspace of polynomials satisfying (p(y_*)=0). Hence

[
K_d^{\mathrm{crit}}(y,z)
========================

## K_{\nu',d}(y,z)

\frac{K_{\nu',d}(y,y_*)K_{\nu',d}(y_*,z)}
{K_{\nu',d}(y_*,y_*)}.
]

Setting (z=y) gives the diagonal formula.

So comp70 is not a numerical accident. It is exactly the finite-dimensional Christoffel/Uvarov boundary projection.

---

# Relation to the signed measure (\sigma=\nu'-a_*\delta_{y_*})

There is one subtle but important distinction.

The formula

[
K_{\nu',d}(y,z)
---------------

\frac{K_{\nu',d}(y,y_*)K_{\nu',d}(y_*,z)}
{K_{\nu',d}(y_*,y_*)}
]

is the **critical boundary-compressed kernel**: it removes the evaluation direction at the exact Christoffel threshold.

The actual signed moment matrix is

[
H_d^-
=====

H_d^0-a_*v_*v_*^T,
]

i.e.

[
\sigma=\nu'-a_*\delta_{y_*}.
]

For this actual signed object, Sherman–Morrison gives

[
(H_d^-)^{-1}
============

(H_d^0)^{-1}
+
\frac{a_*}{1-a_*K_{**}}
(H_d^0)^{-1}v_*v_*^T(H_d^0)^{-1}.
]

Therefore its inverse kernel is

[
\boxed{
K_{H^-,d}(y,z)
==============

K_{\nu',d}(y,z)
+
\frac{a_*}{1-a_*K_{**}}
K_{\nu',d}(y,y_*)K_{\nu',d}(y_*,z).
}
]

Since

[
s_d=\frac1{K_{**}},
]

this can be rewritten as

[
\boxed{
K_{H^-,d}(y,z)
==============

## K_{\nu',d}(y,z)

\frac{a_*s_d}{a_*-s_d}
K_{\nu',d}(y,y_*)K_{\nu',d}(y_*,z),
}
]

provided (0<s_d<a_*), which is exactly the one-defect regime.

Now compare this to the critical projection:

[
K_d^{\mathrm{crit}}(y,z)
========================

## K_{\nu',d}(y,z)

s_dK_{\nu',d}(y,y_*)K_{\nu',d}(y_*,z).
]

Subtract:

[
\boxed{
K_{H^-,d}
=========

## K_d^{\mathrm{crit}}

\frac{s_d^2}{a_*-s_d}
K_{\nu',d}(,\cdot,,y_*)K_{\nu',d}(y_*,,\cdot,).
}
]

So the real (\Pi_1) kernel is the critical boundary-compressed kernel plus an **extra infinitesimal oversubtraction**. That extra coefficient is

[
\frac{s_d^2}{a_*-s_d}.
]

Since the observed/no-margin law has (s_d\to0^+), this oversubtraction is one order smaller than the critical projector. This explains why comp70 sees a vanishingly thin boundary dip: the negative square is carried by a rank-one projector whose excess beyond the critical Christoffel projection collapses as (s_d\to0).

So the exact taxonomy is:

[
\boxed{
K_d^{\mathrm{crit}}
===================

## K_{\nu',d}

\frac{K_{\nu',d}(\cdot,y_*)K_{\nu',d}(y_*,\cdot)}
{K_{\nu',d}(y_*,y_*)}
}
]

is the **critical boundary-removal kernel**, while

[
\boxed{
K_{H^-,d}
=========

## K_d^{\mathrm{crit}}

\frac{s_d^2}{a_*-s_d}
K_{\nu',d}(\cdot,y_*)K_{\nu',d}(y_*,\cdot)
}
]

is the actual **one-negative-square signed kernel** for

[
\sigma=\nu'-a_*\delta_{y_*}.
]

This distinction matters. The corpus explicitly warns that the boundary extension is load-bearing: the bulk alone does not determine the index, and a rank-one boundary change crosses a Krein threshold.

---

# Kernel theorem in the desired form

If we define (K_{\sigma,d}^{\mathrm{crit}}) as the **boundary-compressed kernel associated to removing the (y_*)-evaluation channel**, then the requested theorem is exactly true:

[
\boxed{
K_{\sigma,d}^{\mathrm{crit}}(y,z)
=================================

## K_{\nu',d}(y,z)

\frac{K_{\nu',d}(y,y_*)K_{\nu',d}(y_*,z)}
{K_{\nu',d}(y_*,y_*)}.
}
]

In diagonal form:

[
\boxed{
K_{\sigma,d}^{\mathrm{crit}}(y,y)
=================================

## K_{\nu',d}(y,y)

\frac{K_{\nu',d}(y,y_*)^2}
{K_{\nu',d}(y_*,y_*)}.
}
]

And because

[
s_d=\frac1{K_{\nu',d}(y_*,y_*)},
]

this is

[
\boxed{
K_{\sigma,d}^{\mathrm{crit}}(y,y)
=================================

## K_{\nu',d}(y,y)

s_d
\left(v(y)^T(H_d^0)^{-1}v_*\right)^2.
}
]

This proves comp70 symbolically for every (d).

---

# Interpretation

This is the classical RKHS identity:

[
\text{kernel after removing one boundary evaluation}
====================================================

## \text{original kernel}

\text{normalized rank-one boundary projector}.
]

Or in the programme’s language:

[
\boxed{
\text{positive RKHS kernel}
---------------------------

# \text{one normalized Γ-boundary projector}

\text{boundary-compressed kernel}.
}
]

The rank-one projector is

[
\frac{K_{\nu',d}(\cdot,y_*)K_{\nu',d}(y_*,\cdot)}
{K_{\nu',d}(y_*,y_*)}.
]

The scalar coefficient is exactly

[
\frac1{K_{\nu',d}(y_*,y_*)}=s_d.
]

Thus the scalar Weyl gap is not an extra empirical object. It is the inverse squared norm of the boundary evaluation vector.

The bridge notes had already isolated this same scalar as the inverse exterior Christoffel function at the coarsest trivial-zero point (y_*=-0.16), with the first trivial zero acting as the active single-point protector.

---

# Passing to the limit

For every finite (d), the identity is exact. To pass to the infinite object, use the projective system of polynomial spaces

[
\mathcal P_0\subset \mathcal P_1\subset\cdots.
]

Write

[
K_d^0:=K_{\nu',d},
\qquad
K_d^{\mathrm{crit}}
===================

## K_d^0

\frac{K_d^0(\cdot,y_*)K_d^0(y_*,\cdot)}
{K_d^0(y_*,y_*)}.
]

Introduce the normalized boundary vector

[
\psi_{*,d}(y)
=============

\frac{K_d^0(y,y_*)}
{\sqrt{K_d^0(y_*,y_*)}}.
]

Then

[
\boxed{
K_d^{\mathrm{crit}}(y,z)
========================

K_d^0(y,z)-\psi_{*,d}(y)\psi_{*,d}(z).
}
]

This is the clean finite-section form.

If the kernels (K_d^0) and normalized boundary vectors (\psi_{*,d}) converge in a chosen topology — pointwise on a domain, locally uniformly, weakly in the de Branges/Krein space, or as distributions — then

[
\boxed{
K^{\mathrm{crit}}(y,z)
======================

## K_{\nu'}(y,z)

\psi_*(y)\psi_*(z).
}
]

Equivalently, when the limiting evaluation norm is finite,

[
\boxed{
K^{\mathrm{crit}}(y,z)
======================

## K_{\nu'}(y,z)

\frac{K_{\nu'}(y,y_*)K_{\nu'}(y_*,z)}
{K_{\nu'}(y_*,y_*)}.
}
]

In the actual exterior hard-edge situation, (K_d^0(y_*,y_*)) grows and

[
s_d=\frac1{K_d^0(y_*,y_*)}\to0^+.
]

So the literal infinite (K_{\nu'}(y_*,y_*)) may be infinite. Then the correct limit is not the naive quotient with finite numbers; it is the **finite-section / normalized-vector limit**

[
K_d^{\mathrm{crit}}=K_d^0-\psi_{*,d}\psi_{*,d}.
]

This is exactly the no-margin boundary mechanism: the boundary projector persists as a normalized rank-one direction, while its scalar inverse norm (s_d) tends to zero.

The corpus’s no-margin warnings are consistent with this: the numerical difficulty is generic to reciprocal-squared hard-edge measures and carries no RH content by itself; the actual RH content is the source-built transfer that keeps the relevant sign positive at every degree.

---

# The apex in kernel language

Under the already-established rank-one (N_1) carrier picture,

[
H_d^0=H_d^-+a_*v_*v_*^T,
\qquad
\kappa_-(H_d^-)=1,
]

the repaired form is positive exactly when the scalar Weyl gap is positive:

[
\boxed{
s_d
===

# a_*+\frac1{v_*^T(H_d^-)^{-1}v_*}

\frac1{K_{\nu',d}(y_*,y_*)}

> 0.
> }
> ]

So, with the (N_1) theorem in place, the apex can be written as:

[
\boxed{
K_{\nu',d}(y_*,y_*)>0
\quad\text{for every }d,
}
]

or equivalently

[
\boxed{
s_d>0
\quad\text{for every }d.
}
]

But this statement must be read with the rank-one carrier hypothesis. Pointwise positivity of the real-axis kernel alone is not sufficient in general; the bridge notes explicitly warn that an off-line defect can live in a polynomial eigenvector direction off the moment curve even when the real-axis kernel remains positive.

Thus the correct apex statement is:

[
\boxed{
\text{given the }N_1\text{ signed carrier, the Γ-boundary repair is on the positive side}
\iff
s_d>0
\iff
K_{\nu',d}(y_*,y_*)>0.
}
]

This is exactly the boundary-Weyl scalar gate.

---

# Final theorem statement

For every (d), let

[
H_d^0=[T_{i+j+1}]*{i,j=0}^d,
\qquad
K*{\nu',d}(y,z)=e_d(y)^T(H_d^0)^{-1}e_d(z),
\qquad
y_*=-0.16.
]

Then the finite Christoffel/Uvarov boundary-removal kernel is

[
\boxed{
K_{\sigma,d}^{\mathrm{crit}}(y,z)
=================================

## K_{\nu',d}(y,z)

\frac{K_{\nu',d}(y,y_*)K_{\nu',d}(y_*,z)}
{K_{\nu',d}(y_*,y_*)}.
}
]

In diagonal comp70 form:

[
\boxed{
K_{\sigma,d}^{\mathrm{crit}}(y,y)
=================================

## K_{\nu',d}(y,y)

s_d
\left(e_d(y)^T(H_d^0)^{-1}v_*\right)^2,
\qquad
s_d=\frac1{K_{\nu',d}(y_*,y_*)}.
}
]

The actual signed-kernel inverse for

[
\sigma=\nu'-a_*\delta_{y_*}
]

is the slight over-subtraction

[
\boxed{
K_{H^-,d}
=========

## K_{\sigma,d}^{\mathrm{crit}}

\frac{s_d^2}{a_*-s_d}
K_{\nu',d}(\cdot,y_*)K_{\nu',d}(y_*,\cdot).
}
]

So the finite theorem says:

[
\boxed{
\text{positive zero-measure RKHS kernel}
----------------------------------------

# \text{normalized boundary projector}

\text{critical boundary kernel,}
}
]

and the unrepaired signed object is obtained by an infinitesimal further subtraction, giving exactly one negative square.

That is the kernel-theoretic form of the rank-one boundary-Weyl bridge. The remaining open theorem is still source-built positivity of (s_d) for every (d), not the algebra above. The bridge theorem file states the minimal source-aware target as deriving (Q_0[p]\ge0) from completion, explicit formula, and canonical boundary extension; for the actual folded reciprocal divisor, that all-order positivity forces (y_\rho\in\mathbb R_{>0}), hence RH.
