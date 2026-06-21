Yes. With the standard completed-(\xi) normalization, the archimedean rank-one theorem is true in a clean explicit form.

The key point is:

[
\boxed{
H_d^A=R_d^A-2u_du_d^{\mathsf T},
\qquad
R_d^A\succeq0,
\qquad
u_d=(1,-4,(-4)^2,\dots,(-4)^d)^{\mathsf T}.
}
]

The coefficient (2) depends on the normalization of (S_k^A). With

[
A(s)=\frac1s+\frac1{s-1}-\frac12\log\pi+\frac12\psi(s/2),
]

the coefficient is exactly (2). The vector (u_d) is evaluation at the reciprocal image of the (s=1) pole:

[
s=1
\quad\Longleftrightarrow\quad
w=s-\frac12=\frac12
\quad\Longleftrightarrow\quad
y=-w^{-2}=-4.
]

So

[
p(-4)=\sum_{i=0}^d c_i(-4)^i=\langle c,u_d\rangle.
]

This proves that the unique negative archimedean direction is the cancelled (s=1) pole direction, at the level of the (Q_0) form. The seam-cancellation note already identifies the (A+P) weld, superzeta values (S_k), phase defect, and entireness as the same (s=1) pole-cancellation mechanism; the formula below is the quadratic-form version of that statement.

---

## The theorem

Let

[
\Xi(w)=\xi\left(\frac12+w\right),
]

and split

[
\frac{\Xi'}{\Xi}(w)
===================

A\left(\frac12+w\right)+P\left(\frac12+w\right),
]

with

[
A(s)=\frac1s+\frac1{s-1}-\frac12\log\pi+\frac12\psi(s/2).
]

Define the archimedean reciprocal seam coefficients by

[
S_k^A
=====

-\frac12[w^{2k-1}],A\left(\frac12+w\right),
]

and

[
T_k^A=(-1)^kS_k^A.
]

Then set

[
H_d^A=\left[T_{i+j+1}^A\right]_{i,j=0}^d.
]

Now define

[
u_d=\big((-4)^0,(-4)^1,\dots,(-4)^d\big)^{\mathsf T}.
]

For (n\ge1), define

[
a_n=\frac{4}{(4n+1)^2},
]

and

[
v_n=\big((-a_n)^0,(-a_n)^1,\dots,(-a_n)^d\big)^{\mathsf T}.
]

Then

[
\boxed{
H_d^A
=====

## \frac12\sum_{n=1}^{\infty}a_n,v_nv_n^{\mathsf T}

2u_du_d^{\mathsf T}.
}
]

Therefore

[
\boxed{
H_d^A=R_d^A-2u_du_d^{\mathsf T},
\qquad
R_d^A:=\frac12\sum_{n=1}^{\infty}a_n,v_nv_n^{\mathsf T}\succeq0.
}
]

Moreover (R_d^A) is positive definite for every finite (d), and (H_d^A) has inertia

[
\boxed{
(d,1),
}
]

meaning (d) positive eigenvalues and one negative eigenvalue.

---

## Proof

Start from

[
A(s)=\frac1s+\frac1{s-1}-\frac12\log\pi+\frac12\psi(s/2).
]

The constant (-\frac12\log\pi) contributes no positive (w)-coefficients, so it is irrelevant for (S_k^A).

Put

[
s=\frac12+w.
]

The rational pole part is

[
\frac1{\frac12+w}+\frac1{-\frac12+w}.
]

Expanding around (w=0),

[
\frac1{\frac12+w}
=================

2\sum_{n\ge0}(-2w)^n,
]

and

[
\frac1{-\frac12+w}
==================

-2\sum_{n\ge0}(2w)^n.
]

For odd (n=2k-1), the coefficient is

[
-2^{2k+1}.
]

Therefore the rational part contributes

[
-\frac12(-2^{2k+1})=2^{2k}
]

to (S_k^A).

Now consider the digamma term:

[
\frac12\psi\left(\frac14+\frac w2\right).
]

The coefficient of (w^{2k-1}) is

[
\frac12\cdot
\frac{\psi^{(2k-1)}(1/4)}{2^{2k-1}(2k-1)!}
==========================================

\frac{\psi^{(2k-1)}(1/4)}
{2^{2k}(2k-1)!}.
]

Thus its contribution to (S_k^A) is

[
-\frac12
\cdot
\frac{\psi^{(2k-1)}(1/4)}
{2^{2k}(2k-1)!}
===============

-\frac{\psi^{(2k-1)}(1/4)}
{2^{2k+1}(2k-1)!}.
]

Hence

[
\boxed{
S_k^A
=====

## 2^{2k}

\frac{\psi^{(2k-1)}(1/4)}
{2^{2k+1}(2k-1)!}.
}
]

Using the polygamma identity

[
\psi^{(m)}(x)
=============

(-1)^{m+1}m!\sum_{n=0}^{\infty}\frac1{(n+x)^{m+1}},
]

and (m=2k-1), we get

[
\frac{\psi^{(2k-1)}(1/4)}{(2k-1)!}
==================================

\sum_{n=0}^{\infty}
\frac1{(n+1/4)^{2k}}.
]

Therefore

[
S_k^A
=====

## 2^{2k}

\frac1{2^{2k+1}}
\sum_{n=0}^{\infty}
\frac1{(n+1/4)^{2k}}.
]

Rewrite

[
\frac{1}{2^{2k+1}(n+1/4)^{2k}}
==============================

\frac12
\left(\frac{1}{2(n+1/4)}\right)^{2k}.
]

Define

[
a_n=\left(\frac{1}{2(n+1/4)}\right)^2
=====================================

\frac{4}{(4n+1)^2}.
]

Then

[
S_k^A
=====

4^k-\frac12\sum_{n=0}^{\infty}a_n^k.
]

Now (a_0=4), so

[
S_k^A
=====

## 4^k-\frac12,4^k

# \frac12\sum_{n=1}^{\infty}a_n^k

## \frac12,4^k

\frac12\sum_{n=1}^{\infty}a_n^k.
]

Multiplying by ((-1)^k),

[
T_k^A=(-1)^kS_k^A
=================

## \frac12(-4)^k

\frac12\sum_{n=1}^{\infty}(-a_n)^k.
]

Now put (m=i+j+1). Then

[
H_d^A[i,j]=T_{i+j+1}^A
======================

## \frac12(-4)^{i+j+1}

\frac12\sum_{n=1}^{\infty}(-a_n)^{i+j+1}.
]

The first term is

[
\frac12(-4)^{i+j+1}
===================

# -2(-4)^i(-4)^j

-2u_i u_j.
]

For the second term,

[
-\frac12(-a_n)^{i+j+1}
======================

\frac12 a_n(-a_n)^i(-a_n)^j.
]

So

[
H_d^A[i,j]
==========

-2u_i u_j
+
\frac12\sum_{n=1}^{\infty}
a_n(-a_n)^i(-a_n)^j.
]

In matrix form,

[
\boxed{
H_d^A
=====

-2u_du_d^{\mathsf T}
+
\frac12\sum_{n=1}^{\infty}a_n v_nv_n^{\mathsf T}.
}
]

Thus

[
R_d^A:=\frac12\sum_{n=1}^{\infty}a_n v_nv_n^{\mathsf T}
]

is positive semidefinite, being a sum of positive rank-one matrices.

In fact it is positive definite. If (c\neq0), let

[
p_c(y)=\sum_{i=0}^dc_i y^i.
]

Then

[
c^{\mathsf T}R_d^A c
====================

\frac12\sum_{n=1}^{\infty}a_n,p_c(-a_n)^2.
]

The points (-a_n) are infinitely many distinct real numbers. A nonzero polynomial of degree (d) cannot vanish on all of them. Hence

[
c^{\mathsf T}R_d^A c>0
]

for all (c\neq0). So

[
R_d^A\succ0.
]

Finally, since (H_d^A=R_d^A-2u_du_d^{\mathsf T}) is a positive definite matrix plus one negative rank-one perturbation, it has at most one negative eigenvalue. It has at least one negative direction because the pole term dominates in the (u_d) direction. Indeed

[
u_d^{\mathsf T}H_d^A u_d
========================

## u_d^{\mathsf T}R_d^A u_d

2(u_d^{\mathsf T}u_d)^2.
]

For (n\ge1),

[
4a_n=\frac{16}{(4n+1)^2}\le \frac{16}{25}<1,
]

so

[
|v_n^{\mathsf T}u_d|
====================

\left|\sum_{i=0}^d(4a_n)^i\right|
\le
\frac1{1-4a_n}.
]

Therefore

[
u_d^{\mathsf T}R_d^A u_d
\le
\frac12\sum_{n=1}^{\infty}
\frac{a_n}{(1-4a_n)^2}
<1.
]

Meanwhile

[
2(u_d^{\mathsf T}u_d)^2\ge2.
]

Thus

[
u_d^{\mathsf T}H_d^A u_d<0.
]

So (H_d^A) has at least one negative eigenvalue. Since it has at most one, it has exactly one. Since (R_d^A\succ0), the rank-one perturbation has no additional zero branch once a negative direction exists. Therefore

[
\boxed{
\operatorname{inertia}(H_d^A)=(d,1).
}
]

This proves the archimedean rank-one theorem.

---

## What this means for the programme

This theorem makes the archimedean half explicit:

[
\boxed{
H_d^A
=====

## \underbrace{\frac12\sum_{n=1}^{\infty}a_n v_nv_n^{\mathsf T}}_{\text{positive tail}}

\underbrace{2u_du_d^{\mathsf T}}_{\text{single negative }s=1\text{ pole direction}}.
}
]

So Part A of the bridge is now structurally clear:

[
\boxed{
\text{the archimedean form has one and only one negative direction, the cancelled (s=1) pole at (y=-4).}
}
]

The remaining proof problem is not this rank-one geometry. It is the residual positivity after the prime side cancels the pole direction. In the language of the current programme:

[
\boxed{
\text{rank-one pole cancellation is closed-form; the RH wall is residual (Q_0)-positivity.}
}
]

That matches the current one-wall synthesis: the RH content is not the weld cancellation itself but all-order positivity of the reciprocal zero-divisor (T_k).
