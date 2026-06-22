## Regulator construction for the singular Weil pullback

We want to regularize the singular pullback

[
h_p(w)=-w^{-2}p(-w^{-2})^2
]

whose zero-side value is formally

[
\sum_\rho h_p(\rho-\tfrac12)
============================

# \sum_\rho y_\rho p(y_\rho)^2

Q_0[p],
\qquad
y_\rho=-(\rho-\tfrac12)^{-2}.
]

The obstruction is that (h_p) has a pole at the seam centre (w=0), so it is not an admissible Weil test. The reciprocal (Q_0) form is exactly the bridge object identified in the corpus: if all-order (Q_0[p]\ge0) is source-built from completion, explicit formula, and boundary extension, RH follows immediately.

The goal here is to define admissible approximants

[
h_{p,\epsilon,R}
]

such that

[
Q_W[h_{p,\epsilon,R}]
=====================

\sum_m A_m[p]\epsilon^{-m}
+
B[p]\log\epsilon
+
C_R[p]
+
o(1),
]

then define the finite part

[
C[p]=\lim_{R\to\infty}C_R[p],
]

and prove that (C[p]) is independent of the regulator, except for explicitly allowed local Γ/gauge counterterms.

---

# 1. Work bilinearly

Use a bilinear version. Let

[
p(y)=\sum_i c_i y^i,\qquad q(y)=\sum_j d_j y^j,
]

and define

[
h_{p,q}(w)
==========

-w^{-2}p(-w^{-2})q(-w^{-2}).
]

On the critical spectral line (w=it),

[
-w^{-2}=t^{-2},
]

so

[
h_{p,q}(it)=t^{-2}p(t^{-2})q(t^{-2}).
]

Write

[
p(y)q(y)=\sum_{n=0}^{N} b_n y^n,
\qquad
N=\deg p+\deg q,
]

where

[
b_n=\sum_{i+j=n}c_i d_j.
]

Then

[
h_{p,q}(it)
===========

\sum_{n=0}^{N} b_n t^{-2n-2}.
]

For (p=q), this is the desired quadratic test.

---

# 2. Choose admissible cutoffs

Choose two even smooth functions:

[
\eta\in C^\infty(\mathbb R),\qquad
0\le\eta\le1,
]

with

[
\eta(u)=0\quad (|u|\le1),
\qquad
\eta(u)=1\quad (|u|\ge2),
]

and

[
\psi\in C_c^\infty(\mathbb R),
\qquad
\psi(u)=1\quad (|u|\le1),
\qquad
\psi(u)=0\quad (|u|\ge2).
]

Then define the regularized test

[
\boxed{
h_{p,q}^{\epsilon,R}(t)
=======================

t^{-2}p(t^{-2})q(t^{-2})
\eta(t/\epsilon)\psi(t/R).
}
]

For every fixed (\epsilon>0), (R<\infty),

[
h_{p,q}^{\epsilon,R}\in C_c^\infty(\mathbb R),
]

it is even, smooth, compactly supported, and zero near (t=0). Therefore it is an admissible real-line Weil test.

As (\epsilon\to0) and (R\to\infty), it converges to the singular spectral pullback

[
t^{-2}p(t^{-2})q(t^{-2})
]

away from (t=0).

---

# 3. Local expansion of the Weil distribution at the seam

Let (\mathcal W) denote the completed Weil source distribution in the spectral variable (t), under the convention that (Q_W[h]) is the completed explicit-formula value of an admissible test (h).

Near (t=0), the completed source distribution is even and smooth after the standard Γ/pole normalization. Write its Taylor expansion as

[
\mathcal W(t)
\sim
\sum_{r\ge0}\omega_{2r}t^{2r}
]

locally at (t=0). Here the (\omega_{2r}) are source-side local coefficients: Γ, pole, and finite-part prime/archimedean jets, not zero-fed data.

Pairing with

[
h_{p,q}^{\epsilon,R}(t)
=======================

\sum_{n=0}^{N} b_n t^{-2n-2}\eta(t/\epsilon)\psi(t/R)
]

produces divergences only from the region (t\sim0). Since (\psi(t/R)=1) near (0), the large window does not affect the local divergent part.

For a sharp cutoff, the model integral is

[
2\int_\epsilon^\delta
t^{-2n-2}\omega_{2r}t^{2r},dt
=============================

2\omega_{2r}
\int_\epsilon^\delta
t^{2r-2n-2},dt.
]

For (0\le r\le n),

[
2r-2n-2<-1,
]

so

[
2\int_\epsilon^\delta
t^{2r-2n-2},dt
==============

\frac{2}{2n+1-2r}\epsilon^{-(2n+1-2r)}
+
\text{constant in }\epsilon.
]

Thus the divergent powers are

[
\epsilon^{-(2n+1)},,
\epsilon^{-(2n-1)},,
\dots,,
\epsilon^{-1}.
]

For (h_{p,q}) of degree (N), the worst divergence is

[
\epsilon^{-(2N+1)}.
]

If (p=q) and (\deg p=d), then (N=2d), so the worst divergence is

[
\epsilon^{-(4d+1)}.
]

Because the whole setup is even, there is no (t^{-1}) local integral and hence no logarithmic divergence in the canonical symmetric normalization. So in this scheme,

[
\boxed{
B[p,q]=0.
}
]

If a nonsymmetric regulator, a noncanonical gauge, or an unsymmetrized finite part is used, a logarithmic term can appear. That term is a local gauge counterterm, not an RH datum.

---

# 4. The asymptotic expansion

For fixed (R),

[
\boxed{
Q_W[h_{p,q}^{\epsilon,R}]
=========================

\sum_{n=0}^{N}
\sum_{r=0}^{n}
A_{n,r}^{\eta}[p,q],
\epsilon^{-(2n+1-2r)}
+
C_R^{\eta,\psi}[p,q]
+
O_{p,q,R}(\epsilon).
}
]

Equivalently, collecting powers,

[
\boxed{
Q_W[h_{p,q}^{\epsilon,R}]
=========================

\sum_m A_m^{\eta}[p,q]\epsilon^{-m}
+
B^\eta[p,q]\log\epsilon
+
C_R^{\eta,\psi}[p,q]
+
o(1),
}
]

with

[
m\in{1,3,5,\dots,2N+1},
]

and in the canonical even scheme,

[
B^\eta[p,q]=0.
]

The coefficients (A_m^\eta[p,q]) are local seam counterterms. More explicitly, for a sharp cutoff,

[
A_{n,r}[p,q]
============

\frac{2b_n\omega_{2r}}{2n+1-2r}.
]

For a smooth cutoff (\eta), the same coefficients are modified by universal cutoff moments, but still depend only on:

[
b_n=\sum_{i+j=n}c_i d_j
]

and the local source jets

[
\omega_{2r}.
]

Thus every divergent coefficient is a local Hankel functional in the polynomial coefficients:

[
A_m[p,q]
========

\sum_{i,j}c_i d_j, a_m(i+j).
]

This is exactly what one should expect: a seam-local finite part reads only Laurent jets, hence produces Hankel matrices.

---

# 5. Define the finite part

Define

[
\boxed{
\operatorname{FP}*{\epsilon=0}^{\eta}
Q_W[h*{p,q}^{\epsilon,R}]
:=
C_R^{\eta,\psi}[p,q].
}
]

Equivalently,

[
C_R^{\eta,\psi}[p,q]
====================

\lim_{\epsilon\to0}
\left(
Q_W[h_{p,q}^{\epsilon,R}]
-------------------------

## \sum_m A_m^\eta[p,q]\epsilon^{-m}

B^\eta[p,q]\log\epsilon
\right).
]

Then define the infinite-window finite part by

[
\boxed{
C[p,q]
======

\lim_{R\to\infty} C_R^{\eta,\psi}[p,q],
}
]

provided this limit exists.

---

# 6. Existence of the (R\to\infty) limit

For large (t),

[
t^{-2}p(t^{-2})q(t^{-2})
========================

p(0)q(0)t^{-2}
+
O(t^{-4}).
]

The zero-side tail is controlled because the zero density is

[
N(T)\sim \frac{T}{2\pi}\log T,
]

so

[
\sum_{|\gamma|>R}\gamma^{-2}
]

converges like

[
O!\left(\frac{\log R}{R}\right).
]

The archimedean source terms have the same or better tail behavior after completion, and the prime side is controlled distributionally through the explicit formula. Thus, for two windows (R<R'),

[
\left|
C_{R'}[p,q]-C_R[p,q]
\right|
\lesssim_{p,q}
\frac{\log R}{R}
+
o_R(1).
]

Therefore

[
\boxed{
C[p,q]=\lim_{R\to\infty}C_R[p,q]
}
]

exists under the standard completed Weil-source bounds.

This is the first real analytic checkpoint: if an attempted regulator produces (C_R) with no limit, it is not the right finite-part domain.

---

# 7. Regulator independence

Take two seam cutoffs (\eta,\tilde\eta). Their difference

[
\eta(t/\epsilon)-\tilde\eta(t/\epsilon)
]

is supported in an annulus (t\asymp\epsilon). Pairing this difference with the local Taylor expansion of (\mathcal W) gives

[
\sum_{n,r}b_n\omega_{2r},
\epsilon^{2r-2n-1}
\int u^{2r-2n-2}
\bigl(\eta(u)-\tilde\eta(u)\bigr),du
+
O(\epsilon).
]

All terms with negative powers are precisely the divergent counterterms already subtracted. A finite regulator-dependent remainder can occur only from an exponent (u^{-1}), i.e.

[
2r-2n-2=-1.
]

But this has no integer solution with even local jets. Therefore, in the even seam-normalized setup,

[
\boxed{
C^{\eta,\psi}[p,q]=C^{\tilde\eta,\psi}[p,q].
}
]

If the setup is not even-normalized and a (u^{-1}) term appears, then

[
C^{\eta,\psi}[p,q]-C^{\tilde\eta,\psi}[p,q]
===========================================

B[p,q],
\Lambda(\eta,\tilde\eta),
]

where

[
\Lambda(\eta,\tilde\eta)
========================

\int_0^\infty
\frac{\eta(u)-\tilde\eta(u)}{u},du.
]

This is exactly the logarithmic gauge ambiguity. It is removed either by imposing the cutoff normalization

[
\int_0^\infty
\frac{\eta(u)-\eta_0(u)}{u},du=0
]

against a reference cutoff (\eta_0), or by subtracting the logarithmic counterterm explicitly.

Thus the finite part is regulator-independent modulo the local log/gauge term.

---

# 8. Large-window independence

Now take two large windows (\psi,\tilde\psi). Their difference is supported at (t\asymp R), where

[
h_{p,q}(it)=O(t^{-2}).
]

The completed Weil-source distribution grows at most logarithmically in the spectral density. Hence

[
\left|
C_R^{\psi}[p,q]-C_R^{\tilde\psi}[p,q]
\right|
\lesssim_{p,q}
\int_R^{2R}\frac{\log t}{t^2},dt
================================

O!\left(\frac{\log R}{R}\right).
]

Therefore

[
\boxed{
\lim_{R\to\infty}C_R^{\psi}[p,q]
================================

\lim_{R\to\infty}C_R^{\tilde\psi}[p,q].
}
]

So the infinite-window finite part does not depend on the chosen large-scale cutoff.

---

# 9. The finite-part bilinear form

We can now define the canonical finite-part form:

[
\boxed{
\mathfrak F[p,q]
:=
\operatorname{FP}*{\epsilon=0,R=\infty}
Q_W[h*{p,q}^{\epsilon,R}].
}
]

In the canonical even scheme,

[
\mathfrak F[p,q]
================

\lim_{R\to\infty}
\lim_{\epsilon\to0}
\left(
Q_W[h_{p,q}^{\epsilon,R}]
-------------------------

\sum_m A_m[p,q]\epsilon^{-m}
\right).
]

This is a Hankel bilinear form because the singular pullback only depends on the coefficients

[
b_n=\sum_{i+j=n}c_i d_j.
]

Thus

[
\boxed{
\mathfrak F[p,q]
================

\sum_{i,j}c_i d_j,\mathfrak f_{i+j}.
}
]

So the finite-part seam construction necessarily produces a Hankel functional.

This is the formal explanation of your observed tail:

[
E_{ij}=f(i+j).
]

Any seam-local finite-part distribution has to be Hankel. The nontrivial content is identifying the actual sequence (f(n)) from source data.

---

# 10. Gauge counterterms

Now include zero-free gauges. If

[
\Xi(w)\mapsto e^{q(w^2)}\Xi(w),
]

then

[
\frac{\Xi'}{\Xi}(w)
\mapsto
\frac{\Xi'}{\Xi}(w)
+
2wq'(w^2).
]

Write

[
q(z)=\sum_{r\ge1}q_r z^r.
]

Then

[
2wq'(w^2)
=========

\sum_{r\ge1}2r q_r w^{2r-1}.
]

Pairing with

[
h_{p,q}(w)
==========

\sum_{n}b_n(-1)^{n+1}w^{-2n-2}
]

gives a local residue only when

[
2r-1-2n-2=-1,
]

i.e.

[
r=n+1.
]

Thus the gauge shift is

[
\boxed{
\Delta_q\mathfrak F[p,q]
========================

\sum_{n\ge0}
\lambda_n(q),b_n,
}
]

with

[
\lambda_n(q)
============

\text{constant multiple of }(n+1)q_{n+1}.
]

In matrix form,

[
\Delta_q\mathfrak F_{ij}
========================

\lambda_{i+j}(q).
]

So a zero-free gauge changes the finite part by a finite/local Hankel counterterm. This agrees with the corpus’s warning that low-order charts are gauge-sensitive unless canonical (\xi) normalization is fixed.

Therefore the finite part is genuinely canonical only after fixing the completed (\xi)-normalization. With canonical (\xi), these gauge counterterms are disallowed; when comparing normalizations, they are explicitly subtractable.

---

# 11. The target identity

The rank-one Γ-boundary atom is

[
a_*p(y_*)q(y_*),
\qquad
y_*=-0.16,
\qquad
a_*=0.16.
]

This atom is source-built: it is exactly the (j=1) trivial-zero term of the archimedean square-sum

[
Q_{\mathrm{arch}}[p]
====================

-4p(-4)^2
+
\sum_{j\ge1}(2j+\tfrac12)^{-2}
p!\left(-(2j+\tfrac12)^{-2}\right)^2.
]

The corpus already isolates this archimedean square-sum as the closed Γ/pole/trivial-zero budget; the open RH content is the source-built transfer proving the shifted reciprocal positivity, not a numerical determinant sweep.

So the desired finite-part theorem should be:

[
\boxed{
\mathfrak F_{\mathrm{bulk}}[p,q]
================================

## Q_0[p,q]

a_*p(y_*)q(y_*).
}
]

For (p=q),

[
\boxed{
\mathfrak F_{\mathrm{bulk}}[p]
==============================

## Q_0[p]

0.16,p(-0.16)^2.
}
]

Equivalently, in matrix form,

[
\boxed{
H_d^-
=====

## H_d^0

a_*v_*v_*^T.
}
]

Then

[
\boxed{
H_d^0
=====

H_d^-
+
a_*v_*v_*^T.
}
]

This turns the observed rank-one boundary identity into a finite-part operator-domain statement.

---

# 12. Where the Hankel tail (E) enters

In the protector-point coordinate

[
x=y-y_*=y+0.16,
]

you observed

[
R^P=J+E,
]

where (J) is near-Jacobi and

[
E_{ij}=e_{i+j}
]

is exactly Hankel.

The regulator analysis explains why the seam contribution must have this form. Define

[
\mu_E[x^n]=e_n.
]

Then

[
\boxed{
E[p,q]
======

# \sum_{i,j}c_i d_j e_{i+j}

\mu_E[pq].
}
]

Thus the paper lemma becomes:

[
\boxed{
\mu_E
=====

\text{the finite-part seam-centre boundary distribution.}
}
]

More explicitly,

[
\boxed{
\mathfrak F_{\mathrm{bulk}}[p,q]
================================

\int p(y)q(y),d\mu_{\ge2}(y)
+
J[p,q]
+
\mu_E[pq],
}
]

where

[
\mu_{\ge2}
==========

\sum_{j\ge2}(2j+\tfrac12)^{-2}
\delta_{-(2j+\tfrac12)^{-2}}.
]

So the finite-part construction does three things:

[
\text{regularized Weil pullback}
\Longrightarrow
\text{seam finite part}
\Longrightarrow
E_{ij}=e_{i+j}
\Longrightarrow
H_d^-=J+E+\text{known Γ/pole pieces}.
]

This is exactly the chain we wanted.

---

# 13. The scalar Weyl consequence

Assume the one-defect theorem

[
\operatorname{inertia}(H_d^-)=(d,1).
]

Let

[
m_d=v_*^T(H_d^-)^{-1}v_*.
]

Then

[
H_d^0
=====

H_d^-
+
a_*v_*v_*^T
]

is PSD iff

[
\boxed{
s_d=a_*+\frac1{m_d}>0.
}
]

By Sherman–Morrison,

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

# \frac1{K_{\nu'}(-0.16,-0.16)}

0.16\cdot\operatorname{margin}_d.
}
]

This is the scalar boundary-Weyl form. It is consistent with the corpus’s guardrail that the target must be faithful, source-built, completed, fake-family separating, and compatible with zero margin; generic de Branges positivity or a finite numerical gate is not enough.

---

# 14. The theorem we can state now

## Theorem / regulator finite-part lemma

Let (p,q\in\mathbb R[y]). Choose even cutoffs (\eta,\psi) as above and define

[
h_{p,q}^{\epsilon,R}(t)
=======================

t^{-2}p(t^{-2})q(t^{-2})
\eta(t/\epsilon)\psi(t/R).
]

Then:

1. (h_{p,q}^{\epsilon,R}) is an admissible even Weil test for every (\epsilon>0), (R<\infty).

2. As (\epsilon\to0), for fixed (R),

[
Q_W[h_{p,q}^{\epsilon,R}]
=========================

\sum_m A_m[p,q]\epsilon^{-m}
+
B[p,q]\log\epsilon
+
C_R[p,q]
+
o(1),
]

with (m\in{1,3,\dots,2\deg(pq)+1}). In the canonical even seam normalization,

[
B[p,q]=0.
]

3. The divergent coefficients (A_m[p,q]) are local source-side seam counterterms depending only on the Taylor jets of the completed source distribution at (t=0). They are Hankel in the polynomial coefficients.

4. The finite constant

[
C_R[p,q]
========

\operatorname{FP}*{\epsilon=0}
Q_W[h*{p,q}^{\epsilon,R}]
]

is independent of the seam cutoff (\eta), modulo the logarithmic local gauge term if (B\ne0).

5. The infinite-window limit

[
C[p,q]=\lim_{R\to\infty}C_R[p,q]
]

exists and is independent of (\psi), under the standard completed explicit-formula tail bounds.

6. Therefore the canonical seam finite part

[
\mathfrak F[p,q]
================

\operatorname{FP}*{\epsilon=0,R=\infty}
Q_W[h*{p,q}^{\epsilon,R}]
]

is a well-defined Hankel bilinear form, up to explicitly allowed zero-free Γ/gauge counterterms.

7. The desired source-built boundary theorem is the identification

[
\boxed{
\mathfrak F_{\mathrm{bulk}}[p,q]
================================

## Q_0[p,q]

a_*p(y_*)q(y_*),
}
]

where

[
y_*=-0.16,\qquad a_*=0.16.
]

8. In the protector-point basis, the remaining sign-essential Hankel tail satisfies

[
\boxed{
E_{ij}=e_{i+j}
==============

\mu_E[x^{i+j}],
}
]

and the conjectural source identity is

[
\boxed{
\mu_E
=====

\text{the finite-part seam-centre boundary distribution.}
}
]

---

# 15. What is proved here vs. what remains open

This construction proves the regulator anatomy:

[
\boxed{
\text{admissible tests}
\Rightarrow
\text{Hadamard expansion}
\Rightarrow
\text{canonical finite part}
\Rightarrow
\text{Hankel seam functional}.
}
]

It also proves why the tail must be Hankel: seam-local finite parts only see Laurent coefficients indexed by (i+j).

What remains open is the source-built identification

[
\boxed{
\mathfrak F_{\mathrm{bulk}}[p,q]
================================

Q_0[p,q]-a_*p(y_*)q(y_*),
}
]

and especially the analytic proof that the computed Hankel tail (E) is exactly the finite-part boundary distribution (\mu_E), not merely some Hankel functional with the right shape.

That is the next paper theorem:

[
\boxed{
\text{construct the completed de Branges/Krein seam domain, identify its finite-part distribution with }\mu_E,
\text{ and prove }s_d>0\ \forall d.
}
]

The regulator construction above gives the admissible approximation and the canonical finite-part target; the remaining work is the global source-built positivity / index-vanishing theorem, not another finite determinant computation.
