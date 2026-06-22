Below is the lemma package in “paper math” form. I am writing it as a **conditional/conjectural lemma** with the formal pieces separated from the genuinely open analytic step. The formal algebra is solid; the open part is the de Branges/Krein finite-part construction that makes the singular test function admissible.

---

# Lemma: seam finite-part equals the Hankel tail

## 0. Standing notation

Let

[
\Xi(w)=\xi!\left(\frac12+w\right)
]

be the seam-recentered completed zeta function. It is even. For a zero (w_\rho=\rho-\frac12), define the reciprocal seam-squared coordinate

[
y_\rho=-w_\rho^{-2}.
]

Then on RH,

[
w_\rho=i\gamma
\quad\Rightarrow\quad
y_\rho=\gamma^{-2}>0.
]

Define the shifted reciprocal moments

[
T_k=\sum_\rho m_\rho y_\rho^k,\qquad k\ge1,
]

and the shifted square form

[
Q_0[p]
======

# \sum_{i,j=0}^d c_i c_jT_{i+j+1}

\sum_\rho m_\rho, y_\rho,p(y_\rho)^2
]

for a real polynomial

[
p(y)=\sum_{i=0}^d c_i y^i.
]

This is the corpus’s source-aware reciprocal bridge form: all-order (Q_0[p]\ge0) forces the folded reciprocal zero divisor onto (\mathbb R_{>0}), hence RH. The open content is not this equivalence, but deriving the positivity from completion, explicit formula, and the canonical boundary without zero-feeding.

For ζ, write the Γ-trivial images as

[
y_j=-(2j+\tfrac12)^{-2},
\qquad
a_j=(2j+\tfrac12)^{-2},
\qquad j\ge1.
]

The first active trivial-zero boundary atom is

[
y_* = y_1=-(5/2)^{-2}=-0.16,
\qquad
a_* = a_1=(5/2)^{-2}=0.16.
]

Let

[
v_*=(1,y_*,y_*^2,\dots,y_*^d)^T.
]

---

# 1. Singular Weil pullback

For each polynomial (p), define the meromorphic even test function

[
h_p(w)
======

-w^{-2},p(-w^{-2})^2.
]

Equivalently, with (y=-w^{-2}),

[
h_p(w)=y,p(y)^2.
]

At a zero (w=w_\rho),

[
h_p(w_\rho)=y_\rho p(y_\rho)^2.
]

Thus, formally,

[
\sum_\rho m_\rho h_p(w_\rho)=Q_0[p].
]

But (h_p) has a pole at (w=0), the seam centre (s=\frac12). If (\deg p=d), then (h_p) has pole order (4d+2). Hence (h_p) is not an admissible classical Weil test function. This is exactly the obstruction observed in the Weil-pullback computation: the pullback works on the zero side but becomes singular at the seam centre. The corpus already states that a source-built square identity must use the completed weld and cannot smuggle in ordinary Weil positivity, because ordinary Weil positivity is itself RH-equivalent.

So introduce a de Branges/Krein finite-part extension of the Weil distribution:

[
Q_W^{\mathrm{fp}}[h_p]
:=
\operatorname{FP}_{w=0} Q_W[h_p].
]

This is the paper-math object to construct.

---

# 2. Local seam-residue identity

The following identity is formal and should be the first lemma in the paper.

## Lemma 1 — seam coefficient extraction

Let

[
M_\Xi(w)
========

\frac{1}{2w}\frac{\Xi'(w)}{\Xi(w)}.
]

Then near (w=0),

[
M_\Xi(w)
========

\sum_{k\ge0}(-1)^kT_{k+1}w^{2k}.
]

Therefore, for every real polynomial (p),

[
\boxed{
Q_0[p]
======

-\operatorname{Res}*{w=0}
\left[
h_p(w),wM*\Xi(w),dw
\right]
}
]

or equivalently

[
\boxed{
Q_0[p]
======

-\frac12
\operatorname{Res}_{w=0}
\left[
h_p(w)\frac{\Xi'(w)}{\Xi(w)},dw
\right].
}
]

### Proof

Write

[
p(y)^2=\sum_{n=0}^{2d} b_n y^n,
\qquad
b_n=\sum_{i+j=n}c_i c_j.
]

Then

[
h_p(w)
======

# y,p(y)^2\big|_{y=-w^{-2}}

# \sum_{n=0}^{2d} b_n(-w^{-2})^{n+1}

\sum_{n=0}^{2d} b_n(-1)^{n+1}w^{-2n-2}.
]

Also

[
wM_\Xi(w)
=========

\sum_{k\ge0}(-1)^kT_{k+1}w^{2k+1}.
]

The residue occurs only when (k=n). Hence

[
\operatorname{Res}*{w=0}h_p(w)wM*\Xi(w)dw
=========================================

\sum_{n=0}^{2d}
b_n(-1)^{n+1}(-1)^nT_{n+1}
==========================

-\sum_{n=0}^{2d}b_nT_{n+1}.
]

But

[
\sum_{n=0}^{2d}b_nT_{n+1}
=========================

# \sum_{i,j=0}^d c_ic_jT_{i+j+1}

Q_0[p].
]

So

[
Q_0[p]
======

-\operatorname{Res}*{w=0}h_p(w)wM*\Xi(w)dw.
]

This proves the identity.

---

# 3. Source split

Write the completed logarithmic derivative as

[
\frac{\Xi'}{\Xi}(w)=A(w)+P(w),
]

where (A) is the archimedean/pole part and (P) is the prime/Euler part after completion.

Define

[
Q_A[p]
======

-\frac12\operatorname{Res}_{w=0}
\left[
h_p(w)A(w),dw
\right],
]

[
Q_P[p]
======

-\frac12\operatorname{FP}_{w=0}
\left[
h_p(w)P(w),dw
\right].
]

Then

[
Q_0[p]=Q_A[p]+Q_P[p].
]

The archimedean part has the closed form

[
\boxed{
Q_A[p]
======

-4p(-4)^2
+
\sum_{j\ge1}
(2j+\tfrac12)^{-2}
p!\left(-(2j+\tfrac12)^{-2}\right)^2.
}
]

Equivalently,

[
Q_A[p]
======

-4p(-4)^2
+
\sum_{j\ge1}a_jp(y_j)^2.
]

This is the already-closed archimedean rank-one theorem: the pole gives the single negative direction (p\mapsto p(-4)), while the trivial-zero divisor gives a positive square-sum budget. The corpus records this as an all-(d) theorem with inertia ((d,1)) for the archimedean Hankel form.

The prime side contains the opposite pole repair plus the genuine residual. Define the pole-free prime residual (R^P) by

[
Q_0[p]
======

\sum_{j\ge1}a_jp(y_j)^2
+
R^P[p].
]

Thus

[
\boxed{
R^P[p]
======

## Q_0[p]

\sum_{j\ge1}a_jp(y_j)^2.
}
]

This is the corpus’s partial square identity:

[
Q_0[p]
======

\int |p|^2,d\mu_{\mathrm{triv}}
+
R^P[p],
]

where

[
\mu_{\mathrm{triv}}
===================

\sum_{j\ge1}a_j\delta_{y_j}.
]

The positive trivial-zero measure is source-built; (R^P) carries the remaining RH content.

---

# 4. Extract the first Γ-boundary atom

Split the trivial-zero measure into the first atom and the rest:

[
\mu_{\mathrm{triv}}
===================

a_*\delta_{y_*}
+
\mu_{\ge2},
]

where

[
\mu_{\ge2}
==========

\sum_{j\ge2}a_j\delta_{y_j}.
]

Then

[
Q_0[p]
======

a_*p(y_*)^2
+
\int |p|^2,d\mu_{\ge2}
+
R^P[p].
]

Define the bulk form

[
\boxed{
H^-[p]
:=
Q_0[p]-a_*p(y_*)^2.
}
]

Then

[
\boxed{
H^-[p]
======

\int |p|^2,d\mu_{\ge2}
+
R^P[p].
}
]

In matrix form,

[
\boxed{
H_d^0
=====

H_d^-
+
a_*v_*v_*^T.
}
]

This is the rank-one Γ-boundary split.

The important point is that the boundary atom

[
a_*v_*v_*^T
===========

0.16,v_{-0.16}v_{-0.16}^T
]

is not fitted from zeros. It is exactly the (j=1) trivial-zero term of the Γ-factor square-sum. So this part is source-built from the completion.

---

# 5. The finite-part lemma

Now we can state the desired paper lemma.

## Lemma 2 — seam finite-part/Hankel-tail identification

Let

[
h_p(w)=-w^{-2}p(-w^{-2})^2.
]

There exists a canonical de Branges/Krein finite-part extension of the completed Weil distribution at the seam centre (w=0), denoted

[
\operatorname{FP}_{w=0}Q_W[h_p],
]

such that, after the first Γ-trivial-zero atom is moved to the boundary side,

[
\boxed{
\operatorname{FP}_{w=0}^{\mathrm{bulk}}Q_W[h_p]
===============================================

Q_0[p]-a_*p(y_*)^2.
}
]

Equivalently,

[
\boxed{
\operatorname{FP}_{w=0}^{\mathrm{bulk}}Q_W[h_p]
===============================================

H^-[p].
}
]

Using the source split,

[
\boxed{
\operatorname{FP}_{w=0}^{\mathrm{bulk}}Q_W[h_p]
===============================================

\int |p|^2,d\mu_{\ge2}
+
R^P[p].
}
]

Now write the prime residual in the protector-point coordinate

[
x=y-y_*
=======

y+0.16.
]

Let (J) be the near-Jacobi regular part of (R^P) in the protector basis, and let

[
E:=R^P-J.
]

Then the seam finite-part distribution is the signed moment functional (\mu_E) defined by

[
\boxed{
E_{ij}
======

\mu_E[x^{i+j}].
}
]

Equivalently, for every polynomial (p),

[
\boxed{
E[p]
====

\mu_E[p(x)^2].
}
]

Thus

[
\boxed{
\operatorname{FP}_{w=0}^{\mathrm{bulk}}Q_W[h_p]
===============================================

\int |p|^2,d\mu_{\ge2}
+
J[p]
+
\mu_E[p^2].
}
]

This is the desired identification:

[
\boxed{
\mu_E
=====

\text{finite-part seam-centre boundary distribution.}
}
]

---

# 6. Why (E) must be Hankel

The Hankel structure is not an accident. It is forced by the singular pullback.

Write

[
p(y)^2
======

\sum_{n=0}^{2d} b_n y^n,
\qquad
b_n=\sum_{i+j=n}c_ic_j.
]

Then

[
h_p(w)
======

\sum_{n=0}^{2d} b_n(-1)^{n+1}w^{-2n-2}.
]

A finite-part distribution supported at the seam centre can only pair with the Laurent coefficients indexed by (n). Therefore its contribution has the form

[
\sum_{n=0}^{2d}b_ne_n
=====================

\sum_{i,j=0}^dc_ic_je_{i+j}.
]

Hence its matrix entries depend only on (i+j):

[
E_{ij}=e_{i+j}.
]

So the seam-centre finite part is necessarily a Hankel functional.

In generating-function language, if

[
M_E(w)
======

\sum_{n\ge0}(-1)^ne_nw^{2n},
]

then

[
\boxed{
\mu_E[p^2]
==========

-\operatorname{Res}_{w=0}
\left[
h_p(w),wM_E(w),dw
\right].
}
]

Equivalently,

[
\boxed{
e_n
===

(-1)^n[w^{2n}]M_E(w).
}
]

This gives a concrete source target: identify (M_E(w)) as the seam finite-part component of the regularized completed logarithmic connection.

---

# 7. Schur/Weyl reduction

Assume the one-defect bulk theorem:

[
\operatorname{inertia}(H_d^-)=(d,1).
]

Define

[
m_d
===

v_*^T(H_d^-)^{-1}v_*.
]

Then the rank-one update

[
H_d^0=H_d^-+a_*v_*v_*^T
]

is positive semidefinite if and only if the scalar Weyl gap

[
\boxed{
s_d
===

a_*+\frac1{m_d}
}
]

is positive.

Indeed, the rank-one Schur/Krein crossing threshold is

[
a_c(d)=-\frac1{m_d},
]

so

[
H_d^0\succeq0
\quad\Longleftrightarrow\quad
a_*>a_c(d)
\quad\Longleftrightarrow\quad
a_*+\frac1{m_d}>0.
]

By the Sherman–Morrison identity,

[
v_*^T(H_d^0)^{-1}v_*
====================

\frac{m_d}{1+a_*m_d}.
]

Therefore

[
\frac1{v_*^T(H_d^0)^{-1}v_*}
============================

# a_*+\frac1{m_d}

s_d.
]

But

[
v_*^T(H_d^0)^{-1}v_*
====================

K_{\nu'}(y_*,y_*),
]

the exterior Christoffel kernel of the shifted reciprocal zero measure (\nu') at the Γ-selected point (y_*). Hence

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

0.16\cdot \operatorname{margin}_d.
}
]

This is exactly the boundary-Weyl form anticipated by the corpus: the bulk alone does not determine the index; a rank-one boundary change crosses a Krein threshold, so the source-built theorem must include the canonical Γ/pole/FE boundary extension.

---

# 8. Final lemma package

Putting the pieces together:

## Seam finite-part boundary lemma

For every real polynomial (p), define

[
h_p(w)=-w^{-2}p(-w^{-2})^2.
]

Then the desired de Branges/Krein regularized Weil pullback should satisfy

[
\boxed{
\operatorname{FP}_{w=0}^{\mathrm{bulk}}Q_W[h_p]
===============================================

Q_0[p]-a_*p(y_*)^2.
}
]

Equivalently,

[
\boxed{
\operatorname{FP}_{w=0}^{\mathrm{bulk}}Q_W[h_p]
===============================================

\int |p|^2,d\mu_{\ge2}
+
J[p]
+
\mu_E[p^2],
}
]

where

[
\boxed{
\mu_E[x^{i+j}]=E_{ij},
\qquad
x=y-y_*,
}
]

and (E) is the Hankel tail in the protector-point decomposition

[
R^P=J+E.
]

The scalar boundary theorem then reads:

[
\boxed{
H_d^0\succeq0
\quad\Longleftrightarrow\quad
s_d=a_*+\frac1{v_*^T(H_d^-)^{-1}v_*}>0.
}
]

Equivalently,

[
\boxed{
s_d
===

\frac1{K_{\nu'}(y_*,y_*)}.
}
]

Thus the proof target becomes:

[
\boxed{
\operatorname{FP}_{w=0}^{\mathrm{bulk}}Q_W[h_p]
\text{ source-builds }H_d^-,
\quad
\mu_E
\text{ is the seam finite-part Hankel functional,}
\quad
s_d>0\ \forall d.
}
]

---

# 9. What remains genuinely open

The formal residue identity

[
Q_0[p]
======

-\frac12
\operatorname{Res}_{w=0}
h_p(w)\frac{\Xi'}{\Xi}(w),dw
]

is algebraic coefficient extraction.

The Γ-boundary atom

[
a_*p(y_*)^2
===========

0.16,p(-0.16)^2
]

is source-built from the first trivial-zero term of the archimedean square-sum.

The Sherman–Morrison/Weyl scalar identity

[
s_d
===

# a_*+\frac1{m_d}

\frac1{K_{\nu'}(y_*,y_*)}
]

is algebraic.

The open analytic step is:

[
\boxed{
\text{construct the de Branges/Krein finite-part domain at }w=0
\text{ and prove that its boundary distribution is exactly }\mu_E.
}
]

That is the paper theorem still to prove. It is not a numerical lemma, and it is not a restatement of RH by itself. It is the missing source-built identity that would turn the observed Hankel tail into a canonical seam-centre boundary functional. The guardrail remains the one stated in the corpus: naming a positivity equivalent to RH is not progress unless the object is source-built, completed, faithful, fake-family separating, and compatible with zero margin.
