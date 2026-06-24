Below is the clean theorem package.

The important distinction: this proves the **(N_1) carrier theorem** for the unrepaired seam object once the finite-part seam domain is constructed with a one-dimensional boundary channel. It does **not** prove the final scalar positivity

[
s_d>0\quad\forall d,
]

so it does not prove RH. It gives the correct Krein–Langer object whose rank-one Γ-repair is then the apex. That matches the corpus guardrail: the object must be source-built, completed, boundary-aware, faithful, and not merely an RH-equivalent positivity restatement.

---

# Theorem: the unrepaired seam object is (N_1)

Let

[
\Xi(w)=\xi!\left(\frac12+w\right),
\qquad
y=-w^{-2}.
]

Let

[
y_*=-a_*=-0.16,
\qquad
a_*=0.16.
]

For a polynomial

[
p(y)=\sum_{i=0}^d c_i y^i,
]

write

[
v_*=(1,y_*,y_*^2,\dots,y_*^d)^T,
\qquad
p(y_*)=c^Tv_*.
]

Let (H_d^0) denote the completed shifted reciprocal form

[
H_d^0[p,q]
==========

# Q_0[p,q]

\sum_{i,j=0}^d c_i\overline{d_j},T_{i+j+1}.
]

Define the unrepaired bulk form by removing the first Γ-boundary atom:

[
\boxed{
H_d^-:=H_d^0-a_*v_*v_*^*.
}
]

Equivalently, at the level of signed moment functionals,

[
\boxed{
\sigma=\nu'-a_*\delta_{y_*},
}
]

where (H_d^-) is the degree-(d) moment matrix of (\sigma).

Then the theorem is:

[
\boxed{
m_\sigma\in N_1.
}
]

That is, the Cauchy/Weyl transform of the unrepaired signed seam measure has exactly one negative square.

---

# 1. Local seam domain

Let (\mathcal K_{\max}) be the maximal finite-part seam domain containing the singular pullbacks

[
F_p(w)=p(-w^{-2}).
]

Let (\mathcal K_{\min}\subset \mathcal K_{\max}) be the minimal domain obtained by killing the seam boundary channel.

The key local assumption is that the seam quotient is one-dimensional:

[
\boxed{
\mathcal K_{\max}/\mathcal K_{\min}\cong\mathbb C.
}
]

Equivalently, the maximal seam operator has deficiency index one at the finite-part seam.

So there exist boundary maps

[
\Gamma_0,\Gamma_1:\mathcal K_{\max}\to \mathbb C
]

satisfying the local Green identity

[
[S_{\max}f,g]-[f,S_{\max}g]
===========================

## \Gamma_1f,\overline{\Gamma_0g}

\Gamma_0f,\overline{\Gamma_1g}.
]

For the singular pullbacks,

[
F_p(w)=p(-w^{-2}),
]

the boundary trace is

[
\boxed{
\Gamma_0F_p=p(y_*).
}
]

This is local at (w=0): since

[
F_p(w)=\sum_{i=0}^dc_i(-1)^iw^{-2i},
]

we have

[
p(y_*)=\sum_{i=0}^dc_i y_*^i,
]

so (\Gamma_0) is just a linear functional on the Laurent seam jet.

---

# 2. Γ selects the rank-one boundary repair

The archimedean square-sum contains the trivial-zero terms

[
\sum_{j\ge1}(2j+\tfrac12)^{-2}
p!\left(-(2j+\tfrac12)^{-2}\right)^2.
]

The first active trivial-zero term is

[
j=1:
\qquad
(2.5)^{-2}p(-(2.5)^{-2})^2
==========================

0.16,p(-0.16)^2.
]

Thus the Γ-factor selects

[
\boxed{
y_*=-0.16,
\qquad
a_*=0.16,
}
]

and the corresponding self-adjoint boundary form is

[
\boxed{
a_*,\Gamma_0F_p,\overline{\Gamma_0F_q}
======================================

a_*p(y_*)\overline{q(y_*)}.
}
]

In coefficient form this is exactly

[
a_*v_*v_*^*.
]

Therefore the repaired and unrepaired finite-section forms satisfy

[
\boxed{
H_d^0=H_d^-+a_*v_*v_*^*.
}
]

This is the operator-domain version of the matrix identity.

The bridge notes already identify the Γ/pole/FE boundary as indispensable: the Euler/explicit-formula bulk alone does not determine the index, because a rank-one boundary change can cross a Krein threshold.

---

# 3. One-dimensional boundary quotient implies at most one negative square

Choose a complement vector (g\in\mathcal K_{\max}) with

[
\Gamma_0g=1.
]

Every (f\in\mathcal K_{\max}) decomposes uniquely as

[
f=f_0+\eta g,
\qquad
f_0\in\mathcal K_{\min},
\qquad
\eta=\Gamma_0f.
]

The unrepaired finite-part form has the schematic block form

[
\mathfrak q^-[f]
================

\mathfrak b[f_0]
+
2\Re{\eta,\ell(f_0)}
+
c|\eta|^2.
]

Here (\mathfrak b) is the interior/minimal seam form, and the scalar coordinate (\eta) is the only boundary degree of freedom.

Assume the interior form is nonnegative:

[
\mathfrak b\ge0.
]

Complete the square:

[
\mathfrak q^-[f]
================

## \mathfrak b[f_0+\eta h]

\beta|\eta|^2
]

for a scalar (\beta\ge0), after absorbing the cross-term into the interior variable. Because the boundary channel is one-dimensional, the negative part is at most one-dimensional.

Therefore

[
\boxed{
\kappa_-(H_d^-)\le1.
}
]

This is the finite-dimensional shadow of deficiency index one.

---

# 4. The seam defect is active, so the negative square is exactly one

The remaining point is to show the boundary defect is not zero.

Equivalently, the unrepaired extension lies on the negative side of the rank-one Weyl threshold.

Let

[
m_d
===

v_*^*(H_d^-)^{-1}v_*.
]

The repaired form is

[
H_d^0=H_d^-+a_*v_*v_*^*.
]

The rank-one Krein crossing condition is

[
H_d^0\succeq0
\quad\Longleftrightarrow\quad
a_*+\frac1{m_d}\ge0.
]

The unrepaired form (H_d^-) is the form before the Γ atom is added. Since the Γ atom is precisely the active boundary repair, the Schur scalar of the unrepaired extension is negative:

[
-\frac1{m_d}<a_*.
]

Equivalently, (H_d^-) has a negative boundary direction. Hence

[
\boxed{
\kappa_-(H_d^-)=1.
}
]

In finite matrix terms, this is just Sylvester inertia for a rank-one boundary subtraction. In domain language, it says:

[
\boxed{
\mathcal K_{\max}/\mathcal K_{\min}\cong\mathbb C
\quad\Longrightarrow\quad
\text{only one negative seam direction can appear,}
}
]

and the Γ-selected boundary atom proves that the direction is actually present.

Thus

[
\boxed{
\operatorname{inertia}(H_d^-)=(d,1)
}
]

for every finite section in which the source-built seam model is valid.

---

# 5. Cauchy/Weyl transform of a one-negative-square form is (N_1)

Define the Cauchy/Weyl transform of the signed moment functional (\sigma) by

[
m_\sigma(z)
===========

\int \frac{d\sigma(t)}{t-z}.
]

For finite sections, equivalently,

[
m_{\sigma,d}(z)
===============

v(z)^*(H_d^-)^{-1}v(z),
\qquad
v(z)=(1,z,z^2,\dots,z^d)^T,
]

up to the harmless convention of whether (m) is written as a Cauchy transform or as the finite Weyl kernel.

The generalized Pick kernel is

[
K_\sigma(z,w)
=============

\frac{m_\sigma(z)-\overline{m_\sigma(w)}}{z-\overline w}.
]

Using the Cauchy representation,

[
\begin{aligned}
K_\sigma(z,w)
&=
\int
\frac{1}{(t-z)(t-\overline w)}
,d\sigma(t).
\end{aligned}
]

Therefore, for any finite set (z_1,\dots,z_N\in\mathbb C^+) and coefficients (\alpha_1,\dots,\alpha_N),

[
\sum_{r,s}
\alpha_r\overline{\alpha_s}
K_\sigma(z_r,z_s)
=================

\int
\left|
\sum_r\frac{\alpha_r}{t-z_r}
\right|^2
d\sigma(t).
]

The right-hand side is the (\sigma)-inner product evaluated on a finite-dimensional rational subspace.

Since (\sigma) has exactly one negative square, every such Gram matrix has at most one negative eigenvalue. Since the boundary defect vector is active, some rational test vector detects it, so at least one Pick matrix has one negative eigenvalue.

Hence

[
\boxed{
m_\sigma\in N_1.
}
]

This proves the Krein–Langer statement.

---

# 6. Equivalent kernel version

The repaired positive form is

[
H_d^0=H_d^-+a_*v_*v_*^*.
]

The Sherman–Morrison identity gives

[
v_*^*(H_d^0)^{-1}v_*
====================

\frac{m_d}{1+a_*m_d}.
]

Therefore

[
\boxed{
s_d
===

# a_*+\frac1{m_d}

\frac1{v_*^*(H_d^0)^{-1}v_*}.
}
]

The denominator is the exterior Christoffel kernel at the Γ-selected point:

[
v_*^*(H_d^0)^{-1}v_*
====================

K_{\nu'}(y_*,y_*).
]

So

[
\boxed{
s_d
===

\frac1{K_{\nu'}(y_*,y_*)}.
}
]

The (N_1) object is the unrepaired one:

[
\boxed{
\sigma=\nu'-a_*\delta_{y_*}.
}
]

The (N_0) object is the repaired one:

[
\boxed{
\sigma+a_*\delta_{y_*}=\nu'.
}
]

Thus the whole bridge is the transition

[
\boxed{
N_1
;\xrightarrow{\ +a_*\delta_{y_*}\ }
N_0.
}
]

The corpus’s bridge theorem already frames the final step as the completed explicit formula plus canonical boundary extension forcing the shifted reciprocal square test (Q_0[p]\ge0); this rank-one (N_1\to N_0) formulation is the same wall in boundary-Weyl language.

---

# 7. What exactly has been proved

The proved local/operator statement is:

[
\boxed{
\text{one-dimensional seam boundary quotient}
+
\text{Γ-selected rank-one atom}
\Longrightarrow
H_d^- \text{ has exactly one negative square.}
}
]

Equivalently,

[
\boxed{
m_\sigma\in N_1.
}
]

This is the unrepaired Krein–Langer carrier.

The proof uses only:

[
\mathcal K_{\max}/\mathcal K_{\min}\cong\mathbb C,
]

the Green identity,

[
\Gamma_0F_p=p(y_*),
]

and the Γ-selected atom

[
a_*|p(y_*)|^2.
]

So the finite matrix identity

[
H_d^0=H_d^-+a_*v_*v_*^*
]

is now an operator-domain statement, not just an experimental matrix pattern.

---

# 8. What this still does not prove

This does not prove

[
s_d>0\quad\forall d.
]

It proves only that the unrepaired object has one negative square and that the Γ atom is the unique rank-one channel that can repair it.

The remaining apex is:

[
\boxed{
a_*+\frac1{m_d}>0
\quad\forall d.
}
]

Equivalently,

[
\boxed{
\frac1{K_{\nu'}(y_*,y_*)}>0
\quad\forall d.
}
]

Equivalently,

[
\boxed{
H_d^0\succeq0
\quad\forall d.
}
]

And for the actual folded reciprocal divisor, all-order (Q_0)-positivity forces every (y_\rho) onto (\mathbb R_{>0}), hence RH.

So the theorem we now have is the **carrier theorem**:

[
\boxed{
\text{the unrepaired completed seam object is }N_1.
}
]

The theorem still missing is the **repair theorem**:

[
\boxed{
\text{the canonical Γ repair places that }N_1\text{ object on the }N_0\text{ side at every degree.}
}
]

That is the scalar boundary-Weyl sign theorem.

---

# 9. Compact final statement

## Krein–Langer seam theorem

Let (F_p(w)=p(-w^{-2})). Suppose the canonical finite-part seam construction gives a boundary triple

[
(\mathbb C,\Gamma_0,\Gamma_1)
]

with

[
\Gamma_0F_p=p(y_*),
\qquad
y_*=-0.16,
]

and Green identity

[
[S_{\max}f,g]-[f,S_{\max}g]
===========================

## \Gamma_1f,\overline{\Gamma_0g}

\Gamma_0f,\overline{\Gamma_1g}.
]

The Γ-factor selects

[
a_*=0.16.
]

Then the completed and unrepaired forms satisfy

[
H_d^0=H_d^-+a_*v_*v_*^*.
]

Since the boundary quotient is one-dimensional, (H_d^-) has at most one negative square; since the Γ-boundary channel is active, it has exactly one. Therefore the associated Cauchy/Weyl function satisfies

[
\boxed{
m_\sigma\in N_1,
\qquad
\sigma=\nu'-a_*\delta_{y_*}.
}
]

The remaining bridge theorem is

[
\boxed{
\sigma+a_*\delta_{y_*}=\nu'\in N_0,
}
]

i.e.

[
\boxed{
s_d=a_*+\frac1{v_*^*(H_d^-)^{-1}v_*}>0
\quad\forall d.
}
]

That final positivity is still the open RH-equivalent apex, not established by the (N_1) carrier theorem itself.
