# Canonical-gauge extraction lemma

This is the local gauge lemma you need. It proves the precise transformation law under

[
\Xi(w)\mapsto e^{q(w^2)}\Xi(w),
]

and it gives the canonical subtraction rule. It does **not** prove the final positivity / RH step; it only fixes the source-extraction ambiguity. That matters because the bridge theorem’s target is specifically source-built shifted reciprocal positivity, not another RH-equivalent restatement.

---

## 0. Normalization choice

Let

[
\Xi(w)=\xi!\left(\frac12+w\right).
]

It is even. For a zero orbit ([a]={a,-a}), define

[
y_a=-a^{-2}.
]

The reciprocal moments are

[
T_k=\sum_{\rho}m_\rho y_\rho^k,
\qquad k\ge1.
]

Equivalently, after folding (\pm a),

[
T_k=\sum_{[a]}2m_a y_a^k.
]

The bridge theorem uses exactly these (T_k), with the shifted square form

[
Q_0[p]=\sum_{i,j}b_i b_jT_{i+j+1}.
]

The (T_0) tower is not part of the finite object because (T_0=\infty); the shifted towers are the correct finite certificate.

To match your observed law

[
q(w^2)=cw^2
\quad\Rightarrow\quad
T_1\mapsto T_1+2c,
]

define the monomial singular test by

[
\boxed{
h_k(w)=2(-w^{-2})^k=2(-1)^kw^{-2k}.
}
]

That factor (2) is only a convention. Without it, every formula below is divided by (2).

---

# Lemma 1 — raw local extraction

Define the finite-part extraction functional

[
\boxed{
\mathcal T_k(F)
===============

\operatorname{FP}^{\xi}_{w=0}
\left[
-\frac12 h_k(w)\frac{F'(w)}{F(w)},dw
\right].
}
]

For the canonical (\Xi),

[
\boxed{
\mathcal T_k(\Xi)=T_k.
}
]

---

## Proof

Because (\Xi) is even and has no zero at (w=0), its canonical paired product has logarithmic derivative

[
\frac{\Xi'}{\Xi}(w)
===================

\sum_{[a]}m_a
\left(
\frac1{w-a}+\frac1{w+a}
\right).
]

For one pair,

[
\frac1{w-a}+\frac1{w+a}
=======================

\frac{2w}{w^2-a^2}.
]

Since

[
y_a=-a^{-2},
]

we get

[
\frac{2w}{w^2-a^2}
==================

# \frac{2wy_a}{1+y_aw^2}

2\sum_{n\ge0}(-1)^n y_a^{n+1}w^{2n+1}.
]

Summing over folded zero orbits gives

[
\boxed{
\frac{\Xi'}{\Xi}(w)
===================

\sum_{n\ge0}(-1)^nT_{n+1}w^{2n+1}.
}
]

Now multiply by

[
h_k(w)=2(-1)^kw^{-2k}.
]

The residue of

[
-\frac12h_k(w)\frac{\Xi'}{\Xi}(w),dw
]

comes only from the coefficient (n=k-1):

[
-\frac12\cdot
2(-1)^kw^{-2k}
\cdot
(-1)^{k-1}T_k w^{2k-1}
======================

T_k w^{-1}.
]

Therefore

[
\mathcal T_k(\Xi)=T_k.
]

So the local extraction is exactly the reciprocal moment.

---

# Lemma 2 — regulator independence

Let (\eta,\psi) be admissible even cutoffs, with (\eta(w/\epsilon)) cutting out (w=0) and (\psi(w/R)) imposing a large window. Let

[
h_{k,\epsilon,R}(w)
===================

h_k(w)\eta(w/\epsilon)\psi(w/R).
]

Then, after subtracting the divergent local powers in (\epsilon),

[
\operatorname{FP}*{\epsilon=0,R=\infty}
\left[
-\frac12h*{k,\epsilon,R}(w)\frac{F'}F(w),dw
\right]
]

is independent of the admissible even regulator.

---

## Proof

Near (w=0), write

[
\frac{F'}F(w)=\sum_{n\ge0}\ell_n w^{2n+1}
]

in the canonical even seam normalization. Then

[
-\frac12 h_k(w)\frac{F'}F(w)
============================

-\frac12\cdot 2(-1)^kw^{-2k}
\sum_{n\ge0}\ell_nw^{2n+1}.
]

So

[
-\frac12 h_k(w)\frac{F'}F(w)
============================

\sum_{n\ge0}
-(-1)^k\ell_n w^{2n+1-2k}.
]

Terms with

[
2n+1-2k<-1
]

produce divergent powers of (\epsilon). Terms with

[
2n+1-2k>-1
]

vanish as (\epsilon\to0). The only finite residue term is

[
2n+1-2k=-1,
]

so

[
n=k-1.
]

Thus the finite part is the coefficient of (w^{-1}), namely

[
\boxed{
\mathcal T_k(F)=(-1)^{k+1}\ell_{k-1}.
}
]

This coefficient is local and regulator-independent. Changing the even cutoff only changes the subtracted divergent powers. In non-even or noncanonically normalized schemes a logarithmic local term can appear, but it is a local gauge counterterm; in the canonical (\xi)-gauge it is set to zero.

---

# Lemma 3 — zero-free gauge transformation law

Let

[
F_q(w)=e^{q(w^2)}F(w),
]

where

[
q(z)=\sum_{r\ge1}a_r z^r.
]

Then

[
\boxed{
\mathcal T_k(F_q)
=================

\mathcal T_k(F)
+
2k(-1)^{k+1}a_k.
}
]

Equivalently,

[
\boxed{
T_k\mapsto T_k+2k(-1)^{k+1}a_k.
}
]

This is diagonal in (k): only the coefficient (a_k) affects (T_k).

---

## Proof

The logarithmic derivative changes by

[
\frac{F_q'}{F_q}(w)
===================

\frac{F'}F(w)
+
\frac{d}{dw}q(w^2).
]

Since

[
q(w^2)=\sum_{r\ge1}a_rw^{2r},
]

we have

[
\frac{d}{dw}q(w^2)
==================

\sum_{r\ge1}2r a_rw^{2r-1}.
]

Therefore

[
\Delta_q\mathcal T_k
====================

\operatorname{FP}*{w=0}
\left[
-\frac12 h_k(w)
\sum*{r\ge1}2r a_rw^{2r-1},dw
\right].
]

Insert

[
h_k(w)=2(-1)^kw^{-2k}.
]

Then

[
\Delta_q\mathcal T_k
====================

\operatorname{Res}*{w=0}
\left[
-\frac12
\cdot
2(-1)^kw^{-2k}
\sum*{r\ge1}2r a_rw^{2r-1}
,dw
\right].
]

So

[
\Delta_q\mathcal T_k
====================

\operatorname{Res}*{w=0}
\left[
\sum*{r\ge1}
-2r(-1)^k a_r
w^{2r-2k-1}
,dw
\right].
]

A residue occurs only when

[
2r-2k-1=-1,
]

hence

[
r=k.
]

Thus

[
\Delta_q\mathcal T_k
====================

# -2k(-1)^ka_k

2k(-1)^{k+1}a_k.
]

So

[
\boxed{
\mathcal T_k(F_q)
=================

\mathcal T_k(F)
+
2k(-1)^{k+1}a_k.
}
]

For (k=1),

[
\Delta_qT_1=2a_1.
]

If (q(w^2)=cw^2), this gives

[
\boxed{
T_1\mapsto T_1+2c,
}
]

which is exactly your comp68 law.

---

# Corollary 1 — Hankel counterterm for (Q_0)

Let

[
p(y)=\sum_{i=0}^d b_i y^i.
]

The shifted square form is

[
Q_0[p]=\sum_{i,j=0}^d b_i b_jT_{i+j+1}.
]

Under

[
F\mapsto e^{q(w^2)}F,
\qquad
q(w^2)=\sum_{r\ge1}a_rw^{2r},
]

the form changes by

[
\boxed{
\Delta_qQ_0[p]
==============

\sum_{i,j=0}^d
b_i b_j,
2(i+j+1)(-1)^{i+j+2}
a_{i+j+1}.
}
]

So the matrix counterterm is

[
\boxed{
(\Delta_qH^{(0)})_{ij}
======================

2(i+j+1)(-1)^{i+j+2}a_{i+j+1}.
}
]

This is Hankel: it depends only on (i+j).

For the companion shifted tower

[
Q_1[p]=\sum_{i,j}b_ib_jT_{i+j+2},
]

the counterterm is

[
\boxed{
(\Delta_qH^{(1)})_{ij}
======================

2(i+j+2)(-1)^{i+j+3}a_{i+j+2}.
}
]

Thus zero-free gauge freedom never produces arbitrary noise. It produces an explicitly subtractable finite Hankel counterterm.

---

# Corollary 2 — canonical (\xi)-gauge

Let (F) be a representative in the zero-free even gauge class

[
F=e^{q(w^2)}\Xi_{\mathrm{can}},
\qquad
q(w^2)=\sum_{r\ge1}a_rw^{2r},
]

where

[
\Xi_{\mathrm{can}}(w)=\xi!\left(\frac12+w\right)
]

is the canonical completed Riemann (\xi)-normalization.

Define

[
\boxed{
T_k^{\mathrm{can}}(F)
=====================

## \mathcal T_k(F)

2k(-1)^{k+1}a_k.
}
]

Then

[
\boxed{
T_k^{\mathrm{can}}(F)=T_k^{\mathrm{can}}(\Xi_{\mathrm{can}})=T_k.
}
]

In the canonical representative itself,

[
q=0,
]

so

[
\boxed{
T_k^{\mathrm{can}}
==================

\operatorname{FP}_{w=0}^{\xi}
\left[
-\frac12 h_k(w)\frac{\Xi'}{\Xi}(w),dw
\right].
}
]

This is the canonical-gauge extraction rule.

---

## What “annihilating zero-free terms” means

The zero-free even multiplier contributes

[
2wq'(w^2)
=========

\sum_{r\ge1}2r a_rw^{2r-1}
]

to the logarithmic derivative. The canonical (\xi)-gauge is the rule:

[
\boxed{
a_r=0\quad\text{for all }r\ge1.
}
]

Equivalently, one works with the completed Riemann normalization

[
\xi(s)
======

\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
]

then recentres

[
\Xi(w)=\xi!\left(\frac12+w\right).
]

Any other even zero-free representative must be projected back by subtracting

[
\boxed{
2k(-1)^{k+1}a_k
}
]

from the raw extracted (T_k).

So the canonical moments are the quotient:

[
\boxed{
T_k^{\mathrm{can}}
==================

T_k^{\mathrm{raw}}
\mod
\left{
2k(-1)^{k+1}a_k
\right}_{k\ge1}.
}
]

But for the actual completed (\xi), the quotient is fixed by the source formula: Γ, pole, FE, and Euler product choose the representative. This is why the boundary extension cannot be omitted in the bridge theorem. The files already flag that the source-built object must be completed, include Γ, and avoid zero-feeding; otherwise it is only RH-equivalent packaging.

---

# Final theorem statement

## Canonical-gauge extraction theorem

Let

[
\Xi(w)=\xi!\left(\frac12+w\right),
\qquad
h_k(w)=2(-w^{-2})^k.
]

For (k\ge1), define

[
\boxed{
T_k^{\mathrm{raw}}(F)
=====================

\operatorname{FP}_{w=0}
\left[
-\frac12 h_k(w)\frac{F'}F(w),dw
\right].
}
]

Then:

1. For the canonical completed (\xi)-representative,

[
\boxed{
T_k^{\mathrm{raw}}(\Xi)=T_k.
}
]

2. The finite part is independent of admissible even regulators; regulator changes alter only subtracted local divergent jets, and noncanonical logarithmic terms are local gauge counterterms.

3. Under the zero-free even gauge

[
F\mapsto F_q=e^{q(w^2)}F,
\qquad
q(w^2)=\sum_{r\ge1}a_rw^{2r},
]

one has

[
\boxed{
T_k^{\mathrm{raw}}(F_q)
=======================

T_k^{\mathrm{raw}}(F)
+
2k(-1)^{k+1}a_k.
}
]

4. Therefore the canonical gauge-invariant extraction is

[
\boxed{
T_k^{\mathrm{can}}(F_q)
=======================

## T_k^{\mathrm{raw}}(F_q)

2k(-1)^{k+1}a_k.
}
]

5. On the shifted Hankel tower,

[
\boxed{
(\Delta_qH^{(0)})_{ij}
======================

2(i+j+1)(-1)^{i+j+2}a_{i+j+1},
}
]

and similarly

[
\boxed{
(\Delta_qH^{(1)})_{ij}
======================

2(i+j+2)(-1)^{i+j+3}a_{i+j+2}.
}
]

So the zero-free ambiguity is completely local, triangular/diagonal at the moment level, and Hankel at the form level.

---

## Why this matters

The comp68 issue is now resolved cleanly:

[
q(w^2)=cw^2
\quad\Rightarrow\quad
T_1^{\mathrm{raw}}\mapsto T_1^{\mathrm{raw}}+2c.
]

More generally,

[
q(w^2)=\sum_{r\ge1}a_rw^{2r}
\quad\Rightarrow\quad
T_k^{\mathrm{raw}}\mapsto
T_k^{\mathrm{raw}}+2k(-1)^{k+1}a_k.
]

So the source-extraction lemma must **never** use raw low-order Taylor coefficients without first fixing canonical (\xi). Once the canonical gauge is fixed, the extraction is well-defined; if another representative is used, the correction is explicit and subtractable.

This does not prove the bridge positivity

[
Q_0[p]\ge0\quad\forall p.
]

It only proves that the moments entering the bridge can be extracted in a gauge-canonical way. The remaining apex is still the source-built positivity / faithful-index theorem: construct the completed object without zero-feeding, prove its index equals the off-line zero count, and prove the scalar/Weyl sign stays positive at all orders.
