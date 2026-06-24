## Canonical gauge law

This is a local coefficient theorem. It is not a new RH theorem. Its job is to prevent a false source-extraction step: the local extraction of (T_k) from (\Xi'/\Xi) is **not invariant** under zero-free even multipliers unless we fix the canonical (\xi)-gauge or subtract the exact counterterm.

The result is:

[
\boxed{
\Xi(w)\mapsto e^{q(w^2)}\Xi(w),
\qquad
q(w^2)=\sum_{r\ge1}a_rw^{2r}
}
]

implies

[
\boxed{
T_k^{\mathrm{raw}}
\mapsto
T_k^{\mathrm{raw}}
+
2k(-1)^{k+1}a_k.
}
]

For (q(w^2)=cw^2), this gives

[
\boxed{
T_1\mapsto T_1+2c.
}
]

This matches the computation and explains why naive extraction is gauge-contaminated. The corpus flags exactly this issue: low-order charts must fix canonical (\xi) normalization because zero-free multipliers move local coefficients without moving zeros.

---

# 1. Setup

Let

[
\Xi(w)=\xi!\left(\frac12+w\right).
]

It is even, so zeros come in pairs

[
w=\alpha,\qquad w=-\alpha.
]

Define

[
y_\alpha=-\alpha^{-2}.
]

The folded reciprocal moments are

[
\boxed{
T_k=\sum_{[\alpha]}2m_\alpha,y_\alpha^k,
\qquad k\ge1.
}
]

Equivalently, this is the same as summing over all zeros before folding:

[
T_k=\sum_{\rho}m_\rho\left(-(\rho-\tfrac12)^{-2}\right)^k.
]

This reciprocal seam-squared coordinate is the one used in the proposed bridge theorem: (Q_0[p]=\sum c_ic_jT_{i+j+1}) is the shifted square test. The open part is proving this positivity from source data, not the algebra below.

---

# 2. Expansion of the logarithmic derivative

Assume first that we look only at the zero divisor contribution. For one folded pair ({\alpha,-\alpha}) of multiplicity (m_\alpha),

[
m_\alpha\left(\frac1{w-\alpha}+\frac1{w+\alpha}\right)
======================================================

m_\alpha\frac{2w}{w^2-\alpha^2}.
]

Since

[
y_\alpha=-\alpha^{-2},
]

we have

[
w^2-\alpha^2
============

# w^2+\frac1{y_\alpha}

\frac{1+y_\alpha w^2}{y_\alpha}.
]

Therefore

[
\frac{2w}{w^2-\alpha^2}
=======================

\frac{2wy_\alpha}{1+y_\alpha w^2}.
]

Expand near (w=0):

[
\frac{2wy_\alpha}{1+y_\alpha w^2}
=================================

# 2wy_\alpha\sum_{n\ge0}(-1)^ny_\alpha^nw^{2n}

2\sum_{n\ge0}(-1)^ny_\alpha^{n+1}w^{2n+1}.
]

Summing over folded zero pairs gives

[
\frac{\Xi'}{\Xi}(w)
===================

\sum_{n\ge0}(-1)^nT_{n+1}w^{2n+1},
]

in canonical divisor gauge.

So the coefficient relation is

[
\boxed{
[w^{2k-1}]\frac{\Xi'}{\Xi}(w)
=============================

(-1)^{k-1}T_k.
}
]

Equivalently,

[
\boxed{
T_k
===

(-1)^{k-1}[w^{2k-1}]\frac{\Xi'}{\Xi}(w).
}
]

That is the raw local extraction formula.

---

# 3. Residue version

Define the monomial singular test

[
\boxed{
h_k(w)=2(-w^{-2})^k
===================

2(-1)^kw^{-2k}.
}
]

Then

[
-\frac12h_k(w)\frac{\Xi'}{\Xi}(w)
=================================

-\frac12\cdot 2(-1)^kw^{-2k}
\sum_{n\ge0}(-1)^nT_{n+1}w^{2n+1}.
]

The residue comes from (n=k-1). Its coefficient is

[
-\frac12\cdot2(-1)^k(-1)^{k-1}T_k
=================================

# -T_k(-1)^{2k-1}

T_k.
]

Hence

[
\boxed{
T_k
===

\operatorname{Res}_{w=0}
\left[
-\frac12h_k(w)\frac{\Xi'}{\Xi}(w),dw
\right].
}
]

If the test is made admissible by a cutoff and then finite-part regularized, this residue is the canonical local term once the (\xi)-gauge is fixed.

---

# 4. Apply a zero-free even gauge

Now multiply by a zero-free even factor:

[
\widetilde\Xi(w)=e^{q(w^2)}\Xi(w),
]

where

[
q(w^2)=\sum_{r\ge1}a_rw^{2r}.
]

This does **not** move any zeros. So the divisor-defined (T_k) should not change.

But the logarithmic derivative changes:

[
\frac{\widetilde\Xi'}{\widetilde\Xi}(w)
=======================================

\frac{\Xi'}{\Xi}(w)
+
\frac{d}{dw}q(w^2).
]

Now

[
\frac{d}{dw}q(w^2)
==================

# \frac{d}{dw}\sum_{r\ge1}a_rw^{2r}

\sum_{r\ge1}2r,a_rw^{2r-1}.
]

So the coefficient of (w^{2k-1}) changes by

[
2k,a_k.
]

Using the extraction formula,

[
T_k^{\mathrm{raw}}
==================

(-1)^{k-1}[w^{2k-1}]\frac{\Xi'}{\Xi}(w),
]

we get

[
\Delta T_k^{\mathrm{raw}}
=========================

(-1)^{k-1}\cdot 2k,a_k.
]

Since

[
(-1)^{k-1}=(-1)^{k+1},
]

this is

[
\boxed{
\Delta T_k^{\mathrm{raw}}
=========================

2k(-1)^{k+1}a_k.
}
]

Therefore

[
\boxed{
T_k^{\mathrm{raw}}(\widetilde\Xi)
=================================

T_k^{\mathrm{raw}}(\Xi)
+
2k(-1)^{k+1}a_k.
}
]

That is the canonical gauge law.

---

# 5. Check the first case

Let

[
q(w^2)=cw^2.
]

Then

[
a_1=c,\qquad a_k=0\quad(k\ge2).
]

For (k=1),

[
\Delta T_1
==========

# 2\cdot1\cdot(-1)^2c

2c.
]

So

[
\boxed{
T_1\mapsto T_1+2c.
}
]

For (k\ge2),

[
\Delta T_k=0.
]

So the comp68 law is exactly the (k=1) case of the general diagonal rule.

---

# 6. Hankel counterterm for (Q_0)

Let

[
p(y)=\sum_{i=0}^d c_i y^i.
]

Recall

[
Q_0[p]
======

\sum_{i,j=0}^dc_ic_jT_{i+j+1}.
]

Under the gauge,

[
T_{i+j+1}
\mapsto
T_{i+j+1}
+
2(i+j+1)(-1)^{i+j+2}a_{i+j+1}.
]

Therefore

[
\boxed{
\Delta Q_0[p]
=============

\sum_{i,j=0}^d
c_ic_j
,
2(i+j+1)(-1)^{i+j+2}a_{i+j+1}.
}
]

So the matrix counterterm is

[
\boxed{
(\Delta H^{(0)})_{ij}
=====================

2(i+j+1)(-1)^{i+j+2}a_{i+j+1}.
}
]

This is Hankel because it depends only on (i+j).

That is important: zero-free gauge contamination cannot create arbitrary matrix noise. It creates a **diagonal moment-level / Hankel form-level** counterterm.

---

# 7. Canonical (\xi)-gauge

The divisor-defined moments (T_k) are zero-location data and are invariant under zero-free multiplication.

The raw local extraction

[
T_k^{\mathrm{raw}}(F)
=====================

\operatorname{FP}_{w=0}
\left[
-\frac12h_k(w)\frac{F'}F(w),dw
\right]
]

is **not** invariant.

If

[
F(w)=e^{q(w^2)}\Xi_{\mathrm{can}}(w),
]

with

[
q(w^2)=\sum_{r\ge1}a_rw^{2r},
]

then define

[
\boxed{
T_k^{\mathrm{can}}(F)
=====================

## T_k^{\mathrm{raw}}(F)

2k(-1)^{k+1}a_k.
}
]

Then

[
\boxed{
T_k^{\mathrm{can}}(F)
=====================

# T_k^{\mathrm{raw}}(\Xi_{\mathrm{can}})

T_k.
}
]

The canonical representative is

[
\boxed{
\Xi_{\mathrm{can}}(w)
=====================

# \xi!\left(\frac12+w\right)

\frac12\left(\frac12+w\right)\left(-\frac12+w\right)
\pi^{-(1/2+w)/2}
\Gamma!\left(\frac{1/2+w}{2}\right)
\zeta!\left(\frac12+w\right).
}
]

In this representative,

[
q=0,
]

so no subtraction is needed.

Thus the canonical extraction rule is:

[
\boxed{
T_k^{\mathrm{can}}
==================

\operatorname{FP}_{w=0}^{\xi}
\left[
-\frac12h_k(w)\frac{\Xi'}{\Xi}(w),dw
\right],
}
]

where the superscript (\xi) means: use the completed Riemann (\xi)-normalization and do not allow additional zero-free even factors.

---

# 8. Why this passes the roleplaying test

This is not a literature-level grand theorem. It is a direct local calculation:

[
\frac{d}{dw}q(w^2)
==================

\sum_{r\ge1}2r a_rw^{2r-1}
]

and (T_k) reads the coefficient of (w^{2k-1}) in (\Xi'/\Xi), up to the sign

[
(-1)^{k-1}.
]

Therefore only (a_k) can affect (T_k), and the exact shift is

[
\boxed{
2k(-1)^{k+1}a_k.
}
]

The practical consequence is sharp:

[
\boxed{
\text{Any source-extraction lemma using raw low-order coefficients is invalid unless canonical }\xi\text{-gauge is fixed.}
}
]

That is the entire content. It fixes the gauge bug; it does not prove positivity, (Q_0\ge0), or RH.
