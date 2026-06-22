## Derived effective law

Let

[
y_*=-a,\qquad a=|y_*|>0,
]

and let

[
x_n=y_n=\gamma_n^{-2}>0
]

be the reciprocal zero atoms on RH. The shifted zero measure used by the (Q_0) form is

[
\nu'=\sum_n 2x_n,\delta_{x_n},
]

so the degree-(d) exterior Christoffel inverse at (y_*=-a) is

[
\lambda_d(a)
============

# \frac{1}{K_{\nu'}(-a,-a)}

\min_{\deg p\le d,\ p(-a)=1}
\int p(y)^2,d\nu'(y).
]

By your comp54, this (\lambda_d(a)) is exactly the scalar Weyl gap, up to the fixed boundary normalization; the earlier bridge file already identifies the same object as the inverse Christoffel kernel at the coarsest trivial-zero point.

The empirical parity law

[
\alpha(a)\approx 4.31+\frac12\ln a
]

comes out of the following more precise finite-degree formula:

[
\boxed{
\alpha_d(a)
\approx
4+
\frac{4(1-\ln 2)+2\ln a}{\bar L_d}
}
]

where

[
\bar L_d=\frac1d\sum_{j=1}^d\ln \gamma_j.
]

In the tested degree range, (\bar L_d\approx 4), so

[
\alpha_d(a)
\approx
4+\frac{4(1-\ln2)}4+\frac{2\ln a}{4}
====================================

4.30685+\frac12\ln a.
]

That is the observed law.

So the cleaner derived statement is:

[
\boxed{
\alpha_d(y_*)
\approx
4+
\frac{4(1-\ln2)+2\ln |y_*|}{\bar L_d}
}
]

and the empirical formula

[
\boxed{
\alpha(y_*)\approx4.31+\frac12\ln|y_*|
}
]

is the (\bar L_d\approx4) finite-window specialization.

---

## Derivation

The Christoffel inverse is the norm of the polynomial of degree (d) that equals (1) at the exterior point (-a) and is as small as possible on the positive support. Since the support is a reciprocal hard-edge atom cloud accumulating at (0^+), the extremal polynomial essentially kills the first (d) resolved atoms:

[
p_d(y)
\approx
\prod_{j=1}^d
\frac{y-x_j}{-a-x_j}.
]

This is the exterior-Christoffel version of the auto-deflating extremal polynomial already observed in the corpus: the dangerous polynomial places roots on the dominant reciprocal atoms, while the remaining obstruction lives deeper in the hard edge.

Now evaluate the norm near the next unresolved atom (x_{d+1}). The main exponential scale is

[
\lambda_d(a)
\sim
2x_{d+1}
\prod_{j=1}^d
\left(
\frac{x_{d+1}-x_j}{a+x_j}
\right)^2
\times
\text{tail corrections}.
]

For the Γ-selected exterior points (a=0.16,4/9,4), one has (a\gg x_j), because (x_1=1/\gamma_1^2\approx0.005). Hence

[
a+x_j=a(1+o(1))
]

on the exponential scale, and therefore

[
\log\lambda_d(a)
\approx
2\sum_{j=1}^d\log x_j
-2d\log a
+
2\sum_{j=1}^d
\log\left(1-\frac{x_{d+1}}{x_j}\right)
+
O(\log d).
]

Since

[
x_j=\gamma_j^{-2},
]

the first term is

[
2\sum_{j=1}^d\log x_j
=====================

# 2\sum_{j=1}^d(-2\log\gamma_j)

-4\sum_{j=1}^d\log\gamma_j.
]

This is the universal reciprocal-square exponent (4). This matches the earlier bridge diagnosis: the no-margin rate is generic hard-edge geometry, and the RH content is the sign, not the exponent.

Now set

[
S_d=\sum_{j=1}^d\log\gamma_j=d\bar L_d.
]

Define the effective exponent by

[
\lambda_d(a)
\approx
\exp[-\alpha_d(a)S_d].
]

Then

[
-\alpha_d(a)S_d
\approx
-4S_d
-2d\log a
+
2\sum_{j=1}^d
\log\left(1-\frac{x_{d+1}}{x_j}\right).
]

So

[
\alpha_d(a)
\approx
4
+
\frac{2d\log a}{S_d}
--------------------

\frac{2}{S_d}
\sum_{j=1}^d
\log\left(1-\frac{x_{d+1}}{x_j}\right).
]

The last term is the hard-edge spacing correction.

---

## Where (4(1-\ln 2)) comes from

The hard-edge envelope is

[
d\nu'(y)\sim |\log y|,y^{-1/2}dy,
\qquad y\to0^+,
]

for the shifted zero measure; equivalently, because each atom has mass (2x_n), the underlying support-counting density behaves like

[
dN(y)\sim |\log y|,y^{-3/2}dy.
]

This is the same hard-edge structure described in the bridge file: high zeros map to (y=1/\gamma^2\to0^+), (T_0) diverges while (T_1) converges, and (Q_0) is the marginal slow object that feels this edge.

The quantile law is therefore

[
x_j
===

\gamma_j^{-2}
\sim
C\frac{(\log j)^2}{j^2}.
]

Ignore the slowly varying (\log j) for the leading spacing integral. Then

[
\frac{x_{d+1}}{x_j}
\approx
\left(\frac{j}{d+1}\right)^2.
]

Hence

[
2\sum_{j=1}^d
\log\left(1-\frac{x_{d+1}}{x_j}\right)
\approx
2d\int_0^1\log(1-t^2),dt.
]

Compute the integral:

[
\int_0^1\log(1-t^2),dt
======================

\int_0^1\log(1-t),dt
+
\int_0^1\log(1+t),dt.
]

Now

[
\int_0^1\log(1-t),dt=-1,
]

and

[
\int_0^1\log(1+t),dt=2\ln2-1.
]

Therefore

[
\int_0^1\log(1-t^2),dt
======================

2\ln2-2.
]

So

[
2d\int_0^1\log(1-t^2),dt
========================

# 2d(2\ln2-2)

-4(1-\ln2)d.
]

Thus

[
-\frac{2}{S_d}
\sum_{j=1}^d
\log\left(1-\frac{x_{d+1}}{x_j}\right)
\approx
\frac{4(1-\ln2)d}{S_d}
======================

\frac{4(1-\ln2)}{\bar L_d}.
]

Putting this into the exponent gives

[
\boxed{
\alpha_d(a)
\approx
4+
\frac{4(1-\ln2)}{\bar L_d}
+
\frac{2\ln a}{\bar L_d}
}
]

or

[
\boxed{
\alpha_d(y_*)
\approx
4+
\frac{4(1-\ln2)+2\ln|y_*|}{\bar L_d}.
}
]

That is the derived parity/protector-point formula.

---

## Freezing the finite-window mean gives the empirical law

In the observed degree range,

[
\bar L_d=\frac1d\sum_{j=1}^d\ln\gamma_j\approx4.
]

Therefore

[
\frac{4(1-\ln2)}{\bar L_d}
\approx
\frac{1.227411}{4}
\approx
0.30685,
]

and

[
\frac{2}{\bar L_d}\ln a
\approx
\frac12\ln a.
]

Hence

[
\alpha(a)
\approx
4+0.30685+\frac12\ln a
======================

4.30685+\frac12\ln a.
]

Rounded:

[
\boxed{
\alpha(a)\approx4.31+\frac12\ln a
}
]

with (a=|y_*|).

---

## Check against the three Γ-selected boundary points

### ζ

For ζ,

[
y_*=-0.16,\qquad a=0.16.
]

Then

[
\alpha_\zeta
\approx
4.30685+\frac12\ln(0.16).
]

Since

[
\ln(0.16)=-1.83258,
]

we get

[
\alpha_\zeta
\approx
4.30685-0.91629
===============

3.39056.
]

That matches the observed ζ exponent around (3.41), drifting toward (3.48) depending on truncation/window.

### Odd real primitive character

For the odd character case,

[
y_*=-\frac49,\qquad a=\frac49.
]

Then

[
\ln(4/9)=-0.81093,
]

so

[
\alpha_{\mathrm{odd}}
\approx
4.30685-0.40547
===============

3.90138.
]

That matches the observed (3.90).

### Even real primitive character

For the even character case,

[
y_*=-4,\qquad a=4.
]

Then

[
\ln4=1.38629,
]

so

[
\alpha_{\mathrm{even}}
\approx
4.30685+0.69315
===============

5.00000.
]

That matches the observed (5.05) to the expected finite-window accuracy.

So the law is not a mysterious fitted parity constant. It is:

[
\boxed{
\text{reciprocal-square base }4
+
\text{hard-edge spacing correction }
\frac{4(1-\ln2)}{\bar L_d}
+
\text{exterior boundary normalization }
\frac{2\ln|y_*|}{\bar L_d}.
}
]

With (\bar L_d\approx4), this becomes

[
\boxed{
4.31+\frac12\ln|y_*|.
}
]

---

## Interpretation

The first term (4) is the reciprocal-square weight:

[
x_j=\gamma_j^{-2}
\quad\Rightarrow\quad
x_j^2=\gamma_j^{-4}.
]

The (4(1-\ln2)) term is the hard-edge spacing/Vandermonde correction:

[
2\int_0^1\log(1-t^2),dt
=======================

-4(1-\ln2).
]

The (\ln|y_*|) term is the exterior Christoffel normalization:

[
p(-a)=1
\quad\Rightarrow\quad
\prod_{j=1}^d(a+x_j)^{-2}
\sim
a^{-2d}.
]

Changing parity changes the Γ-selected first trivial-zero image (y_*), hence changes only that exterior normalization. This is why comp55’s ζ / odd / even exponents differ while the hard-edge density class is the same. The bridge files already note that the Γ-factor selects the boundary/protector point and that the margin is an inverse exterior Christoffel function at that point.

---

## Important caveat

The formula

[
\alpha(a)\approx4.31+\frac12\ln a
]

is an **effective finite-degree law**, not the literal (d\to\infty) asymptotic in the normalization

[
\lambda_d(a)\sim \prod_{j\le d}\gamma_j^{-\alpha}.
]

The more honest formula is

[
\alpha_d(a)
\approx
4+
\frac{4(1-\ln2)+2\ln a}{\bar L_d},
\qquad
\bar L_d=\frac1d\sum_{j\le d}\ln\gamma_j.
]

Since (\bar L_d) grows slowly with (d), the (y_*)-dependent slope

[
\frac{2}{\bar L_d}
]

will slowly drift downward at astronomically large degrees. In the current computational range, (\bar L_d\approx4), so the observed slope is very close to (1/2).

So the derived result is:

[
\boxed{
\alpha_d(y_*)
=============

4+
\frac{4(1-\ln2)+2\ln|y_*|}{\bar L_d}
+
\text{slow log-density corrections}.
}
]

And the empirical shorthand is:

[
\boxed{
\alpha(y_*)\approx4.31+\frac12\ln|y_*|.
}
]

That is exactly the parity exponent coming from the exterior Christoffel asymptotics.
