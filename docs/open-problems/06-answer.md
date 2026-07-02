I prove a slightly stronger statement: **under the stated hypotheses, no exceptional pairs occur, and in fact either index can be used.** That is, for each (i\neq j) there is a one-sided point
[
x\in J_{c_i}\setminus K_{c_j}
\quad\text{with}\quad
x\in \partial W .
]
This is stronger than the requested “possibly after exchanging the indices” conclusion. The requested target is exactly the point described in the file: (x\in J_{c_1}), (x\notin K_{c_2}), and (x\in\partial W).

## Standard theorem used

I use the following classical form of the Fatou–Lindelöf–Zdunik/Zakeri biaccessibility theorem.

**Theorem.** Let (c\in M\setminus{-2}), and let (\mu_c) be the equilibrium, equivalently harmonic, measure of (K_c) seen from infinity. Then the set of one-sided points of (J_c) has full (\mu_c)-measure.

Here “one-sided” is in the local sense of the problem: for all sufficiently small (\rho>0),
[
B(p,\rho)\setminus K_c
]
is connected. The Chebyshev case (c=-2), where (K_c=[-2,2]), is exactly the excluded case in which typical points have two exterior sides. The disk case (c=0) is harmless for this theorem, but it is also excluded in the problem statement.

A standard proof is: Fatou’s theorem gives radial landing of external rays for harmonic-measure-a.e. boundary point; the Lindelöf access theorem identifies distinct local accesses with distinct landing external rays; and Zdunik’s theorem says that, for a polynomial with connected Julia set, the set of biaccessible boundary points has harmonic measure zero unless the polynomial is Chebyshev. For (z^2+c), the Chebyshev parameter is (c=-2).

The problem statement permits standard results from polynomial dynamics, plane topology, and potential theory to be used.

---

## Proof

Write
[
K_i=K_{c_i},\qquad J_i=J_{c_i},\qquad G_i=G_{c_i},\qquad \mu_i=\mu_{c_i}
]
for (i=1,2). Each (K_i) is compact, full, connected, has logarithmic capacity (1), and has continuous Green function (G_i) vanishing exactly on (K_i).  Also (K_1\neq K_2), because distinct parameters have distinct filled Julia sets.

Let
[
X=K_1\cup K_2,
]
and let (W) be the unbounded component of (\mathbb C\setminus X), as in the statement.  Put
[
Y=\mathbb C\setminus W.
]
Thus (Y) is the filled-in hull of (X): it is (X) together with all holes of (X). Its outer boundary is (\partial W).

### 1. The outer hull has capacity strictly larger than (1)

First observe that neither (K_1\subset K_2) nor (K_2\subset K_1) can hold. Indeed, suppose for example that (K_2\subsetneq K_1). Choose (a\in K_1\setminus K_2). Since (K_2) is closed, there is a small disk (D) about (a) with (\overline D\cap K_2=\varnothing). The set (K_1\cap \overline D) has positive logarithmic capacity: if (a\in \operatorname{int}K_1), this is immediate from the presence of a small disk; if (a\in J_1), it follows because (\mu_1) has full support on (J_1).

Now use a standard strict monotonicity argument for logarithmic capacity. Let (E) be a compact set of capacity (1), let (A\subset \mathbb C\setminus E) be compact of positive capacity, and assume (G_E>0) on (A). Let (\mu_E) be the equilibrium measure of (E), and choose a probability measure (\sigma) of finite logarithmic energy supported on (A). With the convention
[
I(\nu)=\iint \log \frac1{|z-w|},d\nu(z)d\nu(w),
]
we have (I(\mu_E)=0), because (\operatorname{cap}(E)=1), and
[
I(\mu_E,\sigma)=\int U^{\mu_E},d\sigma
======================================

-\int G_E,d\sigma
<0 .
]
Therefore, for small (t>0),
[
I\bigl((1-t)\mu_E+t\sigma\bigr)
===============================

(1-t)^2 I(\mu_E)
+2t(1-t)I(\mu_E,\sigma)
+t^2I(\sigma)
<0.
]
Hence the Robin constant of (E\cup A) is negative, so
[
\operatorname{cap}(E\cup A)>1.
]

Applying this with (E=K_2) and (A\subset K_1\setminus K_2) gives
[
\operatorname{cap}(K_1)>1,
]
contradicting (\operatorname{cap}(K_1)=1). Thus (K_2\not\subset K_1), and symmetrically (K_1\not\subset K_2).

In particular, (K_2\setminus K_1) contains a compact subset of positive capacity lying in (\mathbb C\setminus K_1). Applying the same strict monotonicity argument with (E=K_1) gives
[
\operatorname{cap}(K_1\cup K_2)>1.
]
Since (Y\supset K_1\cup K_2), monotonicity of capacity gives
[
R:=\operatorname{cap}(Y)>1.
]

### 2. The exposed part of each Julia set has positive harmonic measure

Let (\mu_Y) be the equilibrium measure of (Y). Since (Y) is the filled hull of (X), (\mu_Y) is the harmonic measure of (W) seen from infinity, and it is supported on (\partial W).

For (i=1,2), the standard energy identity gives
[
\int G_i,d\mu_Y=\log \operatorname{cap}(Y)=\log R.
]
Indeed, since (\operatorname{cap}(K_i)=1), the Green function satisfies
[
G_i=-U^{\mu_i},
]
where (\mu_i) is the equilibrium measure of (K_i). By Fubini,
[
\int G_i,d\mu_Y
===============

# -\iint \log\frac1{|z-w|},d\mu_i(w)d\mu_Y(z)

-\int U^{\mu_Y}(w),d\mu_i(w).
]
Because (\mu_i) is supported on (K_i\subset Y), and (U^{\mu_Y}=-\log R) quasi-everywhere on (Y), this equals (\log R).

Now take (i=2). Since (R>1),
[
\int G_2,d\mu_Y=\log R>0.
]
But (G_2=0) exactly on (K_2), while (G_2>0) on (\mathbb C\setminus K_2). Also (\mu_Y) is supported on (\partial W\subset K_1\cup K_2). Hence
[
\mu_Y(\partial W\setminus K_2)>0.
]
Set
[
E_1:=\partial W\setminus K_2.
]
Then (E_1\subset K_1). Moreover (E_1\subset J_1), because no point of (\operatorname{int}K_1) can lie on (\partial W). Thus
[
E_1\subset J_1\setminus K_2
]
and
[
\mu_Y(E_1)>0.
]

Now compare harmonic measures in the nested domains
[
W\subset \Omega_1:=\mathbb C\setminus K_1.
]
The set (E_1) is a common boundary portion of (W) and (\Omega_1). By domain monotonicity of harmonic measure,
[
\omega_W(\infty,E_1)\le \omega_{\Omega_1}(\infty,E_1).
]
But
[
\omega_W(\infty,\cdot)=\mu_Y,
\qquad
\omega_{\Omega_1}(\infty,\cdot)=\mu_1.
]
Therefore
[
\mu_1(E_1)\ge \mu_Y(E_1)>0.
]

So the exposed set
[
E_1=\partial W\setminus K_2\subset J_1\setminus K_2
]
has positive equilibrium measure for (K_1).

### 3. Choose a one-sided point in the exposed set

By the one-sided full-measure theorem quoted above,
[
\mu_1({\text{one-sided points of }J_1})=1.
]
Since (\mu_1(E_1)>0), the intersection
[
E_1\cap {\text{one-sided points of }J_1}
]
is nonempty.

Choose
[
x\in E_1
]
that is one-sided for (K_1). Then, by definition of (E_1),
[
x\in \partial W,
\qquad
x\notin K_2,
\qquad
x\in J_1.
]
Thus (x) is exactly the desired one-sided boundary point visible from infinity.

The same argument with the indices reversed gives a one-sided point of (J_2\setminus K_1) on (\partial W). Hence no exceptional pairs occur under the stated assumptions (c_1\neq c_2\in M\setminus{0,-2}).
