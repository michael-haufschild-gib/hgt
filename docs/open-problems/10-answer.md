I read the uploaded problem. The full file asks for (\mu(Q(K))=1) for quasidisks, where (Q(K)) is the set of boundary points (p) for which arbitrarily small radii (\rho) make (B(p,\rho)\setminus K) connected.

I can give a complete rigorous proof for the **rectifiable quasidisk subcase**, i.e. when the quasicircle (J=\partial K) has finite length. This proves the stated conclusion for every rectifiable quasidisk, hence in particular for chord-arc quasidisks. I am not claiming this settles the nonrectifiable quasidisk or main-cardioid Julia-set case.

---

# Theorem

Let (J\subset \mathbb C) be a quasicircle, let (K) be its closed Jordan interior, and let
[
\Omega=\widehat{\mathbb C}\setminus K.
]
Assume additionally that
[
\mathcal H^1(J)<\infty .
]
Let (\mu) be harmonic measure of (\Omega) evaluated at (\infty), as in the uploaded setting.

Then
[
\mu(Q(K))=1.
]

Equivalently, for (\mu)-almost every (p\in J), for every (\varepsilon>0) there exists (0<\rho<\varepsilon) such that
[
B(p,\rho)\setminus K
]
is connected.

---

# Proof

Because (J) is a rectifiable Jordan curve, the F. and M. Riesz theorem applies to the simply connected Jordan domain obtained from (\Omega) by a Möbius inversion sending (\infty) to a finite pole. Therefore harmonic measure and arclength measure on (J) are mutually absolutely continuous. In particular,
[
\mathcal H^1(E)=0
\quad\Longrightarrow\quad
\mu(E)=0
]
for Borel (E\subset J). This is the classical rectifiable-boundary harmonic-measure theorem allowed by the problem statement.  The same theorem is commonly stated as: for simply connected planar domains bounded by a rectifiable curve, harmonic measure is mutually absolutely continuous with respect to arclength. ([Wikipedia][1])

So it is enough to prove
[
\mathcal H^1(J\setminus Q(K))=0.
]

We prove this using only rectifiability, the Jordan property, and the coarea formula.

---

## Step 1: A topological counting lemma

Fix (p\in J). For (r>0), write
[
N_p(r):=#\bigl(J\cap \partial B(p,r)\bigr),
]
allowing (N_p(r)=\infty).

We claim:

> If (N_p(r)<4), then (B(p,r)\setminus K) is connected, except possibly for the negligible radii where (J) contains a nontrivial arc of (\partial B(p,r)).

Indeed, since (p\in J) and (p) is the center of the ball, the local Jordan arc through (p) must leave (B(p,r)) on both sides, provided (r) is sufficiently small and (J) does not lie in the circle (\partial B(p,r)). Thus (J\cap \partial B(p,r)) has at least two points.

If it has exactly two points, then (J\cap \overline{B(p,r)}) is a single crosscut of the disk (B(p,r)). By the Jordan crosscut theorem, that crosscut divides (B(p,r)) into exactly two pieces, one lying in (K) and one lying in (\Omega). Hence
[
B(p,r)\setminus K
=================

B(p,r)\cap \Omega
]
is connected.

This is precisely the structural fact recorded in the file: when (J) meets the boundary circle in exactly two points, the ball is cut into one (K)-side and one exterior side, so (B(p,r)\setminus K) is connected.

Therefore, for almost every radius (r),
[
B(p,r)\setminus K\text{ disconnected}
\quad\Longrightarrow\quad
N_p(r)\ge 4.
]

---

## Step 2: Coarea lower bound for persistently bad radii

Let (p\in J) be a point of arclength density one for the rectifiable curve (J). That means
[
\lim_{r\downarrow 0}
\frac{\mathcal H^1(J\cap B(p,r))}{2r}
=====================================

1.

]
This holds for (\mathcal H^1)-almost every (p\in J), by the standard density theorem for rectifiable sets.

Suppose, toward a contradiction, that (p\notin Q(K)). Then there exists (\varepsilon_0>0) such that for every (0<r<\varepsilon_0),
[
B(p,r)\setminus K
]
is disconnected.

Hence, by Step 1, for almost every (t\in(0,\varepsilon_0)),
[
N_p(t)\ge 4.
]

Now use the one-dimensional coarea formula for the Lipschitz function
[
z\mapsto |z-p|
]
restricted to the rectifiable curve (J). For (0<a<b<\varepsilon_0),
[
\int_a^b N_p(t),dt
\le
\mathcal H^1\bigl(J\cap (B(p,b)\setminus \overline{B(p,a)})\bigr).
]

Taking (a=r/2) and (b=r), and using (N_p(t)\ge 4) for almost every (t\in(r/2,r)), we get
[
\mathcal H^1\bigl(J\cap (B(p,r)\setminus \overline{B(p,r/2)})\bigr)
\ge
\int_{r/2}^{r}4,dt
==================

2r.
]

So persistent badness forces
[
\mathcal H^1\bigl(J\cap (B(p,r)\setminus \overline{B(p,r/2)})\bigr)
\ge 2r
]
for all sufficiently small (r).

---

## Step 3: Contradiction with arclength density

But at an arclength-density-one point (p),
[
\mathcal H^1(J\cap B(p,r))
==========================

2r+o(r)
]
and
[
\mathcal H^1(J\cap B(p,r/2))
============================

r+o(r).
]

Therefore
[
\mathcal H^1\bigl(J\cap (B(p,r)\setminus \overline{B(p,r/2)})\bigr)
===================================================================

r+o(r).
]

For all sufficiently small (r), this is strictly less than (2r), contradicting the lower bound from Step 2.

Thus no arclength-density-one point can lie outside (Q(K)). Since arclength-density-one points have full (\mathcal H^1)-measure on a rectifiable curve,
[
\mathcal H^1(J\setminus Q(K))=0.
]

Finally, because harmonic measure (\mu) is absolutely continuous with respect to (\mathcal H^1|_J) in the rectifiable Jordan-curve case,
[
\mu(J\setminus Q(K))=0.
]

Hence
[
\boxed{\mu(Q(K))=1.}
]

This proves the desired cofinal one-sidedness statement for every rectifiable quasidisk.

[1]: https://en.wikipedia.org/wiki/Harmonic_measure?utm_source=chatgpt.com "Harmonic measure"
