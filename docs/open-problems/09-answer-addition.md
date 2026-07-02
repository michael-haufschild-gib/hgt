I read the file. The requested statement is the “cofinal one-sidedness” assertion: for each real (c\in[-2,1/4]) and every (\varepsilon>0), find (0<\rho<\varepsilon) such that (B(\beta,\rho)\setminus K_c) is connected. The file explicitly asks for a proof or refutation, while noting that only (c=0) and (c=-2) are already trivial and that the nontrivial fractal cases are the issue.

I cannot honestly certify a full proof for all real (c\in[-2,1/4]). What I can write down rigorously is the complete proof of the two certified cases, and a clean reduction that identifies the exact missing lemma for the fractal cases.

## Theorem 1 — certified full proof for (c=0) and (c=-2)

### Case (c=0)

Here
[
f_0(z)=z^2,\qquad K_0=\overline{\mathbb D},\qquad \beta=1.
]
For any (\rho>0),
[
B(1,\rho)\setminus K_0
======================

{z:|z-1|<\rho,\ |z|>1}.
]
This is the part of the open disk (B(1,\rho)) lying outside the closed unit disk.

If (0<\rho\le 2), the two circles (|z-1|=\rho) and (|z|=1) meet in at most two points, and the set above is a single open circular lune. Hence it is connected.

If (\rho>2), then (\overline{\mathbb D}\subset B(1,\rho)), so
[
B(1,\rho)\setminus \overline{\mathbb D}
]
is an annular disk region, again connected.

Thus (B(1,\rho)\setminus K_0) is connected for every (\rho>0). Therefore for every (\varepsilon>0), any (0<\rho<\varepsilon) works.

### Case (c=-2)

Here
[
f_{-2}(z)=z^2-2,\qquad K_{-2}=[-2,2],\qquad \beta=2.
]
For any (\rho>0),
[
B(2,\rho)\setminus K_{-2}
=========================

B(2,\rho)\setminus[-2,2].
]
Translate by (w=z-2). Then the set becomes
[
B(0,\rho)\setminus[-4,0].
]
Inside (B(0,\rho)), the removed set is either the radial slit ([-\rho,0]) if (0<\rho\le4), or the compact slit ([-4,0]) if (\rho>4).

In either case, the complement is path connected. Indeed, take any point
[
w=re^{i\theta}\in B(0,\rho)\setminus[-4,0].
]
If (w) is not on the positive real axis, move along the circle (|\zeta|=r) from angle (\theta) to angle (0), choosing the shorter circular arc that avoids the negative real axis. This stays in the punctured disk and avoids the slit. Then move radially along the positive real axis to any chosen point (s>0) with (s<\rho). Thus every point can be joined to the positive real gate ((0,\rho)), so the complement is path connected.

Therefore (B(2,\rho)\setminus[-2,2]) is connected for every (\rho>0). Again, for every (\varepsilon>0), any (0<\rho<\varepsilon) works.

So the requested cofinal statement is fully proved for
[
c\in{-2,0}.
]

## A rigorous reduction for all real (c<1/4)

Let
[
U_c:=\mathbb C\setminus K_c.
]
Because (K_c) is compact, full, and connected for (c\in[-2,1/4]), (U_c) is simply connected. For real quadratic maps in this parameter interval, the Julia set is locally connected by the Levin–van Strien theorem for real even unicritical polynomials; the cited theorem says that for (z^2+c), the Julia set is locally connected for (c\in[-2,1/4]). ([arXiv][1])

Let
[
\Phi_c:U_c\to{|\zeta|>1}
]
be the Böttcher coordinate normalized at infinity, and let
[
\Psi_c:=\Phi_c^{-1}.
]
By Carathéodory–Torhorst boundary theory, local connectivity of (J_c) gives a continuous extension of (\Psi_c) to the unit circle; the general theorem states that a conformal isomorphism of a simply connected domain extends continuously to the boundary exactly in the locally connected boundary setting. ([Wikipedia][2])

Define the landing map
[
\gamma_c:\mathbb R/\mathbb Z\to J_c,\qquad
\gamma_c(t)=\Psi_c(e^{2\pi i t}).
]
The file gives the needed access fact at (\beta): the external ray of angle (0) lands at (\beta), and no other ray lands there.  Hence
[
\gamma_c^{-1}(\beta)={0}.
]

For (\rho>0), set
[
E_\rho
:=
{t\in\mathbb R/\mathbb Z:\ |\gamma_c(t)-\beta|<\rho}.
]

### Lemma

If (E_\rho) is connected, then
[
B(\beta,\rho)\setminus K_c
]
is connected.

### Proof of the lemma

Let
[
\Omega_\rho
:=
\Psi_c^{-1}\bigl(B(\beta,\rho)\setminus K_c\bigr)
=================================================

{\zeta:|\zeta|>1,\ |\Psi_c(\zeta)-\beta|<\rho}.
]
Since (\Psi_c) is a homeomorphism from ({|\zeta|>1}) onto (U_c), it is enough to prove (\Omega_\rho) is connected.

Consider the harmonic function
[
u(\zeta):=\log|\Psi_c(\zeta)-\beta|
]
on ({|\zeta|>1}). It is harmonic because (\Psi_c(\zeta)\ne\beta) for (|\zeta|>1); (\beta) lies on the boundary (J_c), not in (U_c).

Suppose (C) is a connected component of (\Omega_\rho). If (\overline C) were compactly contained in ({|\zeta|>1}), then (u<\log\rho) on (C), while (u=\log\rho) on (\partial C). Then (\log\rho-u) would be a positive harmonic function on (C) with zero boundary values, contradicting the maximum principle. Therefore every component (C) of (\Omega_\rho) must accumulate on the unit circle.

Now (\Psi_c) extends continuously to (|\zeta|=1). Thus if
[
|\Psi_c(e^{2\pi i t})-\beta|<\rho,
]
then a one-sided collar neighborhood of (e^{2\pi i t}) in ({|\zeta|>1}) lies in (\Omega_\rho). Consequently the boundary traces of the connected components of (\Omega_\rho) form a disjoint relatively open-and-closed partition of (E_\rho).

If (E_\rho) is connected, this partition has only one member. Therefore (\Omega_\rho) has only one component, and hence
[
B(\beta,\rho)\setminus K_c
]
is connected. ∎

## What remains unproved

The lemma shows that the original problem would follow from the following one-dimensional “angle-clean-level” assertion:

> For every (\varepsilon>0), there exists (0<\rho<\varepsilon) such that
> [
> E_\rho={t:|\gamma_c(t)-\beta|<\rho}
> ]
> is connected.

That assertion is exactly where the nontrivial fractal geometry sits. It is not a consequence merely of single access at (\beta); the file itself warns that access counting and ball-connectivity are different notions.  It is also precisely what the numerical “dirty scale / clean band” discussion is probing.

So the fully rigorous status I can certify is:

[
\boxed{\text{The problem is completely proved for }c=-2\text{ and }c=0.}
]

For the remaining real fractal parameters, the proof reduces to finding cofinally many connected sublevel sets of the external-angle landing-distance function (t\mapsto|\gamma_c(t)-\beta|). I do not have a valid all-parameter proof of that final assertion.

[1]: https://arxiv.org/abs/math/9504227 "https://arxiv.org/abs/math/9504227"
[2]: https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_theorem_%28conformal_mapping%29 "https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_theorem_%28conformal_mapping%29"
