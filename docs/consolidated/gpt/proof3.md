The short answer is:

[
\boxed{
\text{we can define the correct residual, but proving }R_d\succeq0
\text{ is exactly the remaining RH bridge theorem.}
}
]

The pole computation gives a **clean reduction**, not the final proof.

The exact state is:

[
H_d^0=H_d^A+H_d^P,
]

[
H_d^A=R_d^A-2u_du_d^{\mathsf T},
]

[
H_d^P=2u_du_d^{\mathsf T}+R_d^P,
]

so

[
\boxed{
H_d^0=R_d^A+R_d^P.
}
]

Thus the natural residual is

[
\boxed{
R_d:=R_d^A+R_d^P=H_d^0.
}
]

There is no remaining pole-rank-one piece inside (H_d^0); the archimedean pole defect and the prime pole component cancel exactly. This is the quadratic-form version of the seam cancellation already identified in the weld/superzeta/phase-defect note.

So if by

[
R_d=H_d^0-\text{pole-residue contribution}
]

you mean “remove the cancelled (s=1) pole pair,” then

[
\text{pole-residue contribution}=0
]

in the completed form, and

[
R_d=H_d^0.
]

Therefore

[
\boxed{
R_d\succeq0
}
]

is exactly

[
\boxed{
H_d^0=[T_{i+j+1}]_{i,j=0}^d\succeq0,
}
]

which is the source-aware (Q_0) wall.

That is RH-equivalent in the reciprocal seam chart. The one-wall note identifies this reciprocal seam-squared moment problem as the clean global RH coordinate: the zero divisor is mapped to (y_\rho=-(\rho-\tfrac12)^{-2}), and RH is the positivity/Stieltjes condition for the resulting zero-divisor moment sequence.

---

## What we have proved

We have proved the **pole part**.

Let

[
u_d=(1,-4,(-4)^2,\dots,(-4)^d)^{\mathsf T}.
]

The archimedean form splits as

[
\boxed{
H_d^A=R_d^A-2u_du_d^{\mathsf T},
\qquad
R_d^A\succeq0.
}
]

The prime pole at (s=1) contributes

[
\boxed{
H_{d,\mathrm{pole}}^P=+2u_du_d^{\mathsf T}.
}
]

Hence

[
\boxed{
-2u_du_d^{\mathsf T}+2u_du_d^{\mathsf T}=0.
}
]

So the (s=1) pole cancellation is exact at the (Q_0)-form level.

This proves:

[
\boxed{
\text{the unique negative archimedean pole direction is cancelled by the prime pole.}
}
]

That is a real structural theorem.

---

## What remains unproved

What remains is

[
\boxed{
R_d^A+R_d^P\succeq0
\quad\forall d.
}
]

Equivalently,

[
\boxed{
Q_0[p]\ge0
\quad\forall p\in\mathbb R[y].
}
]

This is not a formal consequence of pole cancellation.

A finite-dimensional toy model shows why. Suppose

[
H^A=I-2uu^{\mathsf T},
\qquad
H^P=2uu^{\mathsf T}-3I.
]

The pole terms cancel, but

[
H^A+H^P=-2I
]

is negative. So

[
\boxed{
\text{rank-one pole cancellation does not imply residual positivity.}
}
]

This matches the earlier guardrail: cancellation/finiteness is not positivity. The proof must show a **positive residual transfer**, not merely cancellation.

---

## The correct residual theorem

The theorem we still need is therefore:

[
\boxed{
\textbf{Residual Explicit-Formula Positivity Theorem.}
}
]

For every (d\ge0),

[
\boxed{
R_d^A+R_d^P\succeq0.
}
]

Equivalently, for every real polynomial

[
p(y)=\sum_{i=0}^d c_i y^i,
]

prove

[
\boxed{
Q_0[p]
======

\sum_{i,j=0}^d c_i c_j T_{i+j+1}
\ge0.
}
]

Using the fused seam formula, this is

[
\boxed{
\sum_{i,j=0}^{d}
c_i c_j
(-1)^{i+j+1}
S_{i+j+1}
\ge0,
}
]

where

[
S_k
===

2^{2k}
-\frac14(2^{2k}-1)\zeta(2k)
-2^{2k-2}\beta(2k)
-\frac{1}{2(2k-1)!}
\left(\frac{\zeta'}{\zeta}\right)^{(2k-1)}!\left(\frac12\right).
]

That is the formula-level bridge theorem.

It says:

[
\boxed{
\text{the residue left after the archimedean-prime pole cancellation is positive on every reciprocal-seam square test.}
}
]

---

## Better formulation: quotient out the pole direction

If you want a true “residual after removing the pole direction,” do not subtract a Euclidean rank-one projection arbitrarily. That can destroy positivity even if (H_d^0) is PSD.

The correct coordinate is the **Schur complement** with respect to the pole direction.

Let (u=u_d), and choose a basis (B) for (u^\perp). In block form,

[
H_d^0
=====

\begin{pmatrix}
a & b^{\mathsf T}\
b & C
\end{pmatrix},
]

where

[
a=\frac{u^{\mathsf T}H_d^0u}{u^{\mathsf T}u}.
]

Then, if (a>0),

[
H_d^0\succeq0
]

is equivalent to

[
\boxed{
C-\frac{bb^{\mathsf T}}{a}\succeq0.
}
]

So the mathematically correct “pole-eliminated residual” is

[
\boxed{
\operatorname{Schur}_u(H_d^0)
=============================

C-\frac{bb^{\mathsf T}}{a}.
}
]

But proving

[
\operatorname{Schur}_u(H_d^0)\succeq0
]

for all (d) is still equivalent to the remaining (Q_0) positivity, not an automatic consequence of the pole cancellation.

Your computation already points in this direction: restricting away from (u) improves conditioning only by a fixed factor, and the residual remains the hard generic hard-edge problem. That means the (u)-direction is **only Part A**, not the proof.

---

## What this means conceptually

The proof anatomy is now:

[
\boxed{
\textbf{Part A: pole cancellation.}
}
]

This is proved:

[
H_d^A=R_d^A-2u u^{\mathsf T},
\qquad
H_{d,\mathrm{pole}}^P=+2u u^{\mathsf T}.
]

[
\boxed{
\textbf{Part B: residual positivity.}
}
]

This is open:

[
R_d^A+R_d^P\succeq0.
]

Part A is entireness. Part B is RH.

That is the cleanest current statement.

---

## What a proof of (R_d\succeq0) would need to look like

It cannot be:

[
\text{“the pole cancels, so positivity remains.”}
]

It must produce one of the following.

### 1. A square identity

Something like

[
R_d[p]
======

\int |\mathcal K_p(x)|^2,d\mu(x)
\ge0.
]

### 2. A positive transfer theorem

Something like

[
\text{integer/prime-side positive object}
\longrightarrow
\text{zero-side }Q_0\text{ positivity}.
]

But not merely FID positivity, because FID positivity lives on the integer divisor and is RH-empty.

### 3. A Weil-form pullback

A construction of a test function (h_p) such that

[
Q_0[p]=Q_W[h_p],
]

and the completed explicit formula proves

[
Q_W[h_p]\ge0
]

for this whole family.

### 4. A source-built index theorem

An operator/form (Q_\xi), with the completed boundary extension specified, such that

[
\operatorname{neg}(Q_\xi)=#{\text{off-line zero pairs}},
]

and then a proof

[
Q_\xi\succeq0.
]

---

## Bottom line

You can define

[
R_d:=H_d^0-\text{pole contribution},
]

but because the pole contribution cancels exactly in (H_d^0), this is just

[
\boxed{
R_d=H_d^0.
}
]

Therefore

[
\boxed{
R_d\succeq0
}
]

is not a new reduced theorem. It is the (Q_0) RH wall itself.

The reduction we have achieved is:

[
\boxed{
\text{the only negative archimedean direction is the (s=1) pole direction, and the prime pole cancels it exactly.}
}
]

The missing proof is:

[
\boxed{
\text{the residual completed explicit-formula form is positive.}
}
]

That is exactly the bridge theorem we still need.
