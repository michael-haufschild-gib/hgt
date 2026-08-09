# Source–norm–support forgetful tower law

- **ID:** `source-norm-support-forgetful-tower-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [BRIDGE] [FORMALIZED IN LEAN]`
- **Role:** exact explanation of why arithmetic orientation, positive geometry, and exact topology
  repeatedly detect same RH wall without jointly selecting it.
- **Novelty:** elementary matrix theorem plus existing corpus residue formula; no independent
  novelty claim.

## Goal

Determine whether exactness, positivity, and arithmetic residue are independent constraints. In
the literal two-leg carrier they are successive lossy images of one framed scalar.

## Theorem

Let

\[
 \tau=\begin{pmatrix}0&1\\1&0\end{pmatrix},
 \qquad
 T_\delta=\begin{pmatrix}0&1\\\delta&0\end{pmatrix},
 \qquad
 L_c=cI,
 \quad c\ne0.
 \tag{1}
\]

Put

\[
 D=T_\delta L_c-L_c\tau,
 \qquad
 a=c(\delta-1).
 \tag{2}
\]

Then

\[
 D=aE_{21},
 \qquad
 T_\delta D=aE_{11}.
 \tag{3}
\]

Define

\[
 \Gamma:\mathbb C^2\oplus\mathbb C^2\to\mathbb C^2,
 \qquad
 \Gamma(x,y)=Dx+T_\delta Dy.
 \tag{4}
\]

Then

\[
 \boxed{\Gamma\Gamma^*=|a|^2I_2.}
 \tag{5}
\]

Consequently

\[
 \operatorname{ran}\Gamma=
 \begin{cases}
 0,&a=0,\\
 \mathbb C^2,&a\ne0,
 \end{cases}
 \tag{6}
\]

and for \(a\ne0\),

\[
 \|\Gamma^\dagger\|=|a|^{-1},
 \qquad
 \det(\Gamma\Gamma^*)=|a|^4.
 \tag{7}
\]

### Proof

Direct multiplication gives `(3)`. For
`x=(x_1,x_2)` and `y=(y_1,y_2)`,

\[
 \Gamma(x,y)=a(y_1e_1+x_1e_2).
 \tag{8}
\]

The two nonzero rows are orthogonal and both have norm `|a|`, proving `(5)`. Equation `(6)`, the
pseudoinverse norm, and determinant follow immediately. QED.

## Arithmetic instantiation

The publication-ready cyclic-to-paracyclic source theorem gives, on a trace-one prime cycle,

\[
 a_\rho
 =(\delta_n(\rho)-1)c_\rho
 =\operatorname{Res}(D_{n,\rho}x_0),
 \qquad
 \delta_n(\rho)=e^{(2\Re\rho-1)\log n}.
 \tag{9}
\]

Substitution into `(5)` gives

\[
 \Gamma_\rho\Gamma_\rho^*
 =|\operatorname{Res}(D_{n,\rho}x_0)|^2I,
 \qquad
 \det(\Gamma_\rho\Gamma_\rho^*)
 =|\operatorname{Res}(D_{n,\rho}x_0)|^4.
 \tag{10}
\]

Near critical wall, with

\[
 \kappa=(2\Re\rho-1)\log n,
 \tag{11}
\]

one has

\[
 \|\Gamma_\rho^\dagger\|
 \sim {1\over|c_\rho|\,|\kappa|}.
 \tag{12}
\]

Thus exact wall is also singular-conditioning wall.

## Three-shadow theorem

The maps

\[
 a\longmapsto |a|^2\longmapsto [a=0]
 \tag{13}
\]

have precise information loss:

1. framed arithmetic source retains phase and coorientation of `a`;
2. positive Hilbert geometry retains magnitude but loses phase/coorientation;
3. exact/topological support retains only zero versus nonzero and loses magnitude.

Therefore the three route outputs are not independent constraints. They are successive forgetful
shadows of one source section:

```text
arithmetic/source a
    -> spectral/Hilbert |a|^2
    -> exact/topological [a=0].
```

Taking their product cannot create selection: every component is already a function of `a`.
Positive energy detects displacement from wall but cannot orient or annihilate it. Exactness
detects wall support but supplies no dynamics forcing source section to land there.

## Central-twist isotriviality corollary

Suppose every block transport `T_i` is multiplied by same nonzero scalar `delta`. Every relative
channel is unchanged:

\[
 (\delta T_j)f(\delta T_i)^{-1}=T_jfT_i^{-1}.
 \tag{14}
\]

Hence any invariant built only from relative channels is constant under central scalar twist,
while determinant holonomy changes. Exact-category data alone cannot select `delta=1`; adjoining
the framed central line returns to source scalar `a`.

## No-go closure

- **Exact killing mechanism:** norm and support factor through framed source scalar and erase
  orientation/magnitude respectively.
- **Strongest positive survivor:** exact Gram identity, support classification, and inverse
  conditioning asymptotic.
- **New insight:** corpus “uncertainty” is not a Heisenberg inequality. It is a non-conservative
  forgetful tower between source, norm, and support.
- **Status:** dependency-closed paper proof and literal arithmetic bridge; does not prove source
  residue vanishes.

## Lean-return note

No Lean work is authorized. If later requested, formalize matrix identity independently of
arithmetic residue instantiation.

## Log

- 2026-08-08 — extracted from hostile exactness/admissibility audit.

## Formalized companion

`source-norm-support-forgetful-tower-law-formalized.md` (same directory).
