# Theta-cusp atom–likelihood cross domination

## Status

- Pipeline stage: formalized
- Lean status: complete; direct Lean check passed
- Scope: unconditional same-half-line completed-source theorem; no RH claim

## Inputs already in the corpus

- exact first-atom reflected jet and Riccati normal forms;
- strict positivity of the atom Riccati margin;
- the raw higher-likelihood bound
  \(\mathrm{HigherJet}_2(x)<13/10\) for \(x>0\);
- exact logarithmic likelihood jets;
- support-gap theorem proving \(g_2>0\), likelihood reflected Riccati positivity, and negativity of
  the atom–likelihood mixed channel.

No atom or tail estimate below is re-derived when an existing theorem supplies it.

## 1. Closed-half-line likelihood curvature bound

For \(x>0\), the exact connector to the existing higher-likelihood log jet gives

\[
0<g_2(x)\le \mathrm{HigherJet}_2(x)<\frac{13}{10}.
\]

The cumulant formula makes \(g_2\) continuously differentiable at \(x=0\). Passing to the
right-hand limit yields

\[
0<g_2(x)\le\frac{13}{10}\qquad(x\ge0).
\]

For the reflected likelihood action \(q\), this implies

\[
-q''(t)=g_2(u+t)+g_2(u-t)\le\frac{13}{5}
\]

whenever \(0\le t\le u\). Since \(q'(0)=0\), the mean-value bound gives

\[
-q'(t)\le\frac{13}{5}t
\le\frac{13}{20}z',
\qquad z'=2\sinh(2t),
\]

using \(2t\le\sinh(2t)\).

## 2. Uniform half-factor law

Put

\[
A=\pi e^{2u},\quad z=\cosh(2t)-1,\quad
\lambda=\frac{3A}{(A-\frac32)^2},\quad r=1-\lambda z.
\]

For \(0\le t\le u\), set \(Y=e^{2u}\ge1\). Monotonicity of \(\cosh\) gives

\[
z\le\cosh(2u)-1=\frac{(Y-1)^2}{2Y}.
\]

Moreover

\[
\begin{aligned}
(A-\tfrac32)^2-6Az
&\ge(\pi Y-\tfrac32)^2-3\pi(Y-1)^2\\
&=\pi(\pi-3)Y^2+3\pi(Y-1)+\frac94>0.
\end{aligned}
\]

Thus \(\lambda z<1/2\), so

\[
r>\frac12.
\]

This strengthens the existing qualitative positivity of the reflected atom factor.

## 3. Pure atom domination inequality

Write

\[
w=\lambda/r,\qquad S=2A+w,\qquad
a_2=4w^2z(z+2)+4S(z+1),
\]

and let \(R\) be the existing reduced atom Riccati margin. The previous half-factor law and the
existing \(\lambda\le4\) imply

\[
0<w<8.
\]

Direct expansion gives

\[
4R-\frac{26}{5}S-\frac{13}{10}a_2=K w^2+H w+J,
\]

where

\[
\begin{aligned}
K&=(16A-\tfrac{26}{5})z(z+2)-4(z+1),\\
H&=(32A-\tfrac{26}{5})(z+1)-\tfrac{46}{5},\\
J&=A\big((32A-\tfrac{52}{5})(z+1)-\tfrac{92}{5}\big).
\end{aligned}
\]

For \(A>3\) and \(z\ge0\),

\[
K\ge-4,\qquad H>32,\qquad J>0.
\]

Since \(0<w<8\), \(w^2<8w\), hence

\[
Kw^2+Hw > -4w^2+32w>0.
\]

Therefore

\[
\frac{26}{5}S+\frac{13}{10}a_2<4R.
\]

## 4. Cross domination and completed Riccati positivity

The atom jets are \(a_1=Sz'\) and \(a_2\) as above. With \(q',q''<0\), the negative mixed
channel is

\[
-X=2\big(a_1(-q'')+(-q')a_2\big).
\]

The likelihood bounds and pure atom inequality give, for \(0<t\le u\),

\[
\begin{aligned}
-X
&\le z'\left(\frac{26}{5}S+\frac{13}{10}a_2\right)\\
&<4z'R
=R_{\mathrm{atom}}.
\end{aligned}
\]

The likelihood margin is independently positive, so

\[
R_{\mathrm{completed}}
=R_{\mathrm{atom}}+R_{\mathrm{likelihood}}+X>0.
\]

At \(t=0\), every reflected jet needed by the margin vanishes appropriately and the completed
margin is zero. Therefore the completed margin is nonnegative on each closed same-half-line packet,
which unconditionally proves correlation-angle subadditivity there.

## Hostile checks

- No numerical evaluation is used.
- Tail estimate \(13/10\) is reused from the existing symbolic Gaussian majorant.
- Strict domination is proved by atom margin alone; likelihood margin positivity is extra slack.
- Seam-crossing packets are outside this theorem's scope; they are now closed by
  `ThetaCuspGlobalReflectedRiccati`.

## Formal target

Formalized in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAtomLikelihoodCrossDomination`, including the half-factor
law, atom algebra inequality, likelihood mean-value bounds, strict cross domination, completed
same-half-line Riccati margin, and unconditional same-half-line angle law.
