# Theta-cusp likelihood gap–cumulant–Riccati law

## Status

- Pipeline stage: formalized
- Lean status: direct `lake env lean` check passes
- Scope: unconditional theta-source theorem; no RH claim

## Corpus and literature audit

The corpus already proves the sharp support statement
`ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure` inside
`ThetaCuspCassiniMarkovBoundaryTransport.lean`, but had kept it private. It also already proves:

- all positive-temperature moments exist;
- strict positivity of the first moment and total variance;
- the exact modular seam calibration of the total tilted mean;
- exact first three source-coordinate cumulant jets;
- strict positivity of the single-atom reflected Riccati margin.

The 2026 Hedenmalm spectral paper supplies the theta source and its modular symmetry, but does not
state the tilted support-gap cumulant inequalities or the reflected likelihood Riccati theorem below.
Generic support and Cauchy–Schwarz moment estimates are standard; novelty claimed here is only their
theta-specific combination and the resulting exact obstruction decomposition.

## Setup

For positive likelihood coordinate \(B\), write

\[
 Z=1+M_0,\qquad p=M_0/Z,\qquad e_j=M_j/Z,\qquad m=e_1,
\]

where \(M_j\) is the \(j\)-th moment of the higher likelihood spectral measure tilted by
\(e^{-Br}\). The extra unit mass in \(Z\) is at spectral coordinate zero. Put

\[
 v=e_2-m^2,\qquad
 \kappa_3=e_3-3me_2+2m^3,
\]

and

\[
 \kappa_4=e_4-4me_3-3e_2^2+12m^2e_2-6m^4.
\]

## Paper proof

### 1. Sharp moment recurrence

The existing source decomposition has support in \([3,\infty)\). Hence, pointwise on its support,
\(3r^j\le r^{j+1}\). Multiplication by the positive tilt and integration gives

\[
 3M_j\le M_{j+1}\qquad(j\ge0).
\]

After division by \(Z>0\), \(3e_j\le e_{j+1}\).

### 2. Uniformly small total mean

The exact seam law and strict cooling give, for source coordinate \(x\ge0\),

\[
 2\pi m(x)\le s_0,\qquad
 s_0=\frac92-2\pi+\frac6{2\pi-3}.
\]

Since \(\pi>3\), the denominator \(2\pi-3>3\), so \(6/(2\pi-3)<2\), while
\(9/2-2\pi<-3/2\). Thus \(s_0<1/2\). Positivity of \(m\) and \(2\pi>6\) imply

\[
 0<12m(x)<1.
\]

### 3. Strict overdispersion and positive third cumulant

From \(e_2\ge3m\),

\[
 v=e_2-m^2>2m>0.
\]

From \(e_3\ge3e_2\),

\[
 \kappa_3\ge3(1-m)e_2+2m^3.
\]

Because \(m<1/12\), \(3(1-m)>11/4>2\). Hence

\[
 \kappa_3>2e_2>2v>0.
\]

Consequently the variance is strictly decreasing in likelihood coordinate:
\(v'(B)=-\kappa_3(B)<0\).

### 4. Fourth cumulant domination

Cauchy–Schwarz for the tilted higher measure gives \(M_2^2\le M_0M_4\), hence
\(e_2^2\le pe_4\). The support recurrence gives \(p\le m/3\) and
\(e_3\le e_4/3\). Therefore

\[
\begin{aligned}
\kappa_4-2\kappa_3
&=e_4-(4m+2)e_3-3e_2^2
 +(12m^2+6m)e_2-6m^4-4m^3\\
&\ge \frac{1-7m}{3}e_4
 +(12m^2+6m)e_2-6m^4-4m^3.
\end{aligned}
\]

The first term is positive because \(m<1/12\) and \(e_4>0\). For the second, \(e_2\ge3m\)
gives

\[
(12m^2+6m)e_2-6m^4-4m^3
\ge2m^2(9+16m-3m^2)>0.
\]

Thus

\[
\kappa_4>2\kappa_3>0.
\]

### 5. Alternating source jets

Let \(A(x)=\pi e^{2x}\). For \(x\ge0\), \(A>3\). The first four derivatives of the source
log-partition are

\[
\begin{aligned}
g_1&=-2Am,\\
g_2&=4A^2v-4Am,\\
g_3&=-8A^3\kappa_3+24A^2v-8Am,\\
g_4&=16A^4\kappa_4-96A^3\kappa_3+112A^2v-16Am.
\end{aligned}
\]

The inequalities \(v>2m\), \(\kappa_3>2v\), and \(\kappa_4>2\kappa_3\), together with
\(A>3\), imply

\[
g_1<0,\qquad g_2>0,\qquad g_3<0,\qquad g_4>0.
\]

### 6. Strict reflected likelihood Riccati law

For \(0<t\le u\), let

\[
q(t)=2g(u)-g(u+t)-g(u-t).
\]

Because \(g_2>0\), \(g_1\) is strictly increasing and
\(q'=g_1(u-t)-g_1(u+t)<0\). Directly,
\(q''=-g_2(u+t)-g_2(u-t)<0\). Because \(g_4>0\), \(g_3\) is strictly increasing and
\(q'''=g_3(u-t)-g_3(u+t)<0\). Therefore

\[
2q'q''-q'''>0.
\]

This unconditionally discharges the pure likelihood reflected Riccati hypothesis.

### 7. Exact remaining atom–likelihood obstruction

The single-atom reflected action has \(a'>0\) and \(a''>0\), whereas the likelihood action has
\(q'<0\) and \(q''<0\). Thus the mixed term

\[
X=2(a'q''+q'a'')
\]

is strictly negative. The completed margin is exactly

\[
R_{\rm completed}=R_{\rm atom}+R_{\rm likelihood}+X.
\]

Hence positivity of each component margin alone does not close the completed source. The remaining
same-half-line obligation is the exact quantitative domination

\[
-X<R_{\rm atom}+R_{\rm likelihood}.
\]

This replaces the opaque nonnegativity hypothesis on the total cumulant correction by a single
explicit competition between two unconditional positive margins and one unconditional negative
interference channel.

## Hostile checks

- No numerical evaluation is used; only \(\pi>3\).
- The support edge is not re-proved: existing corpus theorem is promoted and reused.
- The claim does not infer completed-source positivity from positivity of its two summands; the
  mixed Riccati term has the opposite sign and is retained exactly.
- No global center-mixed positivity or RH conclusion is claimed.

## Lean realization

Formalized in:

- `RHTower/ThetaCusp/ThetaCuspLikelihoodGapCumulantRiccati.lean`;
- reusable support theorem promoted in
  `RHTower/ThetaCusp/ThetaCuspCassiniMarkovBoundaryTransport.lean`;
- existing fourth-log-jet derivative API exposed in
  `RHTower/ThetaCusp/ThetaCuspFullReflectionFourthTuran.lean`;
- reduced wall interface wired into
  `RHTower/Hedenmalm/HedenmalmCenterMixedCorrelationAngle.lean`.

## Remaining target

Prove the explicit atom--likelihood cross-domination inequality, then attack the independent
seam-crossing correlation-angle law. These are kept separate: low cumulants and both component
Riccati margins no longer appear as hypotheses.
