# Suzuki Gamma--Beta Markov/Stokes transparency

- **ID:** `suzuki-gamma-beta-markov-stokes-transparency`
- **Stage:** 1-in-progress
- **Type:** PAPER THEOREM / ARCHIMEDEAN COMPLETE-POSITIVITY INPUT /
  THIRD-COMPLETION BOUNDARY LAW
- **Scientific status:** `[PAPER-PROVED] [SOURCE-PURE] [NOT RH]`
  `[CLASSICAL BETA/GAMMA PARENT]`
  `[CORPUS-NEW STOKES COUPLING]`
  `[EXTERNAL NOVELTY UNVERIFIED]`
- **Parents:**
  - `../../../3-formalized/gamma-sonin-asymptotic-passivity-incidence-curvature.md`;
  - `prime-aperture-stokes-action-law.md`;
  - `prime-stokes-ccm-unit-resolvent-weld.md`;
  - `deninger-enhanced-adiabatic-milnor-calderon-vanishing-cycle.md`.
- **Statement:** After division by its exact operator norm, the
  pole-cleared Suzuki archimedean Gamma multiplier is a unimodular
  scattering multiplier times the characteristic function of a
  log-Beta probability law.  It therefore has a canonical
  Markov/defect dilation, not merely an \(L^2\) norm bound.  At the
  arithmetic critical scaling \(\omega=\varepsilon/2\), this calibrated
  Gamma channel converges to the identity on every finite
  aperture-Stokes frequency scale \(O(\varepsilon^{-1})\).  It preserves
  the grade-\(c\) exponential principal symbol, but the convergence is
  not uniform over all frequencies; hence it does not itself restore
  Xi conormal fibres.

## 1. Exact calibrated factorization

Let
\[
 \gamma(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)
\]
and, for \(0<\omega<1/2\), put
\[
 m_\omega(t)
 =
 \frac{\gamma(1/2-\omega+it)}
      {\gamma(1/2+\omega+it)}.                           \tag{1}
\]
The corpus proves the exact norm
\[
 M_\omega
 =
 \sup_{t\in\mathbb R}|m_\omega(t)|
 =
 \pi^\omega
 \frac{\Gamma(1/4-\omega/2)}
      {\Gamma(1/4+\omega/2)}.                            \tag{2}
\]
Set
\[
 a_\omega=\frac14-\frac\omega2,\qquad
 b_\omega=\frac14+\frac\omega2=a_\omega+\omega.          \tag{3}
\]
Direct expansion of `(1)` gives
\[
 \frac{m_\omega(t)}{M_\omega}
 =
 u_\omega(t)\varphi_\omega(t),                           \tag{4}
\]
where
\[
 u_\omega(t)
 =
 \frac{(1/2-\omega+it)(-1/2-\omega+it)}
      {(1/2+\omega+it)(-1/2+\omega+it)}                  \tag{5}
\]
and
\[
 \varphi_\omega(t)
 =
 \frac{\Gamma(a_\omega+it/2)\Gamma(b_\omega)}
      {\Gamma(b_\omega+it/2)\Gamma(a_\omega)}.           \tag{6}
\]
For real \(t\), the two polynomial moduli in `(5)` are exchanged,
so
\[
 |u_\omega(t)|=1.                                       \tag{7}
\]

Let \(B_\omega\) have the Beta distribution
\[
 B_\omega\sim{\rm Beta}(a_\omega,\omega).
\]
The Beta integral gives
\[
 \mathbb E[B_\omega^{it/2}]
 =
 \frac{B(a_\omega+it/2,\omega)}
      {B(a_\omega,\omega)}
 =
 \varphi_\omega(t).                                     \tag{8}
\]
Thus \(\varphi_\omega\) is a normalized positive-definite function
and
\[
 |\varphi_\omega(t)|\leq1.                              \tag{9}
\]
Equations `(4)`, `(7)`, and `(9)` recover the exact passivity bound,
but retain more structure than the scalar estimate.

## 2. Canonical Markov and defect dilation

Let \(P_\omega\) be convolution on \(L^2(\mathbb R)\) by the law of
\(\frac12\log B_\omega\), and let \(U_\omega\) be the unitary Fourier
multiplier with symbol \(u_\omega\).  In Fourier coordinates,
\[
 T_\omega:=U_\omega P_\omega
\]
has symbol \(m_\omega/M_\omega\).  The convolution \(P_\omega\) is
the \(L^2\) implementation of a translation Markov operator; in
particular it is positive, constant-preserving, and contractive.
The second factor is an exact unitary scattering stage.

Equivalently, put
\[
 D_\omega=(I-T_\omega^*T_\omega)^{1/2}.
\]
Then
\[
 V_\omega f=(T_\omega f,D_\omega f)
\]
is an isometry from \(L^2(\mathbb R)\) to
\(L^2(\mathbb R)\oplus L^2(\mathbb R)\).  Hence the calibrated Gamma
multiplier has a source-defined Julia/Stinespring defect channel.  No
Xi zero, divisor norm, or target Pick kernel enters this construction.

This closes only the archimedean finite-channel problem.  A unitary
scattering followed by a Markov convolution does not manufacture the
Euler--Gamma/co-Poisson comparison or its conormal boundary.

## 3. Critical Stokes transparency

The aperture-Stokes corner uses
\[
 \varepsilon=\sigma-1=2\omega.                           \tag{10}
\]
The relevant normalized multiplier is therefore
\[
 g_\varepsilon(t)
 :=
 \frac{m_{\varepsilon/2}(t)}
      {M_{\varepsilon/2}}.                               \tag{11}
\]

### Theorem

For every \(C>0\),
\[
 \sup_{|t|\leq C/\varepsilon}
 |g_\varepsilon(t)-1|
 \longrightarrow0
 \qquad(\varepsilon\downarrow0).                        \tag{12}
\]

### Proof

For sufficiently small \(\varepsilon\), the interval
\([a_{\varepsilon/2},b_{\varepsilon/2}]\) lies in one compact
subinterval of \((0,\infty)\).  On that interval the standard
vertical-strip digamma bound is
\[
 |\psi(x+iy)|
 \leq C_0+C_1\log(2+|y|).                               \tag{13}
\]
Using a holomorphic logarithm of Gamma in the right half-plane and
integrating in the real parameter gives
\[
\begin{aligned}
 \log\varphi_{\varepsilon/2}(t)
 &=
 \int_{a_{\varepsilon/2}}^{b_{\varepsilon/2}}
   \left[\psi(x)-\psi(x+it/2)\right]\,dx .
\end{aligned}                                           \tag{14}
\]
The length of the interval is \(\varepsilon/2\), so `(13)`--`(14)`
give, uniformly for \(|t|\leq C/\varepsilon\),
\[
 |\log\varphi_{\varepsilon/2}(t)|
 \leq
 C_2\varepsilon\log(2+C/\varepsilon)
 \longrightarrow0.                                     \tag{15}
\]
The rational function `(5)` is smooth in \(\omega\) on the real
\(t\)-axis, its denominators stay uniformly away from zero, and
\(u_0(t)=1\).  Differentiating `(5)` in \(\omega\), or subtracting
the two rational expressions directly, gives
\[
 \sup_{t\in\mathbb R}|u_{\varepsilon/2}(t)-1|
 \leq C_3\varepsilon.                                   \tag{16}
\]
Equations `(4)`, `(15)`, and `(16)` prove `(12)`.
\(\square\)

In particular, for every fixed finite aperture action \(c\),
\[
 g_\varepsilon(c/\varepsilon)\longrightarrow1.          \tag{17}
\]
Thus the oscillatory reporter packet
\(\exp(-ic\tau/\varepsilon)\) and its nonzero Stokes residue are not
erased by the canonically calibrated Gamma leg.

More generally, if \(f_\varepsilon\) is Fourier-supported in
\([-C/\varepsilon,C/\varepsilon]\), then
\[
 \|(T_{\varepsilon/2}-I)f_\varepsilon\|_2
 \leq
 \sup_{|t|\leq C/\varepsilon}|g_\varepsilon(t)-1|
 \|f_\varepsilon\|_2
 =
 o(\|f_\varepsilon\|_2).                                \tag{18}
\]
This is the operator form of finite-action Stokes transparency.

## 4. Strong residue-metric conservation

For each fixed real \(t\),
\[
 g_\varepsilon(t)\to1,\qquad |g_\varepsilon(t)|\leq1.
\]
Dominated convergence therefore gives
\[
 T_{\varepsilon/2}\longrightarrow I
\quad\text{strongly on }L^2(\mathbb R).                 \tag{19}
\]
Let \(G\) be any bounded positive residue metric, in particular the
unit aperture-averaged prime-Stokes metric
\[
 2I\leq G\leq4I.
\]
Then for every \(f\in L^2\),
\[
 \langle T_{\varepsilon/2}^*GT_{\varepsilon/2}f,f\rangle
 \longrightarrow
 \langle Gf,f\rangle.                                   \tag{20}
\]
Hence calibrated Gamma completion preserves the already-constructed
prime-Stokes residue metric in the strong nearby-cycle limit.

## 5. Calibration is forced at exponential grade

The raw multiplier is \(m_\omega=M_\omega g_\omega\), and smoothness
of `(2)` at \(\omega=0\) gives
\[
 M_\omega=1+O(\omega).                                  \tag{21}
\]
The aperture defect at action \(c>0\) has size
\[
 a_c(\varepsilon)
 =
 \frac{\varepsilon}{c}e^{-c/\varepsilon}.               \tag{22}
\]
The algebraic error in `(21)` dominates `(22)` by every exponential
order.  Consequently the unnormalized Gamma multiplier has no
well-defined grade-\(c\) comparison with the prime aperture defect.
Division by the exact source norm `(2)` is not an optional rescaling:
it is required before the Stokes associated graded is formed.

This gives a precise mathematical role to Gamma calibration in the
third-completion program:

```text
raw Gamma ratio:
  algebraic amplitude masks exponentially flat Euler residue;

exactly norm-calibrated Gamma ratio:
  unitary scattering times a Beta Markov channel,
  transparent on every finite aperture-Stokes grade.
```

## 6. Nonuniformity and hard boundary

For every fixed \(\omega>0\), the Gamma-ratio asymptotic gives
\[
 |\varphi_\omega(t)|\asymp |t|^{-\omega}
 \qquad(|t|\to\infty).                                  \tag{23}
\]
Therefore
\[
 \inf_{t\in\mathbb R}|g_\varepsilon(t)|=0
\]
for every \(\varepsilon>0\).  Convergence in `(19)` is not operator
norm convergence, and the completed form
\(T_{\varepsilon/2}^*GT_{\varepsilon/2}\) is not uniformly coercive
on the full reporter-frequency space.

The threshold is visible from `(15)`: frequencies with
\(\varepsilon\log|t|=O(1)\), hence
\(|t|\) exponential in \(1/\varepsilon\), can carry a nontrivial
additional Gamma action.  The paper theorem preserves each finite
prime-aperture action but does not prove conservation of the complete
hyperfunction/transseries conormal.

This prevents the result from being misused:

1. it does not make point evaluation continuous in ambient \(L^2\);
2. it does not prove source-effective Wold--Calderón product
   conservativity;
3. it does not identify the anti-Hardy vanishing cycle with
   \(\ell_E\);
4. it does not prove complete Pick positivity of the shifted-Xi
   quotient; and
5. it does not imply RH.

The positive successor is narrower.  The all-prime enhanced
construction may now take the calibrated Gamma leg as an explicit
Markov/scattering correspondence which preserves every finite Stokes
grade.  The remaining frontier theorem is the unbounded
source-relative Calderón/co-Poisson transgression and its
multiplicity-jet conservativity.

## 7. General HT consequence

This theorem exhibits a three-level distinction for a constrained HT
comparison:

```text
boundedness:
  exact Gamma norm M_omega;

complete-positive realization:
  log-Beta Markov channel plus unitary scattering;

exponential conservativity:
  transparency on finite Stokes actions, failure of uniform
  transparency at exponentially high reporter frequencies.
```

A finite norm estimate does not determine the source environment, and
a source-defined CP dilation still does not determine the full
exponential boundary.  The extra invariant is the frequency-dependent
Stokes action of the calibrated dilation.

## 8. Novelty boundary

Parent mathematics includes:

- the Beta integral and the Mellin transform of a Beta random
  variable;
- Bochner positivity of characteristic functions;
- Markov convolution and Julia/Stinespring dilation;
- vertical-strip Gamma-ratio and digamma bounds; and
- strong convergence of bounded Fourier multipliers.

The log-Beta/Gamma-ratio probability representation is therefore not
claimed as new.  Targeted corpus and external searches did not locate
the project-specific conjunction: the exact norm-calibrated Suzuki
Gamma multiplier is a Beta Markov/scattering channel, its raw scalar
normalization masks the prime-aperture exponential residue, and its
calibrated channel is transparent precisely through every finite
aperture-Stokes action while losing uniform control at exponentially
high reporter frequency.  External novelty and significance remain
unverified.

Primary parent references:

- NIST DLMF, §5.11(iii), Gamma-ratio asymptotics;
- the classical Euler Beta integral;
- Bochner's theorem for positive-definite functions.

## Gates

- [x] exact Gamma/Beta factorization proved on paper
- [x] unimodular polynomial scattering factor identified
- [x] canonical Markov and defect dilation constructed
- [x] finite-action Stokes transparency proved
- [x] strong residue-metric conservation proved
- [x] exact calibration necessity at exponential grade proved
- [x] nonuniform high-frequency obstruction isolated
- [x] corpus collision audit
- [ ] independent specialist novelty/significance audit
- [ ] formalize only if the complex Beta-integral and vertical
      digamma interfaces can carry the theorem without a wrapper shell
- [ ] couple the channel to the relative Wold--Calderón first-cell
      complex
- [ ] prove all-prime source conormal conservativity
- [ ] RH

## Log

- 2026-07-29 — Factored the exactly calibrated Suzuki Gamma multiplier
  into a log-Beta Markov characteristic function and a unimodular
  rational scattering factor.  Proved strong and
  \(O(\varepsilon^{-1})\)-frequency Stokes transparency at the
  arithmetic scaling \(\varepsilon=2\omega\), and proved that the
  uncalibrated scalar factor masks every finite exponential aperture
  grade.  Recorded the exponential-frequency nonuniformity which
  prevents this finite CP theorem from being misread as conormal
  conservativity or RH.
