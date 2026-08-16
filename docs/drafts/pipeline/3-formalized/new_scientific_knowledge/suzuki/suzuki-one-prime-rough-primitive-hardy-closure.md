# One-prime rough-primitive Hardy transfer closes trace-zero finite-aperture regularity

- **ID:** `suzuki-one-prime-rough-primitive-hardy-closure`
- **Stage:** 3 — formalized in Lean 4
- **Type:** LOW-RANK SOURCE THEOREM / ROUGH-PRIMITIVE HARDY CLOSURE
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-literal-paired-source-assembly.md`,
  `suzuki-polynomial-carrier-gamma-dimension-wall.md`,
  `../../../3-formalized/new_scientific_knowledge/suzuki/suzuki-complementary-primitive-flux-derivative-recovery.md`,
  `../../../3-formalized/new_scientific_knowledge/suzuki/suzuki-dyadic-orbit-chart-h1-coverage.md`

## 1. Theorem

Let (a>0) satisfy

\[
 2a<\log 3.                                                     \tag{1}
\]

Then Suzuki's visible-prime valuation rank is zero or one. Let (u) be a completed zero mode of
the restricted-Weil operator on ((-a,a)), in the original eigenfunction variable and extended by
zero, and suppose its two signed half-log traces vanish:

\[
 \beta_+(u)=\beta_-(u)=0.                                      \tag{2}
\]

Then

\[
 u\in H^1_0(-a,a).                                             \tag{3}
\]

No inverse-log expansion, conormality premise, flat-sector premise, self-adjoint weighted prime
adjacency, or recurrence hypothesis is assumed. Rank zero/one recurrence clocks are automatically
bounded.

This closes the trace-zero completed-source regularity theorem on the entire first-prime aperture
range. It does not pass the second visible-prime threshold, recurrence-infinite apertures, or the
completed/raw Evans kernel identification.

## 2. Source equation and the low-rank carrier

Literal paired-source assembly gives, on a terminal logarithmic ray,

```text
A F' + ZF = G' + H,
A = 2L I + R - B,                                      (4)
```

with exact rooted signs. Here (G) is the rough cutoff primitive, (H) is zero order, and both
belong to every prescribed Gamma block class below height one.

When no prime is visible, use transport degree (kappa=0). When only prime (2) is visible, use
the polynomial valuation weight

\[
 w(n)=(1+|n|)^{-2/3}.                                  \tag{5}
\]

The one-dimensional square sum converges, and the weighted prime group has two-sided polynomial
degree (kappa=2/3). Choose

\[
 \kappa=\frac23,qquad \sigma=\frac34,qquad
 p=\frac12+\sigma=\frac54.                             \tag{6}
\]

The sharp Gamma dimension theorem gives (kappa<sigma<1). Since
(ell(n)=n\log2), every physical event time lies in a bounded set apart from retained exact root
ports. Thus the polynomial carrier absorbs every literal source coordinate with no logarithmic
recurrence loss.

## 3. Zero-order sources can be completed to rough primitives

After one terminal cutoff, take $H$ supported in $[L_0,\infty)$. Put

\[
 C_H=\int_{\mathbb R}H(t)\,dt,\qquad
 J(L)=\int_L^\infty H(t)\,dt.                           \tag{7}
\]

Choose smooth $\zeta$ equal to one on $(-\infty,L_0-1]$, zero on $[L_0,\infty)$, and
transitioning where $H=0$. Define

\[
 K=-J+C_H\zeta.                                         \tag{8}
\]

Then $K=0$ on the negative exterior, $K=-J$ on the terminal ray, and

\[
 K'=H+C_H\zeta',\qquad H=K'-C_H\zeta'.                 \tag{9}
\]

The remainder $-C_H\zeta'$ is smooth and compactly supported. The weighted Hardy inequality gives

\[
 \|e^{\sigma L}K\|_{L^2}
 \le C_{\sigma,\zeta}\|e^{\sigma L}H\|_{L^2}.          \tag{10}
\]

The stronger block statement follows from the same backward integral. If

```text
h_n = ||e^(sigma L)H||_(L2([n,n+1])),
k_n = ||e^(sigma L)K||_(L2([n,n+1])),
```

then

\[
 k_n\le C_\sigma\sum_{j\ge n-1}e^{-\sigma(j-n)}h_j.    \tag{11}
\]

The geometric kernel is in $\ell^1$, so the literal Gamma block norm of $K$ is finite whenever
that of $H$ is finite. Consequently `(4)` becomes

```text
A F' + ZF = G_total' + H_compact,                       (12)
```

where $G_{\rm total}=G+K$ has the same rough-primitive block class and
$H_{\rm compact}=-C_H\zeta'$ is smooth and compact. This step uses no derivative of $H$.

## 4. Polynomial-group one-block theorem

Fourier transformation of `(12)` and division by the leading factor $z$ makes a primitive block
enter without frequency loss:

\[
 f'(z)=\mathcal A(z)f(z)-\frac{i}{2}\widehat G_{\rm total}(z)
       -\frac{1}{2z}\widehat H_{\rm compact}(z).        \tag{13}
\]

The last term is Schwartz away from the already-removed regular-singular charges. Consider one
physical unit block of $G_{\rm total}$. On $z=x+i\sigma$, the paired fundamental matrix has
slow exponent $p=1/2+\sigma$, while the prime group contributes degree $\kappa$. For
$x\ge t$ beyond the block threshold,

\[
 \|\mathcal H(x)\mathcal H(t)^{-1}\|
 \le C\left(\frac{t}{x}\right)^p(1+x-t)^\kappa.        \tag{14}
\]

Carry the existing Gamma one-block integration-by-parts proof one order farther, to three
frequency integrations. The endpoint at $t=x$ contains
$\mathcal H(x)\mathcal H(x)^{-1}=I$, so polynomial transport cancels there. Resolvent boundary
terms are $L^2$ by Plancherel exactly as in the degree-zero theorem. The lower endpoint and the
homogeneous component have norm majorant

\[
 x^{\kappa-p}.                                         \tag{15}
\]

The third remainder is bounded by

\[
 \int_X^x
 \left(\frac{t}{x}\right)^p(1+x-t)^\kappa t^{-3}\,dt. \tag{16}
\]

Split at $t=x/2$. Since $p<3/2$, the far part satisfies

\[
 \int_X^{x/2}(\cdots)\,dt\le C x^{\kappa-p}.           \tag{17}
\]

On $x/2\le t\le x$, use $t^{-3}\le 8x^{-3}$:

\[
 \int_{x/2}^{x}(\cdots)\,dt
 \le Cx^{-3}\int_0^{x/2}(1+s)^\kappa ds
 \le Cx^{\kappa-2}.                                   \tag{18}
\]

The exact squared-tail tests are therefore

\[
 \int_1^\infty x^{2(\kappa-p)}dx<\infty
 \Longleftrightarrow \kappa<\sigma,                    \tag{19}
\]

and, at integration depth $N$,

\[
 \int_1^\infty x^{2(\kappa+1-N)}dx<\infty
 \Longleftrightarrow \kappa+\frac32<N.                 \tag{20}
\]

For `(6)` and $N=3$, both inequalities are strict. Reflection gives the negative-frequency
tail. The finite frequency interval is bounded, and absolute block summation uses the already
proved literal source norm. Hence

\[
 e^{3L/4}F\in L^2.                                     \tag{21}
\]

This proof explains why arbitrary polynomial degree was false but rank one survives: the free
homogeneous/lower-end channel forces `(19)`, while repeated integration by parts removes every
finite-degree remainder once `(19)` holds.

## 5. Rough primitive does not obstruct the derivative

Use the complementary cutoffs $M$ and $Q=I-M$. Their exact primitive fluxes satisfy

\[
 Y_M'= (2I-Z)MF+H_M,\qquad
 Y_Q'= (2I-Z)QF+H_Q.                                   \tag{22}
\]

Equation `(21)` puts $MF$ in the required weighted space without any flatness hypothesis. Thus
the first expression in `(22)` is weighted $L^2$. The pre-event $Q$-branch has bounded event
clock in rank one, so the existing recurrence estimate puts the second expression in weighted
$L^2$. The opposite rough primitives cancel before coercivity:

\[
 Y_M'+Y_Q'=(AF)'.                                      \tag{23}
\]

Shifted Gamma numerical-range coercivity applied to `(23)` gives

\[
 e^{3L/4}F'\in L^2.                                    \tag{24}
\]

No derivative of $G$, $K$, or a coordinate cutoff is estimated.

## 6. Global $H^1_0$

Coordinate projection of `(24)` gives the weighted derivative estimate in every realized paired
orbit chart. The formalized dyadic coverage theorem now applies:

- if prime $2$ is invisible, $2a<\log2<1$, and one endpoint unit chart covers $(-a,a)$;
- if prime $2$ is visible, centers $a-k\log2$ have spacing $\log2<1$, and finitely many unit
  charts cover $[-a,a]$.

Since $3/4>1/2$, logarithmic change of variables converts `(24)` to an ordinary $L^2$ weak
derivative on every selected chart. Hence $u\in H^1(-a,a)$. The completed zero extension and
`(2)` give zero Sobolev endpoint traces, proving `(3)`. `QED`

## 7. Hostile audit

1. **No flatness premise.** Direct rough-primitive Hardy gives `(21)` for the assembled state;
   finite-to-flat expansion is bypassed only in rank zero/one.
2. **No source derivative.** $G'$ becomes $-i\widehat G/2$ after division by $z$; $H$ is
   first completed to the backward primitive `(7)`.
3. **No arbitrary-degree claim.** Lower endpoint `(15)` is square-integrable exactly for
   $\kappa<\sigma$.
4. **No finite-IBP handwave.** The two exact squared exponents are `(19)`--`(20)`; three steps
   suffice for the concrete carrier.
5. **No compact-middle debt.** Formalized dyadic charts supply the finite local-to-global cover.
6. **No higher-rank overclaim.** Rank at least two violates $d/2<\kappa<\sigma<1$ for every
   uniform radial carrier.
7. **No RH claim.** Second-prime and higher apertures, recurrence-infinite transfer, nonzero-trace
   return, completed/raw Evans identification, raw Evans positivity, and producer classes P/I
   remain.

## 8. Novelty boundary

Weighted Hardy inequalities, repeated integration by parts, and polynomially bounded groups are
classical separately. The source-specific result not found in Suzuki's 2022/2026 screw-function
papers or the predecessor corpus is the exact conjunction

```text
literal rough primitive
+ rank-one fractional orbit carrier
+ three-step Gamma integration by parts
+ complementary primitive cancellation
+ dyadic chart coverage
 -> trace-zero H1_0 below the second-prime threshold.   (25)
```

External priority remains unverified.

## 9. Lean certificate

`formal/GaloisForLFunctions/RHTower/SuzukiOnePrimeRoughPrimitiveHardyTail.lean` proves
unconditionally:

```text
integrableAtTop_suzukiPolynomialIBPFarTailNormSq_iff
  far-end squared tail is integrable iff kappa < sigma;

integrableAtTop_suzukiPolynomialIBPNearTailNormSq_iff
  Nth remainder squared tail is integrable iff kappa + 3/2 < N;

integrableAtTop_suzukiPolynomialIBPTails_iff
  exact joint window;

suzukiOnePrimeThirdIBPTails
  concrete (kappa,sigma,N)=(2/3,3/4,3) certificate;

tsum_suzukiBackwardGeometricBlockEnvelope_le
  sharp unconditional l1 mass bound for the backward primitive;

tsum_suzukiBackwardGeometricBlockEnvelope_lt_top
  strict geometric contraction preserves finite block mass.
```

The operator-valued one-block estimate is now formalized as well (2026-08-16), closing the
`2 -> 3` gate:

```text
GaloisForLFunctions.HTGeometry.polynomialTransportIntegrand
GaloisForLFunctions.HTGeometry.integral_polynomialTransportIntegrand_le
  (16)--(18): the third remainder splits at x/2 into x^(kappa-p) and x^(kappa-2);

GaloisForLFunctions.HTGeometry.norm_transport_lowerEndpoint_le
  (15): the propagated lower endpoint has majorant x^(kappa-p);

GaloisForLFunctions.HTGeometry.norm_transport_remainder_le
  (14)--(18) operator-valued, for an arbitrary transport family with the polynomial bound;

GaloisForLFunctions.HTGeometry.lintegral_sq_polynomialTransportProfile_ne_top
  (21): the block profile is square integrable exactly under kappa < sigma and kappa + 3/2 < 3;

GaloisForLFunctions.RHTower.lintegral_sq_onePrimeBlockProfile_ne_top
  the same at the concrete carrier (kappa,sigma,N)=(2/3,3/4,3);

GaloisForLFunctions.HTGeometry.norm_invFamilyProduct2Deriv_le_rpow_neg_three
  the amplitude left by three integrations by parts decays like t^(-3) on the ray;

GaloisForLFunctions.HTGeometry.norm_le_of_complementaryFlux_coercive
  (23)--(24): the rough primitives cancel before coercivity;

GaloisForLFunctions.RHTower.lintegral_energy_ne_top_of_chart_cover
  the local-to-global step of section 6 over the formalized dyadic charts.
```

Construction of Suzuki's concrete restricted-Weil operator and the vector-valued Fourier/Bochner
composition remain items of the later gates; no Lean wrapper assumes `(3)`.

`SuzukiOnePrimeFractionalCarrier.lean` also closes a prerequisite discovered during formal audit:
the exact `kappa=2/3` weighted valuation shifts are square-summable, obey the polynomial energy
bound, and satisfy the exact group law. Earlier integer-degree infrastructure did not imply this.

## Gates

- [x] close exact polynomial/Gamma homogeneous threshold
- [x] prove third-order remainder threshold
- [x] certify concrete rank-one parameters in Lean
- [x] convert zero-order terminal source to rough primitive
- [x] prove polynomial-group one-block transfer at rank one
- [x] compose complementary flux and dyadic coverage on paper
- [x] formalize backward block-primitive preservation
- [x] construct the fractional `2/3` polynomial shift group
- [x] formalize operator-valued polynomial-group one-block estimate
- [ ] pass the second-prime threshold
- [ ] pass recurrence-infinite apertures
- [ ] identify completed/raw Evans kernels and prove positivity
- [ ] RH or whole-Connes no-go
