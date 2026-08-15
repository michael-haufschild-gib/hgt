# Mass-shifted completed-source hard-edge compactness

- **ID:** `mass-shifted-completed-source-hard-edge-compactness`
- **Stage:** 2-fully-proven / needs specialist audit
- **Route:** U, compactified first-contact source
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN NOT STARTED]`
- **Depends on:** `mass-shifted-hard-edge-paley-wiener-compactification` and the completed Weil
  source formula

## Result

Put `y=a^2`, and for a real polynomial `p` define the literal rational hard-edge test

\[
 g_{a,p}(x)={a\over\sqrt{a^2+x^2}}
 p\!\left((a^2+x^2)^{-1}\right).                              \tag{CSHC.1}
\]

Its completed Xi divisor form is exactly

\[
 \mathcal W(g_{a,p})
 :=\Re\sum_q g_{a,p}(\alpha_q)^2
 =a^2\Phi_{a^2}[p].                                           \tag{CSHC.2}
\]

Fix `C>0`. There are constants `b_C,B_C>0` and `a_C` such that every nonzero `p` with
`deg p<=Ca`, `a>=a_C`, and `mathcal W(g_(a,p))<=0` satisfies

\[
 \boxed{\quad
 {\displaystyle\int_{\mathbb R}\log(2+|x|)|g_{a,p}(x)|^2dx
  \over \|g_{a,p}\|_2^2}
 \le B_C.
 \quad}                                                       \tag{CSHC.3}
\]

Moreover,

\[
 \boxed{\quad
 \|g_{a,p}'\|_2
 \le {2(\deg p+1)\over a}\|g_{a,p}\|_2.
 \quad}                                                       \tag{CSHC.4}
\]

Consequently every normalized family

\[
 a_j\to\infty,\qquad \deg p_j\le Ca_j,\qquad
 \|g_{a_j,p_j}\|_2=1,\qquad \mathcal W(g_{a_j,p_j})\le0       \tag{CSHC.5}
\]

has a strongly convergent `L^2(R)` subsequence. Every limit is a nonzero real Paley--Wiener
function of exponential type at most `2C`.

Thus the `Theta(sqrt(y))` theorem does more than bound degree. Completed prime--Gamma incidence
prevents the bounded-type packet from translating to height infinity. Route U's cofinal first
contacts have genuine nonzero finite-type subsequential limits.

## 1. Exact completed source

For a real even test `g` of the present rational class, the explicit formula is

\[
 \begin{aligned}
 \mathcal W(g)
 ={}&2g(i/2)^2
 +{1\over\pi}\int_{\mathbb R}g(x)^2\vartheta_\infty(x)dx\\
 &-{1\over\pi}\sum_{n\ge2}{\Lambda(n)\over\sqrt n}
      \widehat{g^2}(\log n).                                  \tag{CSHC.6}
 \end{aligned}
\]

The polar term is nonnegative. The archimedean rate obeys universal constants `b,B>0` with

\[
 \vartheta_\infty(x)\ge b\log(2+|x|)-B.                       \tag{CSHC.7}
\]

The only issue is a coefficient-uniform bound for the complete prime term when degree moves with
`a`.

## 2. Rational prime information cone

Use

\[
 x=a\tan(\theta/2),\qquad -\pi<\theta<\pi,
\]

and set

\[
 q_{a,p}(\theta)=p\!\left(a^{-2}\cos^2(\theta/2)\right).
\]

Then `q_(a,p)` is a real trigonometric polynomial of degree at most `deg p`, and cancellation of
the half-density Jacobian gives

\[
 \|g_{a,p}\|_2^2={a\over2}\int_{-\pi}^{\pi}q_{a,p}(\theta)^2d\theta, \tag{CSHC.8}
\]

\[
 \widehat{g_{a,p}^2}(L)
 ={a\over2}\int_{-\pi}^{\pi}q_{a,p}(\theta)^2
 e^{-iaL\tan(\theta/2)}d\theta.                              \tag{CSHC.9}
\]

The contour shift needs an endpoint argument because the Fourier exponential has an essential
singularity at `theta=pi`.  Put `w=e^(i theta)` and

\[
 E_L(w)=\exp\!\left(aL{1-w\over1+w}\right).
\]

Then `E_L` is holomorphic on `|w|>1`, including infinity, and the real-circle integral is the
radial limit from `|w|>1`.  Indeed, on `|w|=rho>1`,

\[
 \Re {1-w\over1+w}={1-\rho^2\over|1+w|^2}\le0,
\]

so `|E_L|<=1`; dominated convergence as `rho` decreases to one recovers (CSHC.9), including the
single endpoint as a null set.  Cauchy's theorem in the annulus `1<|w|<e^sigma` then moves the
integral to `|w|=e^sigma` without crossing the endpoint singularity.  On that circle,

\[
 \Im\tan((\theta-i\sigma)/2)
 =-{\sinh\sigma\over\cos\theta+\cosh\sigma}
 \le-\tanh(\sigma/2),                                      \tag{CSHC.10}
\]

Equivalently this is `theta -> theta-i sigma`.  If
`q(theta)=sum_(|k|<=N)q_k e^(ik theta)`, Parseval gives the exact exterior-circle estimate

\[
 \int_{-\pi}^{\pi}|q(\theta-i\sigma)|^2d\theta
 =2\pi\sum_{|k|\le N}|q_k|^2e^{2k\sigma}
 \le e^{2N\sigma}\int_{-\pi}^{\pi}|q(\theta)|^2d\theta.
\]

Therefore

\[
 \boxed{\quad
 { |\widehat{g_{a,p}^2}(L)|\over\|g_{a,p}\|_2^2}
 \le \exp\!\left(2N\sigma-aL\tanh(\sigma/2)\right).
 \quad}                                                       \tag{CSHC.11}
\]

Fix `L_C>4C`.  Since the derivative at zero of
`L_C tanh(sigma/2)-2C sigma` is `L_C/2-2C>0`, choose one small `sigma>0` and `delta>0` such that

\[
 L_C\tanh(\sigma/2)-2C\sigma=\delta>0.              \tag{CSHC.11a}
\]

For `log n<=L_C`, the trivial Fourier bound is

\[
 |\widehat{g^2}(\log n)|\le\|g\|_2^2.                         \tag{CSHC.12}
\]

For `log n>L_C`, (CSHC.11) and `N<=Ca` give

\[
 { |\widehat{g^2}(\log n)|\over\|g\|_2^2}
 \le e^{2Ca\sigma}n^{-a\tanh(\sigma/2)}.
\]

Using `Lambda(n)<=log n` and the integral test,

\[
 e^{2Ca\sigma}\sum_{n>e^{L_C}}
   {\log n\over n^{a\tanh(\sigma/2)+1/2}}
 \le C_{C,\sigma,L_C}e^{-a\delta+L_C/2}(1+aL_C).
                                                               \tag{CSHC.12a}
\]

This is uniformly bounded and tends exponentially to zero after increasing `a_C`. Hence

\[
 \boxed{\quad
 \sum_{n\ge2}{\Lambda(n)\over\sqrt n}
 |\widehat{g_{a,p}^2}(\log n)|
 \le B_C\|g_{a,p}\|_2^2.
 \quad}                                                       \tag{CSHC.13}
\]

This is the rational hard-edge information cone: scaled degree `N/a<=C` permits only a bounded
prime-log aperture, uniformly over every coefficient vector.

## 3. Gamma growth forces height tightness

Insert (CSHC.7) and (CSHC.13) into (CSHC.6), discard the nonnegative polar term, and use
`mathcal W(g)<=0`. This gives

\[
 {b\over\pi}\int\log(2+|x|)g(x)^2dx
 \le \left({B\over\pi}+{B_C\over\pi}\right)\|g\|_2^2,        \tag{CSHC.14}
\]

which is (CSHC.3). In particular, normalized null or negative packets are uniformly tight:

\[
 \sup_{a,p}\int_{|x|>R}|g_{a,p}(x)|^2dx
 \le {B_C\over\log(2+R)}\longrightarrow0.                     \tag{CSHC.15}
\]

This uses the completed source essentially. Degree control alone permits translation to arbitrary
height; Gamma growth is the confining potential, while finite prime-log aperture makes arithmetic
forcing bounded at fixed scaled degree.

## 4. Uniform translation control

In the same coordinate,

\[
 g_{a,p}(a\tan(\theta/2))=\cos(\theta/2)q_{a,p}(\theta),
 \qquad {d\theta\over dx}={2\over a}\cos^2(\theta/2).          \tag{CSHC.16}
\]

Bernstein's inequality for a degree-`N` trigonometric polynomial and (CSHC.8) give

\[
 \begin{aligned}
 \|g_{a,p}'\|_2^2
 &\le {2\over a}\left\|
 {d\over d\theta}(\cos(\theta/2)q_{a,p}(\theta))
 \right\|_2^2\\
 &\le {4(N+1)^2\over a^2}\|g_{a,p}\|_2^2,                    \tag{CSHC.17}
 \end{aligned}
\]

proving (CSHC.4). Thus normalized bounded-scaled-degree packets have a uniform translation modulus
in `L^2`.

Equations (CSHC.15) and (CSHC.17) are the two Kolmogorov--Riesz conditions, so (CSHC.5) is strongly
precompact in `L^2(R)`. Norm one makes every strong limit nonzero.

The Fourier-support assertion requires more than pointwise convergence of individual modes.
Introduce the exact self-adjoint Cayley angular-momentum operator

\[
 \mathsf L_a={a^2+x^2\over2a}(-i\partial_x)-{ix\over2a}.       \tag{CSHC.18}
\]

The unitary Cayley half-density sends `e^(ik theta)` to a constant multiple of

\[
 {a\over\sqrt{a^2+x^2}}e^{2ik\arctan(x/a)},
\]

and (CSHC.18) sends this function to `k` times itself.  Hence every present packet satisfies, for
all integers `m>=0`,

\[
 \| (\mathsf L_a/a)^m g_{a,p}\|_2
 \le (N/a)^m\|g_{a,p}\|_2\le C^m\|g_{a,p}\|_2.              \tag{CSHC.19}
\]

Let a normalized subsequence converge strongly to `g`.  For every compactly supported smooth
`phi`, self-adjointness and

\[
 (\mathsf L_a/a)^m\phi\longrightarrow ((-i\partial_x)/2)^m\phi
 \quad\hbox{in }L^2
\]

show that `((-i partial_x)/2)^m g` exists in `L^2` and has norm at most `C^m`.  Plancherel now gives

\[
 \int_{\mathbb R}(|\xi|/2)^{2m}|\widehat g(\xi)|^2d\xi\le C^{2m}.
                                                               \tag{CSHC.20}
\]

If the Fourier transform had positive mass where `|xi|>2C+epsilon`, (CSHC.20) would fail for large
`m`.  Thus `supp widehat g subset [-2C,2C]`.

The same Cayley model gives locally uniform complex convergence, not merely real `L^2`
convergence.  From (CSHC.8), normalized packets have `||q||_2^2=2/a`.  The trigonometric
reproducing-kernel bound, `N/a<=C`, and
`2 arctan(z/a)=2z/a+O_K(a^-3)` imply a uniform bound for `g_(a,p)(z)` on every compact
`K subset C`.  Montel compactness and the real strong limit identify the holomorphic limit.
Together with (CSHC.20), this proves the Paley--Wiener assertion without a mode-measure gap.

## 5. Canonical first-contact consequence

Take any cofinal Route U sequence of singular first-contact blocks with

\[
 N_j/a_j\le C.
\]

Let `p_j` be the terminal-normalized null polynomial and normalize `g_(a_j,p_j)` in `L^2`.
Finite null incidence gives `mathcal W(g_(a_j,p_j))=0`, so the theorem supplies a nonzero strong
Paley--Wiener limit after a subsequence. If also `N_j/a_j->tau`, the complete null row passes to
the limit against every hard-edge packet of type strictly below `2tau`.  For this passage, the
Gamma term is controlled by strong `L^2` convergence against the fixed strip-Schwartz packet, the
polar term by the locally uniform convergence above, and the prime tail by the polarized version
of (CSHC.11)--(CSHC.12a), with degree `N_j+M_j`.  The finite prime prefix passes by ordinary
`L^2` pairing.

Diagonal nullity does **not** follow directly from strong `L^2` convergence: a vanishing amount of
mass could retain nonvanishing logarithmic Gamma energy at infinity.  Instead, (CSHC.3) and lower
semicontinuity put the limit `g` in the form domain

\[
 \int\log(2+|x|)|g(x)|^2dx<\infty.                            \tag{CSHC.21}
\]

For `0<r<1`, the dilation `g_r(x)=g(rx)` has type strictly below `2tau` and converges to `g` in
the norm

\[
 \|h\|_2^2+\int\log(2+|x|)|h(x)|^2dx.                        \tag{CSHC.22}
\]

Strong continuity follows first for compactly supported continuous functions and then by density,
using the moderate-weight inequality
`log(2+|x|/r)<=log(1/r)+log(2+|x|)`.  Smooth interior-frequency functions are dense in the same
weighted Paley--Wiener form domain as follows.  Since `g_r` has Fourier support a positive distance
from the type boundary, choose a smooth Fourier multiplier `m` equal to one on that support and
still supported strictly inside the boundary.  If `chi_R` is a physical cutoff, then
`m(D)(chi_R g_r)` has smooth compactly supported Fourier transform and converges to `g_r` in the
weighted norm.  The last assertion follows from `chi_R g_r -> g_r` and the boundedness of
convolution by the Schwartz kernel of `m(D)` under the moderate logarithmic weight.  Thus
lower-flag orthogonality gives
`mathcal W(g,g_r)=0`.  At fixed type the prime sum is finite, Gamma multiplication is continuous in
(CSHC.22), and evaluation at `i/2` is a bounded Paley--Wiener functional.  Letting `r` increase to
one proves `mathcal W(g,g)=0`.

The limit is therefore a finite-type Weil-null vector orthogonal to the lower-type test flag, not
an arbitrary negative Weil witness.

The polynomial null vectors remain real-rooted in their rational coordinate. Determining the exact
closed constraint this imposes on the Paley--Wiener limit is the next source problem; it is not
being replaced by an unsupported Laguerre--Polya claim.

## Conjecture--failure--pivot audit

1. **Bounded scaled degree automatically gives a nonzero limit.** **Failed.** Packets can translate
   to height infinity; type compactness alone permits weak convergence to zero.
2. **Completed-source height coercivity.** **Proved.** Rational prime information is bounded at
   fixed `N/a`, while Gamma rate grows logarithmically.
3. **Naive mode-measure Paley--Wiener passage.** **Failed as a proof.** Pointwise convergence of
   moving Cayley modes does not control coefficient cancellation.
4. **Cayley angular-momentum compactness.** **Proved.** Uniform bounds for every power of the exact
   self-adjoint generator force sharp Fourier support and locally uniform entire convergence.
5. **Canonical first-contact limit.** **Proved.** Source tightness plus rational Bernstein control
   gives strong, nonzero Paley--Wiener compactness and retains the lower null flag.

## Higher universal principle

Route U had two independent-looking noncompact variables: polynomial degree and spectral height.
They are controlled by the two halves of the completed source.

\[
 \text{degree}/a\quad\longleftrightarrow\quad\text{finite prime-log aperture},
\]

\[
 \text{height}\quad\longleftrightarrow\quad\text{Gamma confining potential}.
\]

Prime information controls frequency; Gamma growth controls position. Together they give phase-
space compactness. Earlier degree recession, first-prime horizon, and Gamma far-right positivity
were shadows of this completed uncertainty law.

## Novelty audit

Corpus search found the heat prime-information cone and several Gamma coercivity statements, but
no rational hard-edge contour estimate (CSHC.11), no completed-source logarithmic tightness at
moving degree, and no strong compactness theorem for Route U first-contact null packets. Literature
search found classical Paley--Wiener, Mehler--Heine, and semiclassical Weil frameworks, but no
matching shifted-Xi reciprocal-Hankel phase-space compactness theorem. No priority claim is made
without specialist audit.

## Lean status

No Lean declaration is claimed. Faithful formalization requires the literal rational test,
trigonometric Cayley substitution, contour shift with endpoint indentation, coefficient-uniform
prime tail, Gamma lower coercivity, rational Bernstein estimate, Kolmogorov--Riesz compactness, and
the canonical Xi null-row limit. An abstract compactness theorem supplied with source estimates as
hypotheses would not meet the route's unconditional Lean requirement.

## Lean formalization status

Formalized so far (all unconditional, axiom profile `[propext, Classical.choice, Quot.sound]`):

| Equation | Lean |
|---|---|
| (CSHC.1) | `RHTower.routeUHardEdgeRationalTest`, `routeUHardEdgeRationalTestSq` (`XiShiftedHardEdgeRationalTest`) |
| (CSHC.2) | `RHTower.tsum_routeUHardEdgeRationalTestSq_eq` |
| (CSHC.4)/(CSHC.17) | `RHTower.integral_deriv_routeUHardEdgeRationalTest_sq_le` (`XiShiftedHardEdgeBernstein`) |
| (CSHC.6) base | `RHTower.tsum_routeUHardEdgeRationalTestSq_one_eq_arithmetic` |
| (CSHC.6) finite reduction | `RHTower.tsum_routeUHardEdgeRationalTestSq_eq_moments`, `..._eq_iteratedDeriv` |
| (CSHC.7) | `RHTower.re_digamma_vertical_ge` (`DigammaVerticalLogGrowth`); companion upper bound `RHTower.abs_re_digamma_vertical_le` (`DigammaVerticalGrowthBound`) |
| (CSHC.8) | `RHTower.integral_routeUHardEdgeRationalTest_sq` |
| (CSHC.9) | `RHTower.routeUHardEdgeFourierSq_eq` |
| (CSHC.10) | `RHTower.re_routeUCayleyMobius_le` |
| (CSHC.11) | `RHTower.norm_routeUHardEdgeFourierSq_le` — see deviation note below |
| (CSHC.12) | `RHTower.norm_routeUHardEdgeFourierSq_le_l2` |
| (CSHC.13) | `RHTower.routeUHardEdgePrimeSum_le` |
| (CSHC.16) | `RHTower.routeUHardEdgeRationalTest_tan` |
| Kolmogorov–Riesz covering half of (CSHC.5) | `GaloisForLFunctions.HTGeometry.totallyBounded_of_finiteDimensional_approx` |

Deviation recorded for (CSHC.11): the Lean proof replaces the card's Parseval-on-the-shifted-circle
step by a Chebyshev-coefficient bound, giving the constant `2(N+1)e^{2Nσ}` in place of `e^{2Nσ}`.
The extra factor is polynomial in the degree and is absorbed by the exponential aperture decay, so
(CSHC.13) and everything downstream is unaffected.

### Remaining build: the density form of (CSHC.6)

The corpus proves (CSHC.6) in *divisor/resolvent-moment* coordinates.  The tightness argument
(CSHC.14) needs it in *density* coordinates, i.e. with the archimedean term as
`(1/pi) int g^2 theta_infty` and the prime term as `(1/pi) sum Lambda(n) n^{-1/2} hat{g^2}(log n)`.
The build plan, module by module:

1. `HTGeometry/PoissonKernelIntegrals` — `int (a^2+x^2)^{-1} = pi/a`,
   `int ((a^2+x^2)(b^2+x^2))^{-1} = pi/(ab(a+b))` (no separation of the heights). **Done.**
2. `HTGeometry/LogWeightedPoisson` — `log(2+|x|)(a^2+x^2)^{-1}` is integrable. **Done.**
3. `RHTower/DigammaVerticalGrowthBound` — `|Re psi(c+iy)| <= K(c) + log(2+|y|)`. **Done.**
4. `RHTower/PoissonDigammaReproduction` — the Poisson kernel of height `a` reproduces the
   archimedean rate: `(1/pi) int a/(a^2+x^2) Re psi(c + i x/2) dx = psi(c + a/2)`. **Done.**
5. `HTGeometry/CauchyKernelFourier` — `int (a^2+x^2)^{-1} e^{-iLx} dx = (pi/a) e^{-a|L|}`, by
   Fourier inversion against the two-sided exponential.
6. `HTGeometry/MassDerivativeTransfer` — for `w` with `‖w(x)‖ <= K + log(2+|x|)`,
   `d/dX int w(x) (X+x^2)^{-(n+1)} dx = -(n+1) int w(x) (X+x^2)^{-(n+2)} dx`.  One lemma serves both
   the archimedean weight and the Fourier kernel.
7. Archimedean moments `A_n(X) = int theta_infty(x)(X+x^2)^{-(n+1)}dx`, with
   `A_0(X) = (pi/sqrt X)(logDeriv Gamma_R(1/2+sqrt X)).re` from module 4.
8. Fourier moments `F_n(X,L)`, with exponential decay in `L` obtained by polarizing the corpus cone
   (`u^k` lies in the span of `{u p(u)^2}`), and the prime function
   `Pi_n(X) = (1/pi) sum_m Lambda(m) m^{-1/2} F_n(X, log m)` differentiated termwise.
9. Monomial density identity by induction on `n`:
   `M_n(X) = 2(X-1/4)^{-(n+1)} + (1/pi) A_n(X) - Pi_n(X)`, then (CSHC.6) in density form for every
   real `p` by linearity.
10. (CSHC.14)/(CSHC.15) tightness, the approximating-subspace half of (CSHC.5), and the Cayley
    angular-momentum Paley–Wiener support (CSHC.18)–(CSHC.20).

### Density-form build: completed

Modules 1–10 of the plan above are now Lean-proved and axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

| Item | Lean |
|---|---|
| Poisson rational integrals | `GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq`, `integral_inv_sq_add_sq_mul'` |
| Logarithmic Poisson integrability | `GaloisForLFunctions.HTGeometry.integrable_log_mul_inv_sq_add_sq` |
| Two-sided vertical digamma bound | `RHTower.abs_re_digamma_vertical_le` |
| Poisson reproduction of the archimedean rate | `RHTower.integral_poissonWeight_mul_re_digamma_half` |
| Fourier transform of the Cauchy kernel | `GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq_mul_cexp_neg` |
| Mass-derivative transfer | `GaloisForLFunctions.HTGeometry.hasDerivAt_massPairing`, `iteratedDeriv_massPairing` |
| Exponential frequency aperture of the mass kernel | `GaloisForLFunctions.HTGeometry.norm_massPairing_cauchyFourierWeight_le` |
| Archimedean moments and (CSHC.7) | `RHTower.routeUArchimedeanMoment_zero_eq`, `RHTower.routeUArchimedeanRate_ge` |
| Prime moments and their closed form | `RHTower.hasDerivAt_routeUPrimeMoment`, `RHTower.routeUPrimeMoment_zero_eq` |
| Monomial density identity | `RHTower.xiResolventMoment_eq_routeUDensityMoment` |
| (CSHC.6) in density coordinates | `RHTower.tsum_routeUHardEdgeRationalTestSq_eq_density` |
| (CSHC.13), mass-uniform | `RHTower.routeUHardEdgePrimeSum_uniform_le` |
| (CSHC.3)/(CSHC.14) | `RHTower.routeUHardEdge_log_moment_le` |
| (CSHC.15) | `RHTower.routeUHardEdge_tail_le` |

Second deviation recorded: the Lean (CSHC.13) fixes the aperture depth at `sigma = 1` and the
threshold at `L_C = 8C + 4`, and states the mass restriction as `a >= 4` rather than an implicit
`a >= a_C`.  With those explicit choices the gain is `L_C·rate(1) - 2C >= 1`, which is what makes the
bound uniform in the mass; the constant is
`B_C = (2C+2)·e^{8C+4}·sum_m Lambda(m) m^{-3/2}`.

Remaining: the approximating-subspace half of (CSHC.5), and the Cayley angular-momentum
Paley–Wiener support (CSHC.18)–(CSHC.20).

### Next: the `L²` precompactness half of (CSHC.5)

Mathlib has no Kolmogorov–Riesz criterion, so it is being built.  The covering half is
`GaloisForLFunctions.HTGeometry.totallyBounded_of_finiteDimensional_approx`; the quantitative half
is the grid approximation.  Its elementary engine is now formal:

    HTGeometry/IntervalPoincare.lean
      sq_integral_le_length_mul                Cauchy-Schwarz against the constant one
      sq_sub_left_le_of_hasDerivAt             |g(x) - g(a)|^2 <= h * int g'^2 on a length-h interval
      integral_sub_left_sq_le_of_hasDerivAt    int (g - g(a))^2 <= h^2 * int g'^2

Remaining steps, in order:

1. `MemLp (routeUHardEdgeRationalTest a p) 2 volume` and the `L^2`-norm identities
   `‖toLp g‖^2 = int g^2`, `‖toLp g - toLp v‖^2 = int (g - v)^2` (both scratch-verified: the second
   is `MemLp.toLp_sub` with `real_inner_self_eq_norm_sq` and `L2.inner_def`).
2. The grid step space: `Submodule.span ℝ` of finitely many indicator classes, finite-dimensional
   because the spanning set is finite.
3. The approximation estimate: on `[-R,R]` with mesh `h`, the left-endpoint step function `v`
   satisfies `int (g - v)^2 <= tail(R) + h^2 * int g'^2`, by summing
   `integral_sub_left_sq_le_of_hasDerivAt` over the grid and adding `routeUHardEdge_tail_le`.
4. Feed the derivative bound `integral_deriv_routeUHardEdgeRationalTest_sq_le` (which gives
   `int g'^2 <= 4(N+1/2)^2/a^2 * int g^2`, hence `<= (2C+1/2)^2 * int g^2` when `N <= Ca` and
   `a >= 4`) and the tail bound into `totallyBounded_of_finiteDimensional_approx`.
5. The nonzero limit, and then (CSHC.18)-(CSHC.20): the Cayley angular-momentum operator, its
   moment bound, and the Paley-Wiener support of the limit.

### (CSHC.5) precompactness: done

Mathlib has no Kolmogorov–Riesz criterion, so a general one was built and is now formal and
axiom-clean:

    HTGeometry/IntervalPoincare.lean         int (g - g(alpha))^2 <= h^2 int g'^2 on a length-h cell
    HTGeometry/UniformGridStep.lean          uniform grids, their left-endpoint step functions, the
                                             telescoping of an interval integral over a grid, and
                                             `integral_sub_gridStep_sq_le`
    HTGeometry/L2GridApproximation.lean      the L^2 norm identities for representatives, the grid
                                             step class as an element of a finite-dimensional
                                             subspace of `Lp R 2 volume`, and
                                             `totallyBounded_toLp_of_tight_deriv`:
                                             uniform L^2 bound + uniform tightness + uniform L^2
                                             derivative bound  ==>  totally bounded in L^2

Its instantiation on the hard-edge family:

    RHTower/XiShiftedHardEdgePrecompactness.lean
      routeUHardEdgeTestDeriv                       the derivative in a Chebyshev frame
      integrable_routeUHardEdgeTestDeriv_sq         its square is integrable
      memLp_routeUHardEdgeRationalTest              the test is in L^2
      totallyBounded_routeUHardEdgeFamily           (CSHC.5): the normalized nonpositive family of
                                                    scaled degree <= C and mass >= 4 is totally
                                                    bounded in L^2(R)
      exists_subseq_tendsto_routeUHardEdge          a strongly convergent subsequence whose limit is
                                                    a unit vector

Only (CSHC.18)-(CSHC.20) remain: the Cayley angular-momentum operator, the moment bound
`‖(L_a/a)^m g‖ <= C^m ‖g‖`, and the Paley-Wiener support `supp ghat subset [-2C, 2C]` of the limit.

### (CSHC.18)-(CSHC.19): done

    RHTower/CosinePhaseParseval.lean
      integral_sin_int_mul                  the full-period integral of an integer-frequency sine
      integral_cos_shift_mul_cos_shift      orthogonality of phase-shifted cosines
      cosPhasePoly                          the m-th derivative frame  sum_j b_j j^m cos(j th + m pi/2)
      hasDerivAt_cosPhasePoly               it really is the derivative frame
      integral_cosPhasePoly_sq              Parseval for it
      integral_cosPhasePoly_sq_le           the L^2 Bernstein inequality  ‖q^(m)‖ <= N^m ‖q‖

    RHTower/XiShiftedHardEdgeAngularMomentum.lean
      routeUCayleyLift                      (U F)(x) = cos(psi(x)/2) F(psi(x))
      routeUCayleyMomentum_lift             (CSHC.18): ((a^2+x^2)/(2a)) d/dx + x/(2a) acts on lifts
                                            as d/d(theta) — the real form of L_a, the half-density
                                            factor supplying exactly the x/(2a) term
      integral_routeUCayleyLift_sq          the lift is an isometry up to the factor a/2
      routeUAngularDescendant_zero          the zeroth descendant is the rational hard-edge test
      integral_routeUAngularDescendant_sq_le_test
                                            (CSHC.19): ‖A_a^m g‖ <= N^m ‖g‖

### The one remaining step: (CSHC.20)

Mathlib now has Plancherel as an `L^2` isometry (`MeasureTheory.Lp.norm_fourier_eq`), so the
Paley–Wiener support can be reached without distribution theory, by the plain-derivative route:

1. In the angular chart the plain derivative acts on the profile as
   `T F = (1/a)·(-(1/2) sin(th) F + (1 + cos th) F')`, which sends a trigonometric polynomial of
   degree `D` to one of degree `D+1` with `‖T F‖ <= (1/a)(2D + 1/2)‖F‖`.
2. Iterating, `‖g^{(m)}‖ <= ((2N + 2m)/a)^m ‖g‖`, which for fixed `m` tends to `(2C)^m` along the
   family because `N <= Ca` and `a -> infinity`.
3. Plancherel converts this into `int (2 pi |xi|)^{2m} |ghat_j|^2 <= (2C + 2m/a_j)^{2m}`, and Fatou
   along an a.e.-convergent subsequence of `ghat_j -> ghat` gives
   `int (2 pi |xi|)^{2m} |ghat|^2 <= (2C)^{2m}` for every `m`.
4. If `ghat` had positive mass where `2 pi |xi| > 2C` the left side would grow geometrically faster
   than the right, so `supp ghat` is contained in `2 pi |xi| <= 2C`, i.e. exponential type `2C`.

What has to be built for step 1 is a general trigonometric-polynomial layer: full Parseval for
`sum_j (b_j cos j th + c_j sin j th)`, closure of the degree filtration under multiplication by
`sin th` and `cos th` and under differentiation, and the `L^2` Bernstein inequality in that
generality.  `CosinePhaseParseval.lean` is the cosine half of it.

### (CSHC.20) build: the trigonometric layer

    HTGeometry/ComplexTrigPolynomial.lean          (axiom-clean, wired, built)
      expMon, integral_expMon, integral_expMon_mul_conj   orthogonality of e^{ik th} on the period
      trigExp D f                                          the degree-D trigonometric polynomial
      integral_normSq_trigExp                              Parseval:  int ‖G‖^2 = 2 pi sum ‖f k‖^2
      hasDerivAt_trigExp                                   d/d th multiplies the k-th coefficient by ik
      integral_normSq_trigExp_deriv_le                     L^2 Bernstein:  ‖G'‖ <= D ‖G‖
      TrigSupp, trigExp_eq_of_supp, trigSupp_*             the degree filtration
      expMon_one_mul_trigExp, expMon_neg_one_mul_trigExp   multiplication by e^{±i th} is the
                                                           coefficient shift, degree D -> D+1

The complex-exponential encoding was chosen because the shift has no edge case at frequency zero,
unlike the real cosine/sine description.

Still to write for (CSHC.20):

1. `RealTrigDeg D F := ∃ f, TrigSupp D f ∧ ∀ th, (F th : ℂ) = trigExp D f th`, with closure under
   the derivative and under multiplication by `sin th` and `cos th` (degree `D+1`), all immediate
   from the shift lemmas and `cos th = (e^{i th} + e^{-i th})/2`, `sin th = (e^{i th} - e^{-i th})/(2i)`.
2. Minkowski for `int (A+B)^2` on `[-pi, pi]` — from the corpus's real Cauchy–Schwarz
   `HTGeometry.sq_integral_mul_le` — giving `‖T F‖ <= (1/a)((1/2) + 2D)‖F‖` for
   `T F = (1/a)(-(1/2) sin th · F + (1 + cos th) F')`.
3. The iteration `‖T^m F‖ <= (1/a)^m prod_{i<m}(2(N+i) + 1/2) ‖F‖`, and hence
   `‖g^{(m)}‖ <= ((2N + 2m)/a)^m ‖g‖` through the Cayley isometry
   `integral_routeUCayleyLift_sq`.
4. Plancherel (`MeasureTheory.Lp.norm_fourier_eq`) and Fatou to pass to the limit, then the
   support conclusion.

### (CSHC.20) build: the real trigonometric layer landed

    HTGeometry/RealTrigDegree.lean                (axiom-clean, wired, built)
      expMon_one_add_neg_one, expMon_one_sub_neg_one   Euler for the two shift monomials
      RealTrigDeg D F                                   F real with (F : C) of degree at most D
      RealTrigDeg.mono / .deriv / .mul_cos / .mul_sin / .add / .smul / .congr / .continuous
                                                        the closure calculus: differentiating keeps
                                                        the degree, multiplying by cos or sin raises
                                                        it by one
      RealTrigDeg.integral_deriv_sq_le                  L^2 Bernstein for real trig polynomials
      trigNorm, trigNorm_sq, trigNorm_add_le            the L^2 norm on the period and Minkowski,
                                                        the latter from the corpus's real
                                                        Cauchy-Schwarz `sq_integral_mul_le`
      trigNorm_le_of_sq_le, trigNorm_deriv_le           pointwise domination and Bernstein in norm form
      trigCayleyStep a F F'                             (1/a)(-(1/2) sin th F + (1 + cos th) F')
      realTrigDeg_trigCayleyStep                        it raises the degree by exactly one
      trigNorm_trigCayleyStep_le                        ‖T F‖ <= (1/a)(1/2 + 2D) ‖F‖

Remaining for (CSHC.20): iterate `trigCayleyStep` `m` times (degree `N + m`, norm factor
`prod_{i<m} (1/a)(1/2 + 2(N+i))`), identify the `m`-fold iterate with the profile of `g^{(m)}`
through `integral_routeUCayleyLift_sq`, and then apply Plancherel
(`MeasureTheory.Lp.norm_fourier_eq`) and Fatou to pass to the limit.
