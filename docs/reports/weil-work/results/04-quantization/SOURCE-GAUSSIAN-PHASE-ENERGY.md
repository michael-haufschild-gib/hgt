# Actual source phase energy at Gaussian scale

Cycle24 paper proof; cycles25–27 formal progress. **Full T24 asymptotic remains
Lean-pending. BRIDGE; independent scientific novelty unestablished. WP04
remains OPEN.** The exact Gaussian phase identity and absolute convergence
are now proved in `WeilWorkQuantizationGaussianPhase.lean`; final direct and
standard-axiom audits passed. Evidence: `gaussian-phase-lean-audit.txt`.
The intended theorem has hW as its only substantive premise. Estimates below
are deductions from that source, not additional assumptions in the capstone.

## Two questions, kept separate

C24 remains UNPROVED: for every hW there is C>0 such that, for T>=2,

    integral_T^(2T) |quantizationTraceF hW (2t)|^2 dt <= C T log T.

Its competing world is an actual full-positive source with this normalized
time energy unbounded. No such source is constructed. Fixed-line Carlson
limits and critical coefficient energy do not settle this alternative.

The actual block-disorder theorem would combine with C24 to give, unless
rigidity holds, cofinally

    integral_T^(2T) |canonicalPhase hW (2t) - c| dt >= a T/log T

for each fixed unit lock c and some a>0. Indeed the existing remainder
factorization gives integral |W-c||F| > eta T. Cauchy--Schwarz and
|W-c|^2<=2|W-c| give eta^2 T^2 < 2 C T log T integral |W-c|.
This is a conditional reduction, not a new unconditional theorem. C24 alone
would still not supply settlement or quantization.

T24 below instead calibrates a signed physical energy directly from the
actual source pole. It does not prove C24, identify physical energy with
coefficient energy, or set the coefficient variance to zero.

## Exact T24 statement

Fix arbitrary hW : WeilPositiveFull lam. Write

- a_n = forwardCoeff lam n = sourceCoeff lam n;
- b = (sourceCompletion hW 1).re;
- F(t) = quantizationTraceF hW t;
- W(t) = canonicalPhase hW t, used only for t>0;
- g_T(t) = exp(-(t/T)^2);
- M(T) = integral_(0,infinity) |F(t)|^2 g_T(t) dt;
- D(T) = integral_(0,infinity) |W(t)-1|^2 |F(t)|^2 g_T(t) dt;
- Ilog = integral_(0,infinity) log u exp(-u^2) du.

All these integrals are absolutely convergent for T>0. There is a real c
with

    sum_(1<=n<=N) a_n/n - b log N -> c,

where the real a_n are identified with their complex embeddings. Moreover
b!=0, and there is C>=0 such that for every T>=2,

    |2 M(T) - D(T) - sqrt(pi) b^2 T log T - A T| <= C T^(7/8),

    A = 2 b^2 Ilog + sqrt(pi) (2 b c - b^2 log(2 pi)).

In particular

    (2 M(T)-D(T))/(T log T) -> sqrt(pi) b^2 > 0.

Thus the actual positive physical energy has a strictly positive T log T
floor. More precisely it is half the calibrated pole contribution plus half
the nonnegative physical phase-defect energy, with a sublinear error. This
does not give an upper bound for M or a vanishing bound for D.

## Source inputs checked in the current corpus

1. `WeilWorkSingularArithmeticForwardCoefficients` proves that a_n is real,
   a_0=0, a_1=1, its Dirichlet series is absolutely convergent on Re s>1,
   and sum_(n<=N) |a_n|^2/n = O(1+log N).
2. `WeilWorkSettledPhaseForwardSummatory.exists_sharp_forward_sum_le`
   gives sum_(n<=N) a_n = beta N + O_epsilon((N+1)^(1/2+epsilon)),
   beta=sourceCompletion hW 1. Reality of a and this limit give Im beta=0.
   `sourceCompletion_one_ne_zero` gives b!=0. The existing ordinary centered
   harmonic limit in `WeilWorkSingularArithmeticForwardMean` agrees with c
   after adding b times Euler's constant.
3. `WeilWorkQuantizationSubpolynomial.exists_quantizationProdF_subpolynomial`
   controls the actual quotient uniformly for 1/2<Re s<=3/2 and |Im s|>=2.
   The radial trace, compact bounds and conjugation are already constructed
   in the RadialBoundary/RadialGrowth leaves. No continuous critical edge is
   required.
   `ZetaChiLeftHalfPlaneGrowth.exists_norm_zetaChi_strip_le` at j=1 supplies
   the uniform polynomial gamma-ratio bound needed for chi(1-s) on these
   tails. Its relevant half-strip branch uses `norm_zetaChi_le_half_strip`.
4. `WeilWorkSettledPhaseCanonicalDisorder` checks the actual reflection law:
   G(t)=W(t)G(-t) almost everywhere for t>0, with G the completed radial trace.
   `canonicalPhase` is exp(i pi mu((-t,t])). It is NOT used at negative t;
   its definition there is not the reflected conjugate phase.
5. `ZetaChiGaussianKernel.integral_zetaChi_mul_cpow_mul_gaussWeight`
   is a gamma-kernel identity, despite the name zetaChi. The factor is
   chi(s)=GammaR(1-s)/GammaR(s). No functional equation of the source enters.
6. `WeilWorkSingularArithmeticGaussianError.exists_weighted_gaussian_kernel_error_le`
   proves, for T>=1 and integer n>0,

       n^(9/8) |leftKernel(T,n)-2 exp(-4 pi^2 n^2/T^2)| <= C0 T^(5/6).

   This kernel statement has no source premise. Absolute summability at
   9/8 pays its use with the convolution a*a as well as with the different
   signed coefficient sequence used in that existing module.

## Dependency-closed paper proof

### 1. Harmonic finite part with a rate

Use epsilon=1/8 in the actual sharp source sum, and extend it from integers
to real x>=1 by taking floors:

    A0(x):=sum_(n<=x) a_n = b x + E(x),   E(x)=O(x^(5/8)).

The floor error is O(1) and is absorbed. Partial summation gives

    sum_(n<=x) a_n/n = A0(x)/x + integral_1^x A0(u)/u^2 du
                      = b log x + c + O(x^(-3/8)),
    c = b + integral_1^infinity E(u)/u^2 du.

The tail is absolutely integrable because 5/8-2<-1. This proves both
existence and the rate, without presuming a Laurent expansion on the edge.

### 2. Summatory convolution, retaining signed coefficients

Put d=a*a and C0(x)=sum_(n<=x) d_n. For m=floor(sqrt x), finite hyperbola
splitting gives exactly

    C0(x)=2 sum_(j<=m) a_j A0(x/j)-A0(m)^2.

There is no coefficient positivity premise. The error in the first term is
bounded by

    O(x^(5/8) sum_(j<=m) |a_j| j^(-5/8)).

Cauchy--Schwarz uses the actual critical square energy:

    sum_(j<=m) |a_j| j^(-5/8)
      <= (sum |a_j|^2/j)^(1/2) (sum j^(-1/4))^(1/2)
      = O(m^(3/8) sqrt(1+log m)).

Consequently that error is O(x^(13/16) sqrt(1+log x)). The harmonic rate
from step1 and the square A0(m)^2 have error O(x^(13/16)); replacing m^2
by x and 2 log m by log x costs O(sqrt x), for x>=4. The bounded initial
interval is absorbed in the constant. Since sqrt(log x)=O(x^(1/16)),

    C0(x)=b^2 x log x+(2 b c-b^2)x+O(x^(7/8)).              (H)

For 0<x<1 the same error bound holds after enlarging the constant, because
C0(x)=0 and x^(1/8)|log x| is bounded. All convolution sums are finite.

### 3. Gaussian summation with the complete error

Let q_T(x)=exp(-(2 pi x/T)^2). Absolute Dirichlet convergence at 9/8 for
a*a implies absolute convergence of sum d_n q_T(n). Summation by parts,
followed by (H), gives

    sum d_n q_T(n)
      = integral_0^infinity (b^2 log x+2 b c) q_T(x) dx
        + O(T^(7/8)).

To verify the error, bound it by a constant times
integral_0^infinity x^(7/8)|q_T'(x)| dx. Substitution x=T u/(2 pi) leaves
T^(7/8) times a fixed finite Gaussian moment. The terms at zero and infinity
vanish; x log x tends to zero at zero. The same substitution in the main
term gives, with I0=sqrt(pi)/2,

    sum d_n q_T(n) = T/(2 pi) *
      [b^2 (log T-log(2 pi)) I0+b^2 Ilog+2 b c I0]
      + O(T^(7/8)).                                        (G)

Ilog is finite: |log u| is integrable near zero, and the Gaussian dominates
log u at infinity. No evaluation of a gamma derivative is needed.

### 4. Exact gamma transform on the absolute line

Let f(s)=prodF(quantizationCompletion hW)(s), so f=the actual Dirichlet
series on Re s>1. For s=3/2+it, expand f(s)^2 using absolute Dirichlet
convolution. Define

    J_right(T)=integral_R chi(1-s) f(s)^2 exp((s-1/2)^2/T^2) dt.

Fubini is justified by sum |d_n| n^(-3/2)<infinity and an integrable
Gaussian times polynomial bound for chi on this line. Applying the corpus
kernel formula, using t -> -t and n^(-s)=n^(-1)n^(1-s), yields exactly

    J_right(T)=2 pi sum_(n>=1) d_n leftKernel(T,n).

The factor n cancels; no n or square-root normalization is omitted. At
integer n, cos(2 pi n)=1. The kernel estimate in input6 and
sum |d_n| n^(-9/8)<infinity now give

    J_right(T)=4 pi sum d_n q_T(n)+O(T^(5/6)).               (K)

This is the reason for Gaussian smoothing: it pays the aggregate error
without a Ramanujan bound, short-interval coefficient estimate, or a
sharp-cutoff Gonek lemma.

### 5. Actual radial passage, avoiding an unpaid pole calculation

For each fixed T>=2, shift the two vertical tails |t|>=2 from Re s=3/2
to Re s=1/2+eta, eta>0. There is no pole in these two rectangles. The
upper/lower outer horizontal segments vanish by the source's uniform
subpolynomial bound and Gaussian decay. The two inner horizontal segments
at t=+/-2 are bounded independently of eta and T>=2: the actual completed
source is bounded there by its right-edge modulus; all denominator factors
are nonzero on these segments; the Gaussian has bounded modulus.

Then send eta down to zero. Radial trace convergence is pointwise. Uniform
source polynomial bounds, gamma-ratio polynomial bounds and the fixed
Gaussian provide one integrable majorant on both tails. Dominated convergence
therefore identifies the literal critical radial trace. Both remaining
vertical compact pieces |t|<=2 have O(1) integrals uniformly for T>=2,
using their actual compact bounds. Thus

    J_boundary(T)=J_right(T)+O(1),                          (C)
    J_boundary(T)=integral_R chi(1-(1/2+it)) F(t)^2 g_T(t) dt.

The O(1) term retains the effect of the pole at s=1. No assertion that the
entire strip is pole-free, no contour crossing without residue, and no
source functional equation is used.

### 6. Identify the actual phase without division by a boundary value

For t>0 outside the already established common null set, G(t)=W(t)G(-t)
and G(-t)=conj G(t). On s=1/2+it the polynomial s(s-1) is real and nonzero.
The gamma factors are nonzero. Multiplication, without dividing by G(t), gives

    chi(1-s) F(t)^2 = W(t)|F(t)|^2.

This remains valid at every admitted trace zero. Conjugation of the actual
trace makes the negative-t integrand the conjugate of the positive-t one.
Consequently

    J_boundary(T)=2 integral_(0,infinity) Re W(t)|F(t)|^2 g_T(t) dt
                 =2 M(T)-D(T),

since |W|=1. Combine (G), (K), and (C); 5/6<7/8. Their main coefficient is
exactly sqrt(pi)b^2 and their linear term exactly A above. This proves T24.

## Novelty and adversarial audit

The parent mechanism is classical gamma-kernel/Gonek analysis and Dirichlet
hyperbola summation. [Conrey--Ghosh--Gonek, Lemmas 1--2](https://sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/simplezeros.pdf)
uses explicit stationary-phase remainders; its sharp-cutoff coefficient
conditions cannot be assumed for this source. The corpus's Gaussian kernel
instead supplies the summable error used here. No novelty is claimed for
those general mechanisms.

The inspected corpus has the native gamma-decaying phase energy formula
`WeilPaperGammaEnergy.paperGammaEnergy_native_phase_formula`; that is a
different finite global energy. T24 calibrates the uncompleted physical
trace at growing Gaussian scale. Corpus searches and exact source reads did
not identify this hW-only two-term calibration. Search coverage is imperfect;
this is an internal bridge claim, not proof of external originality.

Rejected implications:

- Theorem1 of [Brevig--Kouroupis](https://arxiv.org/html/2510.05793v1) assumes
  a uniform horizontal-line/height mean bound; it does not produce C24.
- [Saksman--Seip](https://arxiv.org/pdf/0712.0492) shows that the physical
  boundary orbit need not satisfy the naive Carlson identity. Its bounded
  examples are not counterexamples to the source-specific O(T log T) claim.
- [Defant--Schoolmann](https://arxiv.org/pdf/2107.10145), Theorems1.2 and7.1,
  supplies boundary/local uniform Riesz convergence in specified classes;
  this does not interchange approximation and growing-height averages.
- A signed second moment does not bound its absolute second moment above.
- The actual coefficient law K=b^2+V does not imply that the physical phase
  defect has leading coefficient V. That identification is still unpaid.

## Next gate

Cycle25 Lean map: `quantizationTraceF_phase_ae` and
`quantizationTraceF_square_phase_ae` prove the actual positive-height phase
law at trace zeros as well. The three integrability theorems pay convergence
of M, D and J for every T>0 from hW alone. Exact negative-height conjugation
then gives `quantizationGaussian_signed_energy_complex`: J is the real
embedding of 2M-D. This completes the physical identification in step6,
not the Gaussian asymptotic or any positive-energy upper estimate.

Still required in Lean: harmonic finite-part rate, signed convolution main
term and Gaussian summation. Cycle26 closes the absolute-line kernel
extraction in GaussianExtraction, with all twelve public declarations and
dependency closures audited; see gaussian-extraction-lean-audit.txt.
GaussianShift also passes its final direct audit for the exact residue
shift, dominated critical-boundary passage and physical energy-kernel
formula. All nine public declarations and their dependency closures use only standard
axioms; see gaussian-shift-lean-audit.txt. The same scratch audit verifies
gaussWeight(T,1)=exp(1/(4*T^2)), including its exact normalization. The corpus already has `sum_Icc_mul_apply_add_sqrt_prefix_sq` for
arbitrary real arithmetic weights; do not rebuild its combinatorial proof.
Its source statement was inspected; its use still needs a toolchain check.

Cycle25 SOTA update: [Brevig--Kouroupis, 28 September 2026](https://arxiv.org/html/2609.35496v1),
Theorem1 and Corollary2, replace bounded continuation by order-zero
continuation for the iterated Hardy-space mean formula. This does not close
C25: the critical coefficient row has divergent squared norm, and the
Mellin approximation estimate in their proof loses the reciprocal horizontal
gap. My applicability audit: choosing a gap of size 1/log T does not supply
decay with a fixed admissible smoothing exponent; source subpolynomial
constants are not uniform as that exponent tends to zero. Neither a joint
boundary/height limit nor the actual physical coefficient constant follows.

Formalize exactly T24, including (H), (G), (K), (C), the zero-safe phase
identity and the final hW-only statement. Keep its leaves within
WeilWorkQuantization*.lean. Read/check names in scratch Lean before using
them; final audits are direct foreground `lake --old env lean` on leaves.
No full or umbrella build. No isolated generic lemma is a completed T24.

After that, test the stronger physical calibration

    M(T)/(T log T) -> sqrt(pi) K/2,

where K is the already-proved coefficient-energy constant. Together with
T24 this would identify D(T)/(T log T) with sqrt(pi)V. It is a new OPEN
conjecture here, not a paper consequence. Even V=0 at this leading scale
would not itself pay the existing rigidity receiver's o(T) weighted error.

## Cycle26 stronger contour theorem T25 — compiled

The extraction formalization exposes a sharper form of (C). For the same
actual source and every T>=1, with beta=quantizationCompletion(hW)(1),

    J(T) = Jright(T) + pi*beta^2*exp(1/(4*T^2))
         = 2*pi*sum_n d_n*leftKernel(T,n)
           + pi*beta^2*exp(1/(4*T^2)).                 (T25)

All equalities here are complex equalities; beta is the actual real source
residue, not an assumed normalization. T25 is paper-proved below and compiled in GaussianShift, including its
critical-boundary passage. Its mechanism is classical
residue calculus, so the novelty verdict remains BRIDGE. The corpus's
`sourceZetaPairing_gaussian_shift` treats the different coefficient sequence
(lambda-Lambda)*1*1 and cannot be substituted for this squared-source result.
The two cycle26 deep searches and inspected source definitions found no
already-applicable declaration for T25; coverage limitations are retained.

1. Put A(s)=G(s)/(s*Gamma_R(s)), where G is the actual completion. A is
   holomorphic for Re(s)>1/2, A(1)=beta, and f(s)=A(s)/(s-1) away from one.
   The function chi(1-s) is holomorphic on this half-plane: its numerator
   Gamma_R(s) has no pole there and its reciprocal-Gamma denominator is
   entire. Thus chi(1-s)*f(s)^2 is holomorphic away from one.
2. Let p(s)=(s-1)*zeta(s), extended by p(1)=1. This is holomorphic and
   nonzero in a neighborhood of one. The functional equation gives, on
   that punctured neighborhood,

       (s-1)*chi(1-s)*f(s)^2 = A(s)^2*zeta(1-s)/p(s).

   Taking s->1 gives -beta^2/2, since zeta(0)=-1/2. This computes the
   residue without assuming nonvanishing of zeta on an entire strip.
3. Multiply by exp((s-1/2)^2/T^2). The only enclosed pole when shifting
   from 3/2 to a=1/2+eta, 0<eta<1/4, has residue
   -beta^2*exp(1/(4*T^2))/2. The actual source subpolynomial bound,
   the corpus chi strip bound and Gaussian suppression kill both outer
   horizontal segments. Both vertical lines are absolutely integrable.
   The oriented rectangle formula is Jright-Ja=2*pi*residue; hence
   Ja=Jright+pi*beta^2*exp(1/(4*T^2)). The sign is fixed by this orientation.
4. Pass eta->0 for fixed T. On |t|>=2, the uniform open-strip source bound
   and chi polynomial bound give one integrable polynomial-Gaussian
   majorant. On |t|<=2, `quantizationRightMajorant` is continuous on the
   compact rectangle 1/2<=Re(s)<=3/4 and dominates |f(s)|; chi and the
   Gaussian are continuous and bounded there. These bounds square to a
   common integrable majorant. The actual pointwise radial trace limit
   gives Ja->J(T), including trace zeros and discontinuities. No continuous
   boundary extension, phase representation or physical mean-square
   estimate is assumed.
5. The now-compiled absolute-line extraction identifies Jright with the
   convergent kernel sum. The compiled Gaussian phase identity identifies
   J with 2M-D. This proves the paper statement T25. Its bounded residue
   correction implies the older (C), but does not imply C24 or C25.

All four T25 obligations are compiled: the actual pole computation,
uniform Gaussian strip decay, the simple-pole line shift, and dominated
radial passage for the literal squared integrand. The capstones are
quantizationGaussian_boundary_shift, quantizationGaussian_energy_kernel,
and quantizationGaussian_energy_extraction. They use only the specified
hW and the numerical scale range. No source regularity, sign, coefficient
normalization or critical mean-square premise is added.

The physical extraction error is O(T^(5/6)) after retaining the exact polar
correction. T24 still needs the harmonic finite-part rate, convolution main
term and Gaussian coefficient asymptotic. T25 does not prove an upper bound
for M, vanishing D, variance zero, or the common-endpoint quantization law.

## Cycle27: harmonic finite part and a shorter Gaussian main

The integer version of step(H) is compiled in
`WeilWorkQuantizationHarmonicFinitePart.lean`. Its fixed real constant is

    c = Re dirichletSum(n -> a_(n+1)-beta, 1) + b*EulerGamma.

Convergence at 5/8 gives a bounded sequence of centered Dirichlet partial
sums there. `norm_dirichletSum_sub_partialSum_le`, shifted to 1, bounds
the harmonic tail by 4C(N+1)^(-3/8). The exact coefficient identity and
0 < harmonic(N)-log(N)-EulerGamma < 1/N give the claimed rate and limit.
This reuses the corpus's quantitative Abel theorem; it is classical and
is not a separate scientific novelty claim. The real-floor extension also
passed its final direct and axiom audits. Step(H) is fully formalized.
The LaurentFinitePart leaf identifies this same c with the actual source
regular part at1, preserving the regular part's source-only strip bounds.

### T26: Gaussian convolution main by Mellin inversion

This is a replacement for the hyperbola route when the desired output is
the Gaussian sum itself. For the same specified hW, literal d=a*a, b and c,
put Q(T)=sum_(n>=1) d_n exp(-(2*pi*n/T)^2). For every fixed theta with
1/2<theta<1, the exact paper statement is

    Q(T) = T/(2*pi) *
      [sqrt(pi)*b^2/2 * log(T/(2*pi)) + sqrt(pi)*b*c + b^2*Ilog]
      + O_(hW,theta)(T^theta),                         T>=1.

The values and error are complex, with the displayed main term real.
Thus T25 and the compiled kernel error imply the physical T24 expansion
with O(T^(5/6)), stronger than its original O(T^(7/8)). The exact bounded
polar term from T25 can either be retained or absorbed. No claim of Lean
completion is made for T26 or this improved physical asymptotic.

**Attack and verdict: BRIDGE.** This is classical Mellin singularity
analysis applied to the actual source, not a new parent theory. The
Flajolet--Gourdon--Dumas converse-mapping theorem (1995, Theorem4) includes
the mechanism; its introduction already discusses Gaussian divisor sums.
The new corpus search found no returned theorem for this literal source.
An arbitrary-function contour statement does not discharge its source
bounds. No physical mean-square upper estimate follows from this signed
moment. Failure could only occur at an unpaid analytic/inversion/constant
identification step; each is supplied in the following paper proof.

**Dependency-closed paper proof.** Write F(s)=prodF(quantizationCompletion hW,s).
The actual source results give: (i) F=sum a_n n^(-s) absolutely for Re(s)>1;
(ii) F is holomorphic in Re(s)>1/2 except its simple pole at1, with residue
beta; (iii) F has a uniform polynomial bound on every closed vertical
strip theta<=Re(s)<=3/2 away from a compact neighborhood of1. The compiled
subpolynomial theorem is stronger than (iii). Reality of a_n and
sourceCompletion_conj at1 give beta=b real.

The centered ordinary Dirichlet sum A(s)=sum (a_n-beta)n^(-s) is
holomorphic for Re(s)>1/2: for each point select a strictly smaller real
abscissa above1/2 and use the corpus's locally uniform Abel convergence.
For Re(s)>1, absolute convergence gives A(s)=F(s)-beta*zeta(s).
Analytic uniqueness extends this identity through the punctured connected
half-plane. Since zeta(s)=1/(s-1)+EulerGamma+O(s-1), one obtains

    F(s)=b/(s-1)+c+O(s-1),

where A(1) is real (all centered finite sums are real), and c is exactly
the fixed constant in the compiled harmonic theorem. There is no new
choice of finite part. Mathlib's riemannZeta_0 and its value at1 provide
the zeta regularization in this toolchain.

Set X=T/(2*pi). Mellin inversion of exp(-u^2) on Re(s)=3/2 and absolute
convergence of sum |d_n|n^(-3/2) give

    Q(T) = (1/(2*pi*i)) integral_(3/2)
             X^s * Gamma(s/2)/2 * F(s)^2 ds.

The interchange is absolute: the norm of (X/n)^s on that line equals
(X/n)^(3/2), while Gamma(s/2) is integrable. The n=0 coefficient is zero.
The Gaussian Mellin transform is obtained from Euler's Gamma integral by
v=u^2; its inverse follows from ordinary Mellin inversion. Continuity is
immediate for the single Gaussian kernel. Thus no convergence of a
critical Dirichlet series is used in this step.

On theta<=Re(s)<=3/2, Gamma(s/2) has exponential vertical decay times a
fixed polynomial (Stirling on this positive strip). Combined with (iii),
both horizontal integrals tend to zero. Only the double pole at1 is
crossed; Gamma has no pole on this strip. The integral on Re(s)=theta is
bounded by X^theta times the finite, T-independent integral of
|Gamma((theta+it)/2)F(theta+it)^2|/2. Hence its error is O(T^theta), uniformly
for all T>=1. Constants depend on the specified hW and fixed theta.

Let H(s)=Gamma(s/2)/2. Its integral representation yields H(1)=sqrt(pi)/2
and H'(1)=Ilog. Differentiation under that integral is justified on any
small closed neighborhood of1 by integrability of
(u^(-epsilon)+u^epsilon)*|log u|*exp(-u^2). Expanding X^s H(s) F(s)^2 at1
gives the residue

    X * [H(1)b^2 log X + 2H(1)bc + H'(1)b^2].

This is the displayed main term. Take theta=3/4. The already compiled
physical extraction differs from 4*pi*Q(T) plus the exact bounded polar
term by O(T^(5/6)). Since T^(3/4)<=T^(5/6) for T>=1, the resulting physical
error is O(T^(5/6)). Its two main coefficients agree term-for-term with
T24. This completes the paper proof of T26 and the strengthened T24.

**Formalization decision.** H and its Laurent identification are compiled.
Use this Mellin route for the Gaussian main. Do not formalize a large signed
hyperbola argument merely because it was the first paper proof. Existing
generic ingredients include `mellinInv_mellin_eq`,
`mellinInv_line_Gamma_eq_exp_neg`, `differentiableOn_dirichletSum`,
`differentiable_riemannZeta₀`, and the actual source subpolynomial bounds.
Cycle28 compiled the squared-source Mellin inversion and absolute
integrability in WeilWorkQuantizationGaussianMellin.lean, for every
positive scale and every absolute line c>1. All nine public declarations
have clean direct/API/standard-axiom audits. The double-pole shift and
normalized main still need Lean proofs; the simple-pole T25 theorem alone
does not supply them. Corpus search located rectIntegral_div_sub_sq_eq_deriv
in HTGeometry/RectangleDerivativeFormula.lean for the rectangle step.
C24/C25, variance zero and WP04 remain OPEN. The next physical
reformulation T27 and hard source conjecture C28 are in
CENTERED-PHASE-ENERGY.md; neither has a Lean theorem yet. That file now
also contains complete paper proofs T28/T29: actual Gaussian coefficient
recovery, a rigidity-or-linear-energy alternative, and the quantitative
physical lower comparison with the source coefficient variance. Prioritize
that pole-free comparison before normalizing further Mellin main constants.

Primary parent: [Flajolet, Gourdon and Dumas (1995), Theorem4 and Section3](https://specfun.inria.fr/dumas/Publications/FlGoDu95.pdf).
