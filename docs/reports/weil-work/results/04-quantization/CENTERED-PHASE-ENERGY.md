# Phase defect as actual pole-centered energy

Cycle31. All three T28 assertions are compiled. T27/T29 remain in formal integration. C28/C30/C31: OPEN.
Verdict for T27: **BRIDGE**; independent scientific novelty unestablished.
WP04 remains OPEN. No additional source hypothesis is introduced.

Cycle31 external parent check: Broucke--Hilberdink's Appendix B supplies
the classical finite Bessel mechanism. It does not supply our source upper
bound. [Saksman--Seip](https://arxiv.org/pdf/0712.0492), Theorem1 and its
two-prime construction, shows that bounded ordinary Dirichlet series can
fail to have a boundary mean; small coefficient square norm also need not
control the actual boundary mean. Their exponential construction is
zero-free. Thus finite-prime dependence and nonvanishing alone do not pay
the missing boundary identity. This is not a counterexample satisfying hW.
[Brevig--Kouroupis--Perfekt](https://arxiv.org/html/2405.03522) likewise
distinguishes generalized boundary values and warns against interchanging
the relevant mean/vertical limits. We retain the actual Gaussian trace
and explicit finite Gram matrix, with no assumed limiting mean.

## Exact statements

Fix hW : WeilPositiveFull lam. Let b=Re(sourceCompletion hW 1),
F(t)=quantizationTraceF hW t, Z(t)=riemannZeta(1/2+it), and
g_T(t)=exp(-(t/T)^2). Use the actual positive-height canonical phase W.
The residue beta is real by sourceCompletion_conj at1, so beta=b.
Define

    E(T) = integral_(0,infinity) |F(t)-b Z(t)|^2 g_T(t) dt,
    D(T) = quantizationGaussianDefect hW T.

**T27.** There exists C>=0, depending only on the specified hW, such that
for all T>=1,

    |2 E(T)-D(T)| <= C T^(5/6).

Every integral is absolutely convergent. Consequently E(T)=o(T) if and
only if D(T)=o(T); similarly their normalized T log T limits differ by a
factor of two whenever either limit exists. T27 proves neither vanishing
nor existence of either leading limit.

**C28, the next hard source conjecture.** For every specified hW,

    E(T)/T -> 0 as T -> infinity.

No B2 representative, phase representation, coefficient-variance bound,
or exchange of limits is part of this conjecture. Its competing world is
a full-positive integer-supported source retaining positive or unbounded
mean-square distance from its pole-matched zeta function. This is a
statement about the literal physical trace. Generic holomorphic functions
can have such a distance; the integer-supported Weil source must do the
work. This asks for o(T) control where C25 asks for a leading T log T
law; C25's coefficient identification alone does not imply it.

## Attack before proof

The corpus's centered harmonic convergence concerns ordinary Dirichlet
sums in the open half-plane. It supplies no boundary mean-square limit.
Its finite Dirichlet-polynomial mean-value theorem supplies no approximation
of this actual infinite trace. T23 makes the phase-resonance functional
unbounded on abstract B2, so an abstract null representative is insufficient.
The resonance theorem inspected in this audit is a radial pair-kernel
limit, not the fixed-frequency physical Cesaro coefficient theorem.

The actual critical coefficient energy is logarithmically divergent.
Brevig--Kouroupis (2026) assumes square-summable coefficients and concludes
an iterated fixed-line mean identity. It does not establish C28. The
mixed-moment search returned automorphic/Dirichlet-character families,
whose realization hypotheses are absent for a general hW.

T27's mechanism is Gaussian extraction, pole cancellation and polarization.
The Mellin parent is classical. Its significance inside this investigation
is identifying the phase cost with one concrete positive physical error;
there is no scientific novelty claim based only on not finding an exact hit.
C28 survives this preliminary attack but has no paper proof or Lean theorem.

## Dependency-closed paper proof of T27

1. Put A(s)=F_int(s)-b*zeta(s), with F_int the literal decompleted source
   in Re(s)>1/2. The source has its only pole there at1, with residue b;
   zeta has residue1. Thus A extends holomorphically across1. More explicitly,
   the existing source regular part R and the entire regularized zeta
   zeta_0 give A=R-b*zeta_0. Equality first holds for Re(s)>1 and then by
   analytic uniqueness on the punctured connected half-plane. This
   extension has polynomial growth on every closed inner strip: use the
   actual source subpolynomial bound and
   `exists_bound_norm_riemannZeta_strip`. No RH or Lindelof bound for zeta
   is used.

2. On Re(s)>1 its coefficients are u_n=a_n-b for n>=1, with u_0=0.
   The series is absolutely convergent there. Hence A(s)^2 has the literal
   convolution d=u*u, absolutely convergent on the same half-plane and in
   particular at9/8. This d differs from both a*a and the other package's
   (lambda-Lambda)*1*1. The coefficient at zero vanishes.

3. For T>0, the critical boundary of A is exactly F(t)-bZ(t). Source radial
   convergence and continuity of zeta give this pointwise. On compact
   intervals the existing source radial majorant plus continuous zeta
   dominates it uniformly; on tails, their polynomial bounds and the
   Gaussian give an integrable majorant. Therefore the critical squared
   chi moment is the radial limit of its interior line integrals. Negative
   heights are complex conjugates of positive heights.

4. Shift chi(1-s) A(s)^2 exp((s-1/2)^2/T^2) from the critical boundary to
   Re(s)=3/2. There is no pole: A is holomorphic and
   chi(1-s)=GammaR(s)/GammaR(1-s) is holomorphic for Re(s)>1/2 (the inverse
   Gamma factor is entire). Polynomial strip bounds and Gaussian decay
   kill the two horizontal ends; step3 pays the radial limit. The generic
   Gaussian kernel identity and absolute convergence of d give

       J_A(T) = 2*pi sum_n d_n leftKernel(T,n).

   The corpus's weighted kernel error at9/8, multiplied by
   sum |d_n| n^(-9/8), gives

       J_A(T) = 4*pi sum_n d_n exp(-(2*pi*n/T)^2) + O(T^(5/6)).

5. The Mellin inversion argument of T26 applies to A^2. Here
   Gamma(s/2) A(s)^2/2 has no pole between any fixed theta in (1/2,1)
   and3/2. Its vertical decay is exponential times a polynomial. Therefore
   the coefficient Gaussian sum is O(T^theta), with a constant independent
   of T>=1. Take theta=3/4 and absorb it into T^(5/6). Thus
   |J_A(T)|<=C T^(5/6). This step uses an unshifted, absolutely convergent
   Mellin inversion and an ordinary pole-free contour shift; it assumes
   no physical mean estimate.

6. Write chi_t=chi(1-(1/2+it)). The unconditional zeta functional equation
   gives chi_t Z(t)=conj Z(t), including zeta zeros. The compiled source
   phase identity gives

       Re(chi_t F(t)^2)
         = |F(t)|^2 - |W(t)-1|^2 |F(t)|^2/2

   for almost every t>0. Since b is real, direct expansion, without dividing
   by either trace, gives

       Re(chi_t (F(t)-bZ(t))^2)
         = |F(t)-bZ(t)|^2 - |W(t)-1|^2 |F(t)|^2/2.

   Gaussian integrability and conjugation across zero now yield the exact
   complex identity J_A(T)=2E(T)-D(T). Step5 proves T27.

The argument exposes the real open issue: positivity of E and D only
compares them; it does not make either small. C28's first [OPEN CORE] is
source-only control of E(T)=o(T). A proof must use more than fixed-line
Dirichlet convergence or an abstract almost-periodic representative.

## Next formal obligations

Finish T26's literal Mellin extraction and main, reusing the now-identified
harmonic/Laurent constant. Reuse that proof for A with no polar term, then
formalize T27's exact positive-energy identity. Keep C28's zero-mean source
estimate separate. If using C28 as a quantization receiver, first prove
the actual fixed-frequency Cesaro coefficient transfer and its arithmetic
rigidity consequence; do not substitute the existing radial resonance law.

Primary scope checks: [Brevig--Kouroupis, 2026](https://arxiv.org/html/2609.35496v1),
[Flajolet--Gourdon--Dumas, 1995](https://specfun.inria.fr/dumas/Publications/FlGoDu95.pdf),
[Kaneko, mixed moments](https://arxiv.org/abs/2109.12495),
[Balkanova--Frolenkov, 2023](https://ddd.uab.cat/pub/pubmat/pubmat_a2023v67n2/pubmat_a2023v67n2p611.pdf).

## Cycle28: T28, coefficient recovery from the actual trace

T28 has a dependency-closed paper proof below. Assertions1/3 are compiled
in GaussianRecovery/GaussianCoefficientLimit/GaussianEnergy; assertion2
is compiled in GaussianGram/GaussianBessel. It fills
the coefficient-transfer obligation above. Verdict **BRIDGE**, with no
independent scientific novelty claim. It does not prove C28.

Retain A(t)=F(t)-b*zeta(1/2+it), u_n=a_n-b for n>=1, u_0=0.
For each fixed integer n>=1 and T>0, put

    B_n(T) = (T sqrt(pi))^(-1) integral_R
               A(t) exp(i t log n) exp(-(t/T)^2) dt.

The exact assertions, for every specified hW, are:

1. B_n(T) -> u_n/sqrt(n) as T -> infinity.
2. For every finite S subset {1,2,...} and epsilon>0, eventually

       2 E(T)/(T sqrt(pi)) >= sum_(n in S) |u_n|^2/n - epsilon.

3. Either lambda=Lambda on n>=2 and RH, or there exist kappa>0 and T0
   such that E(T)>=kappa*T for every T>=T0.

Consequently C28 implies the required arithmetic rigidity and RH. It is
enough even to have arbitrarily large scales at which E(T)/T tends to zero.
This is an actual-source conclusion; no abstract B2 representative is used.

### Attack and complete paper proof

The source polynomial growth and absolute right-half-plane Dirichlet series
do not by themselves bound E from above. A nonzero Dirichlet polynomial
already exhibits a positive linear Gaussian energy. The conclusion must
retain that alternative. The classical Bessel mechanism is explicitly
present in Broucke--Hilberdink (2024), Appendix B. Their mean theorem has
coefficient-sign and counting assumptions absent here. Our Gaussian contour
argument below uses the already-paid source continuation and radial bounds
to reach its literal critical trace; it does not apply their mean theorem.

By steps1--3 of T27, A(s)=F_int(s)-b*zeta(s) is holomorphic on Re(s)>1/2,
including1, and has polynomial vertical growth on every strip ending at3/2.
Uniform growth down to the critical boundary follows by combining the
compiled source radial compact/tail majorants with the unconditional zeta
strip bound. Its actual boundary is A(t). The coefficients u_n are real,
and sum |u_n| n^(-3/2) converges. All Gaussian integrals below converge
absolutely. Real coefficients and conjugation give |A(-t)|=|A(t)|.

Fix n and T. Shift the entire-in-strip integrand

    n^(s-1/2) A(s) exp((s-1/2)^2/T^2)

from Re(s)=1/2+eta to3/2. No pole remains. Polynomial bounds multiplied
by exp(-y^2/T^2) kill both horizontal edges as |y| tends to infinity.
Then let eta decrease to zero; the uniform radial majorants justify
dominated convergence. With the dt normalization, both vertical integrals
are equal. On the right line, interchange the absolutely convergent
Dirichlet series and integral, dominated by

    n exp(1/T^2) sum_m |u_m| m^(-3/2) exp(-t^2/T^2).

The Gaussian Fourier integral now gives the exact absolutely convergent sum

    B_n(T) = n sum_(m>=1) u_m m^(-3/2)
      exp(1/T^2 - (T log(n/m) + 2/T)^2/4)
           = sum_(m>=1) (u_m/sqrt(m))
               exp(-T^2 log(n/m)^2/4).

The first representation, not a presumed critical absolute series, pays
the limit. For T>=1 each summand is bounded in modulus by
e*n*|u_m|*m^(-3/2). Its pointwise limit is zero for m!=n and u_n/sqrt(n)
for m=n. Dominated convergence for this summable majorant proves assertion1.
The second representation is an exact simplification, not an unweighted
boundary Dirichlet expansion. In particular no T-dependent critical
truncation or exchange with a boundary limit is hidden here.

Use the probability measure dnu_T=exp(-(t/T)^2)dt/(T sqrt(pi)). For a fixed
finite S put P_S(t)=sum_(n in S) (u_n/sqrt(n)) exp(-i t log n).
Assertion1 gives

    integral A(t) conjugate(P_S(t)) dnu_T -> sum_(n in S) |u_n|^2/n.

The Gaussian Fourier formula gives the same limit for integral |P_S|^2:
all distinct log frequencies have exponentially vanishing cross terms.
Expand the nonnegative integral |A-P_S|^2 and retain the resulting lower
bound for integral |A|^2=2E(T)/(T sqrt(pi)). This proves assertion2,
without assuming the existence or finiteness of any limiting energy.

If every u_n is zero, a_1=1 forces b=1, hence every positive-index source
coefficient is1. The existing vonMangoldt_and_RH_of_coeff_eq_one applies:
its summability, continuation, derivative and normalization premises are
all supplied by hW, as already assembled in the quantization package.
Otherwise fix n with u_n!=0, take S={n} and
epsilon=|u_n|^2/(2n). Assertion2 yields the explicit eventual lower bound

    E(T) >= sqrt(pi)*|u_n|^2/(4n) * T.

This proves assertion3 and the C28 receiver. Conversely, coefficient
rigidity identifies F_int=zeta by its absolute Dirichlet series and
analytic uniqueness; radial limits give A(t)=0 and E(T)=0. Thus C28 is
an exact physical rigidity target, not a weaker upper estimate already
supplied by the signed moment.

### What remains hard

C28 still needs a source-only upper bound beating a positive multiple of T.
T28 supplies a lower obstruction and pays its actual coefficient transfer;
it cannot remove its own nonrigid alternative. T27 would also turn that
alternative into an eventual linear phase-defect lower bound. Neither
statement supplies the common full-measure endpoint set. Formalize the
finite-set T28 bound and T29 using the compiled Gaussian coefficient recovery
and energy comparison. The source-only alternative is already compiled;
the finite-set and quantitative paper bounds are not.

Primary parent audit: [Broucke--Hilberdink (2024), Appendix B](https://arxiv.org/html/2409.06301v1#Sx1).
The September2026 [Fejer--Riesz inequality](https://arxiv.org/abs/2609.03855)
and [Dirichlet-group Riesz means](https://arxiv.org/abs/1908.06458) concern
Hardy-space inputs; no such source-space membership was inferred here.

### Cycle30: direct one-frequency energy inequality

The following closed proof pays assertion3 without waiting for the finite
Gram-matrix formalization of assertion2. It is the one-frequency case of
the same classical argument, not a new scientific conjecture.

Write g_T(t)=exp(-t^2/T^2), M_T=T sqrt(pi)>0. The already-proved linear
bound on the actual centered trace makes |A|^2 g_T integrable. The
inequality |A|<=|A|^2+1 makes each twisted A g_T integrable too. Conjugation
of the actual source and zeta, and reality of beta, give A(-t)=conj A(t).
Thus the whole-line energy equals 2E(T), and integral g_T=M_T.

For any real frequency ell, let B=M_T^-1 integral exp(i ell t) A(t) g_T(t).
Pointwise Young's inequality gives

    2 Re(conj B exp(i ell t) A(t)) g_T(t)
      <= |A(t)|^2 g_T(t) + |B|^2 g_T(t).

All three terms are integrable by the bounds just established. Integration
gives 2 M_T |B|^2 <= 2E(T)+M_T|B|^2, hence

    |B|^2 <= 2E(T)/M_T.

At ell=log(n), compiled coefficient recovery gives |B|^2 -> q=|u_n/sqrt(n)|^2.
If u_n!=0, q>0 and eventually |B|^2>q/2. Therefore eventually
E(T)>=sqrt(pi)q T/4. If all positive-index u_n vanish, a_1=1 gives beta=1
and all a_n=1; the existing exact coefficient-rigidity assembly supplies
lambda=Lambda and RH from hW. No physical limiting mean is assumed. The
finite-set lower bound and its quantitative T29 strengthening still need
their separate formal Gram-matrix argument.

## T29: the coefficient variance forces the physical logarithmic lower bound

T29 is a stronger statement exposed by the T28 proof. Dependency-closed
paper proof follows; Lean pending. Verdict **BRIDGE**: Gaussian coefficient
recovery and Bessel are classical. The contribution here is the literal
source comparison, not a new general mean-value method.

Let B=sum_(m>=1)|u_m|m^(-3/2), finite by source absolute convergence.
For every integer N>=1 and real T>=1,

    2 E(T)/(T sqrt(pi)) >= sum_(n=1)^N |u_n|^2/n
       - (2 exp(2)+1) B^2 N^4 exp(-T^2/(32N^2)).             (Q)

In particular, for the already compiled source variance V and K=b^2+V,

    liminf_(T->infinity) 2 E(T)/(sqrt(pi) T log T) >= V.

Here liminf can be expressed without extended-value conventions: for
every epsilon>0 the ratio is eventually at least V-epsilon. Combining
the paper-proven T27 and T24 gives the two physical lower comparisons

    liminf D(T)/(sqrt(pi) T log T) >= V,
    liminf 2 M(T)/(sqrt(pi) T log T) >= K.

These are lower bounds, with no assertion of finite limsup, existence of
the physical limits, equality, or V=0. The last two conclusions depend
on T27/T24, whose full asymptotics are still not compiled.

### Quantitative proof and attack

For 1<=n<=N and m!=n, integer separation gives
|log(n/m)|>=1/(2N). Indeed, for m>n use
log(m/n)>=log(1+1/n)>=1/(n+1); for m<n use
log(n/m)>=log(1+1/m)>=1/(m+1)>=1/n.
The inequality log(1+x)>=x/(1+x), x>=0, follows by integrating
1/(1+t) on [0,x]. Thus this step uses exact integer support.

For real L, (T L+2/T)^2>=T^2 L^2/2-4/T^2. In T28's first exact
series, each off-diagonal summand is therefore bounded by

    exp(2) n |u_m| m^(-3/2) exp(-T^2/(32N^2)),

since T>=1. The diagonal term is exactly c_n=u_n/sqrt(n). Put
q=exp(-T^2/(32N^2)). Uniformly for n<=N,

    |B_n(T)-c_n| <= exp(2) B N q.

Also |c_n|<=B n, so sum_(n<=N)|c_n|<=B N^2. For the finite
polynomial P_N=sum c_n exp(-it log n), its Gaussian Gram matrix has
diagonal1 and every off-diagonal entry at most
exp(-T^2/(16N^2))<=q. Hence

    integral |P_N|^2 dnu_T <= sum |c_n|^2 + B^2 N^4 q,
    Re integral A conjugate(P_N) dnu_T
      >= sum |c_n|^2 - exp(2) B^2 N^3 q.

Expand integral |A-P_N|^2>=0, combine these estimates, and use N^3<=N^4.
This proves (Q). All sums involving P_N are finite. The only infinite
interchange is T28's absolutely convergent right-line series, already paid.
No assumption that u_n has one sign, or that A belongs to a critical Hardy
or Besicovitch space, enters the argument.

Fix 0<delta<1 and let N=floor(T^delta). For sufficiently large T,
T^delta/2<=N<=T^delta. Consequently log N/log T->delta, while
N^4 q <= T^(4delta) exp(-T^(2-2delta)/32)->0. Exponential decay against
every power pays this last limit. The corpus theorem
exists_forwardCoeff_energy_variance, together with
forwardCoeff_eq_sourceCoeff and reality of beta, gives

    (sum_(n<=N)|u_n|^2/n)/log T -> delta V.

Divide (Q) by log T. The eventual lower bound is delta V-epsilon for
every epsilon>0. Taking delta arbitrarily close to1 proves the stated
V lower bound; for V=0 it follows directly from E>=0. T27 has error
O(T^(5/6)), and T24 has the signed leading term sqrt(pi)b^2 T log T.
Their normalized errors vanish, proving the stated D and M comparisons.

The sharp limitation is visible: none of these inequalities bounds the
energy above. Exact coefficient recovery allows mass to escape to higher
frequencies as T grows. A matching source upper bound must rule out that
escape. Thus the next source conjecture is C25's upper half:

    for every epsilon>0, eventually
      2 M(T)/(sqrt(pi) T log T) <= K+epsilon.               (C25-upper)

T29 would make this sufficient for the full C25 physical/coefficient
identification, but not for V=0 or C28. This refines an existing conjecture,
not a new theorem. The hardest target remains eliminating positive centered
physical energy from the full-cone arithmetic source.

### Centering the source recurrence does not close the upper bound

A fresh full-corpus query and the proof of
exists_forwardCoeff_log_moment_le were inspected. The latter uses the
uncentered convolution identity lambda*a=(log n)*a_n. If
Delta_n=sum_(d|n,d>=2)lambda_d-log n, the exact centered recurrence is

    (lambda*u)_n = (log n) u_n - b Delta_n,  n>=1.

Applying the Toeplitz form to u retains the forcing correlation with
Delta_n; dropping it is invalid. The compiled logarithmic variance limit
and coprime-covariance budget do not make that term vanish. No centered
upper estimate or variance-zero assertion has been inferred from them.

Plan revision: after the audited scalar/source Mellin leaf, prioritize
the pole-free actual Gaussian coefficient identity T28 and the quantitative
physical lower comparison T29. Reuse existing contour/radial machinery.
Keep T26's double-pole main and T27 formalization pending explicitly;
do not delay the actual mean comparison solely to normalize main constants.

## Cycle29: actual centered source and boundary contour

`WeilWorkQuantizationCenteredSource` now has a clean direct Lean audit.
The source used in T28 is defined explicitly by the divided difference
of G(s)/(s Gamma_R(s)), minus b zeta_0(s). This fills s=1, gives exactly
F(s)-b zeta(s) away from one, identifies its coefficients u_n, and supplies
one linear radial bound down to the actual critical trace. No continuity
of the original completion on the critical boundary is assumed.
`WeilWorkQuantizationCenteredGaussian` also passed its clean direct audit
for the actual residue-free Fourier-Gaussian boundary shift. T28's coefficient extraction,
limit, and Bessel conclusion are not yet claimed as formalized.

Hard-core attack: the existing complex-power self-pairing is restricted
to Re(1/z)>1/2 and gives exponent alpha(z)=1/(2 Re(1/z)-1), with a
source- and z-dependent constant. For real 0<r<2 this is r/(2-r).
Consequently the proposed shortcut “vary the power near r=1 and force
centered variance to vanish” is unsupported: exponent control does not
control the limiting energy constant, and no uniformity in r is supplied.
This attack is rejected as a proof, not declared a counterexample to C28.
The nontrivial surviving input is already in the corpus's PowerEnergy
and ForwardVariance modules; no duplicate theorem or novelty claim.

External comparison on 2026-10-08: Ramachandra's 1974 paper uses the
functional equation in the crucial contour step and separate moment
estimates for the mean-value conclusions. Suzuki's screw-function
positivity concerns the specified zeta spectral data. Neither inspected
argument supplies C28 for our arbitrary full-positive arithmetic source.
The Gaussian extraction/Bessel mechanism is classical (BRIDGE).
Sources: https://www.numdam.org/article/ASNSP_1974_4_1_1-2_81_0.pdf ;
https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/jlms.12785 ;
https://arxiv.org/html/2409.06301v1 (Appendix Bessel comparison).
Exact internal search coverage is retained in cycle29-search-evidence.json;
the power-specific deep search is partial, and no absence claim follows.

Further attack on C25-upper: an ordinary smoothed Dirichlet truncation
cannot currently cross the physical critical line. At a radial point
s=1/2+eta+it, shifting the smoothing variable while keeping s+w in the
proved holomorphic region only gives a tail factor X^(-eta+delta),
0<delta<eta. It degenerates as eta tends to zero. Taking a polynomial
X=T^A therefore supplies no uniform vanishing radial error. The actual
centered source is pole-free at one, but no continuation left of 1/2 has
been proved. Thus the proposed truncation proof of C25-upper stops at
this specific uniform tail estimate; it cannot borrow a functional
equation for A. The surviving T28 Fourier identity shifts right from the
boundary and avoids that unsupported crossing entirely. This is a
mechanism audit, not a new counterexample or a retirement of C25-upper.

## Cycle30: extraction and a fresh embedding check

T28's series interchange and individual coefficient limit passed clean
direct leaf audits in WeilWorkQuantizationGaussianRecovery and
WeilWorkQuantizationGaussianCoefficientLimit. The terms are expanded on Re=3/2;
absolute norms factor into the summable absolute Dirichlet terms and one
fixed integrable Gaussian kernel. The resulting normalized moment is the
absolutely convergent logarithmic Gaussian coefficient sum. Its uniform
absolute-line majorant for T>=1 pays dominated convergence, yielding
B_n(T)->u_n/sqrt(n) for every positive integer n. No critical
Dirichlet-series convergence or physical limiting mean is assumed.
The finite-set Bessel bound remains to formalize. GaussianEnergy now
proves its singleton energy comparison and the source rigidity-or-linear-energy
alternative; no source upper bound has been obtained.

A new external candidate was inspected at its primary source:
[Chen--Fang--Guo--Hou--Shao--Zhou, September 2026 preprint](https://arxiv.org/html/2609.11560v2),
Theorem1.1 and the norm definition in Section1.1. It claims local critical
Lp embedding for Dirichlet polynomials for p>2. This is not adopted as a
proved input here. At p=2 the Hardy norm of sum u_n n^(-s) is sum |u_n|^2,
whereas our controlled critical coefficient energy is sum |u_n|^2/n.
Using the normalized coefficients u_n/sqrt(n) moves its controlled trace
to A(1+it), not the required A(1/2+it). Thus the direct proposed application
does not produce C25-upper or C28. Higher-p use also needs its actual
Hardy norm and a justified infinite boundary limit. The mismatch is an
applicability obstruction, not a disproof of the preprint or the source
conjecture. Gaussian/Bessel recovery remains BRIDGE, with the exact
classical comparison in Broucke--Hilberdink AppendixB retained.

## Cycle31: finite Bessel proof and explicit comparison errors

GaussianGram and GaussianBessel passed clean final direct leaf audits.
The first gives the exact Gaussian square integral of every finite
exponential polynomial and the diagonal Gram limit for distinct frequencies.
The second integrates the actual source cross term, proves the finite
variational inequality, and combines those identities with actual
coefficient recovery. Thus T28 assertion2 is now compiled, completing
all three assertions. No extra analytic premise is imposed on hW.

GaussianFiniteEstimates also passed its clean final direct audit. Here
is its complete finite estimate, used inside the T29 proof. For a finite
frequency set write Q=sum |c_n|^2 and S1=sum |c_n|. If every off-diagonal
Gaussian kernel is at most q>=0 and every moment error |B_n-c_n| is at
most delta, then

    |Gram-Q| <= S1^2 q,
    2E/(T sqrt(pi)) >= Q - 2 S1 delta - S1^2 q.

For the first inequality, subtract the exact diagonal and bound the norm
of each off-diagonal term by |c_n||c_m|q; the double sum is S1^2 q.
For the second, Re(conj(c_n) B_n)>=|c_n|^2-|c_n|delta follows from
Re(z)>=-|z|. Sum this inequality and combine the first bound with the
compiled variational inequality. These arguments use only finite sums
and already-proved integrability. The q and delta bounds are explicit
finite analytic inputs, not newly assumed source properties.

T29 still requires its uniform arithmetic coefficient-error estimates
and growing-cutoff limit. The generic finite estimate does not discharge
them. T27, C25-upper, C28, C30, C31 and WP04 remain OPEN. C31's new
quantitative source comparison is recorded separately in
EXPOSING-VARIANCE-COERCIVITY.md, without a formal receiver or proof claim.
