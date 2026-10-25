# The golden receiver as a weighted digit module

- **ID:** biarithmetic-golden-digital-module
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (explicit paper derivation; audits pending)
- **Parent:** [Biarithmetic Geometry](biarithmetic-geometry-foundations.md), golden-datum module and infinite-rank spectral synthesis.
- **Statement sought:** Compute all common cofactor tangents, the completed Wiener module, its annihilator, and its Bohr hull for the damped inverse-zeta coefficients of the corpus's golden datum.

## Exact source identification

ACS proves the golden numerator `1-5u+5u^2`, with roots
`alpha=sqrt(5)*phi=(5+sqrt(5))/2` and `beta=sqrt(5)/phi=(5-sqrt(5))/2`.
Its inverse zeta series is

`(1-u)(1-5u)/(1-5u+5u^2)=1-u/(1-5u+5u^2)`.

Therefore its coefficient at norm `5^r`, `r>=1`, is
`-(alpha^r-beta^r)/(alpha-beta)`; at norm one it is one, and all other norms have zero
coefficient. This is the inverse of the actual golden rational zeta function, not a freely
chosen power row. After damping by `n^-epsilon`, put
`a=alpha*5^-epsilon`, `b=beta*5^-epsilon`. For
`0<epsilon<log(phi)/log(5)`, one has `sqrt(5)<a<5` and `0<b<sqrt(5)`.

For `0<t<5`, define

`V_t(n)=sum_(r>=1) t^r frac(n/5^r)`.

The sum converges because its tail is geometric with ratio `t/5`. The centered integer
receiver is exactly `(V_a(n)-V_b(n))/sqrt(5)`; the coefficient at norm one contributes zero
to a centered prefix. The mean series converges absolutely.

## Exact digit law

Write `n=5m+r`, `0<=r<5`. No fractional-part carry occurs in
`m/5^(s-1)+r/5^s`, since the first fractional part is a multiple of `5^(1-s)` and the added
term is smaller than that grid spacing. Reindexing the absolutely convergent series gives

`V_t(5m+r)=t V_t(m)+r*t/(5-t)`.

Consequently, if `d_l(n)` are the ordinary base-five digits,

`V_t(n)=t/(5-t) sum_l d_l(n)t^l`.

In particular `V_t(5n)=t V_t(n)` and `V_t(n)-t V_t(floor(n/5))` is uniformly bounded.
For `1<t<5`, the first nonzero digit and the geometric digit bound give
`c_t n^(log(t)/log(5)) <= V_t(n) <= C_t n^(log(t)/log(5))` for positive `n`.
For `t<=1`, the elementary bound is constant or logarithmic. Thus `V_b` has bounded total
pronic energy, while `V_a` escapes. The finite repairing kernel `delta_1-a delta_5`
annihilates every normalized golden tangent, giving the exact operator relation
`V_5=a^-1 I`. This is a proposed source derivation, still requiring Lean verification.

## Candidate full tangent classification

For `a` in the escaping range define, for positive real `x`,

`F_a(x)=sum_(s in Z) a^s frac(x/5^s)`.

Positive `s` have a geometric tail with ratio `a/5`; negative `s` have a geometric tail with
ratio `1/a`. On every compact interval both tails are uniform. The function is right
continuous, regulated, and Riemann integrable; its discontinuities lie at positive
five-adic rationals. It obeys `F_a(5x)=a F_a(x)` and is bounded above and below by positive
multiples of `x^gamma`, where `gamma=log(a)/log(5)>1/2`.

The finite-source scaling formula is

`a^-M V_a(n)=sum_(s>=1-M) a^s frac((n/5^M)/5^s)`.

It equals `F_a(n/5^M)` exactly: every omitted term has an integer fractional-part argument
and vanishes. For fixed cofactor `j`, a.e. continuity controls the grid perturbation from
`floor(n/j)`. Riemann sums, with a
separate uniformly integrable bound near zero, should therefore give every tangent as

`K_tau(j,k) = [integral_0^tau F_a(x/j)F_a(x/k) dx/x^2] /
              [integral_0^tau F_a(x)^2 dx/x^2]`,  `1<=tau<=5`.

Every phase occurs by `T_M=floor(tau*5^M)`; arbitrary horizons have phase-convergent
subsequences. The endpoint phases agree by five-adic scaling. The exact constants from
`1/sqrt(5)` cancel, and the `V_b` component disappears by its bounded energy.

For finite packets, the unnormalized norms at all phases are equivalent:
`Q_1 <= Q_tau <= Q_5=(a^2/5)Q_1`. Hence all phase completions are isomorphic as Wiener
modules via the identity on the packet space, although their normalized Gram metrics may
differ. This would classify the module independently of the phase.

## Candidate exact annihilator and spectral synthesis

At a positive five-adic rational `x` with five-adic valuation `v_5(x)`, the jump of `F_a`
is `-a^(v_5(x)+1)/(a-1)`. It is nonzero. At `x=d/5^m`, with `5` not dividing `d`, the
function `F_a(x/j)` jumps precisely when the five-free part of `j` divides `d`.
For a critical Wiener kernel `c`, write

`B_c(e)=sum_(r>=0) c(5^r e)a^-r`, for five-free `e`.

The series `sum_j c(j)F_a(x/j)` converges uniformly on compact intervals because
`|F_a(x/j)|<=C x^gamma j^-gamma` and `gamma>1/2`. Its jump at `d/5^m` is the common
nonzero factor `-a^(1-m)/(a-1)` times `sum_(e|d) B_c(e)`. If the represented vector is
zero, right continuity makes the function zero everywhere on the observed interval; choosing
large `m` puts each desired jump inside it. Divisor induction then gives every `B_c(e)=0`.
Conversely these equalities kill the function by regrouping the absolutely convergent series.
Thus the anticipated annihilator is exactly the kernel of evaluation in the prime-five
coordinate at `a^-1`, with no conditions on the other prime coordinates.

The corresponding Bohr hull is the coordinate slice `omega(5)=sqrt(5)/a`. The kernel should
be the closed principal ideal generated by `delta_1-a delta_5`, by one-variable Wiener
division at an interior point. Finite packet vectors indexed by five-free integers are
linearly independent: the jump relations are triangular in divisibility. The full integer
cofactor module is therefore infinite-dimensional, despite its one-dimensional restriction
to powers of five. These two representations must not be conflated.

Payment should equal this annihilator: a nonzero profile has positive asymptotic normalized
energy, while membership in the principal ideal gives an actual repair through the bounded
base-five defect and the paid `V_b` part. This last implication requires an explicit bounded
Wiener division estimate, not merely closure of the principal ideal.

## Audit obligations

- [x] Corpus source numerator and eigenvalue sum/product inspected.
- [x] Exact inverse-series coefficients, actual arithmetic source and mean, paid-ideal reduction, and geometric centered-prefix identity in Lean.
- [ ] Complete the Riemann-sum and small-origin estimates on paper.
- [ ] Check the regulated jump calculation, uniform infinite-kernel interchange, and all phase limits.
- [ ] Prove bounded Wiener division and payment equivalence; compare existing AOT coordinate ideals.
- [ ] Literature audit for weighted digit functions and one-prime Wiener modules; no novelty claim yet.
- [ ] Dependency-closed paper theorem before moving this card to stage 2.
- [ ] Lean formalization, axiom audit, and precise selectivity statement.

This is the inverse-zeta receiver embedded in the ordinary integer divisor-prefix model.
The prime-power lattice alone is a different, smaller action. The field's golden
calibration must state which action it uses. No claim about the actual Möbius source follows.

## Paper audit: origin, phase limits, and division

The scaling function is uniformly bounded on `[1,5]` and bounded below by its positive
geometric tail with indices `s>=2`. Scaling gives two-sided bounds `c x^gamma<=F_a(x)<=C x^gamma`
for all positive `x`. This also proves integrability of `F_a(x/j)F_a(x/k)/x^2` at zero,
since `2gamma-2>-1`.

Let `h=5^-M`, `x_n=nh`, and `T_M h->tau`. The scaled pronic sum is exactly

`h sum_(1<=n<=T_M) [a^-M V_a(floor(n/j))] [a^-M V_a(floor(n/k))] / (x_n(x_n+h))`.

On `x_n>=eta>0`, each scaled digit row is exactly its bilateral profile at
`5^-M floor(n/j)`. Approximate the profile uniformly on the compact argument interval by a
finite sum of fractional-part functions. Each approximant has finitely many discontinuities;
away from them the perturbation of size at most `h` caused by the floor tends uniformly to
zero. The bounded Riemann sums over small neighborhoods of the finite discontinuity set have
arbitrarily small total length. This proves convergence on `[eta,tau]`. On `0<x_n<eta`, the
digit bound gives the majorant `C h sum x_n^(2gamma-2) <= C' eta^(2gamma-1)` uniformly in
`M`; comparison with the integral of the decreasing power proves the last inequality.
Letting `eta` decrease to zero completes the limit. This applies to every fixed pair and
therefore simultaneously to the countable Gram table. Subcritical `V_b` has finite pronic
energy and disappears in each mixed pairing by Cauchy–Schwarz.

Every summand of the bilateral profile has a right limit and a left limit. Uniform convergence
on compact intervals passes both limits through the series. A summand jumps only when
`x/5^s` is an integer, with jump `-a^s`; summing `s<=v_5(x)` gives exactly
`-a^(v_5(x)+1)/(a-1)`. At all other points the function is continuous. The same uniform
convergence for a full critical Wiener packet justifies summing its jumps. A right-continuous
function vanishing almost everywhere on an open interval vanishes everywhere there: a
nonzero value would persist on a right neighborhood of positive measure. Thus the jump
argument identifies the full, rather than merely finite-packet, vector kernel.

For bounded Wiener division set `R=5^-1/2` and let `f_r(e)=f(5^r e)`, with `5` not dividing
`e`. If `sum_r a^-r f_r(e)=0`, define

`g_r(e)=-sum_(t>=1) a^-t f_(r+t)(e)`.

Absolute convergence holds because `a R>1`. The zero-evaluation identity gives
`g_0(e)=f_0(e)`, and subtraction gives `g_r(e)-a g_(r-1)(e)=f_r(e)` for `r>=1`.
Hence `f=(delta_1-a delta_5)*g`. The exact geometric estimate is

`sum_(r,e) |g_r(e)| R^r/sqrt(e)
 <= [1/(a R-1)] sum_(r,e) |f_r(e)| R^r/sqrt(e)`.

To prove it, interchange the nonnegative double sum and put `s=r+t`; the inner geometric
sum is bounded by `sum_(t>=1)(aR)^-t=1/(aR-1)`. This is an explicit division bound and
proves that the principal ideal is closed and equals the coordinate-evaluation kernel.

Finally `(delta_1-a delta_5)*c` has only finitely many exceptional coefficients and, for
`r>=2`, coefficient `-(a-b)b^(r-1)/sqrt(5)` at norm `5^r`. Since `b<sqrt(5)`, it belongs
to the critical Wiener algebra and is paid. Multiplication by the divided critical kernel
preserves payment. Conversely every paid kernel annihilates the full covariance limit by
the uniform source norm bound and the single-series argument on the parent card. Thus
payment, the vector kernel, the operator annihilator, and the closed principal ideal agree.
The Bohr hull is exactly `omega(5)=sqrt(5)/a`; evaluating the generator proves both inclusions.

These complete the mathematical estimates identified above on paper. Formal verification,
source-series bookkeeping, independent error audit, and novelty comparison still remain;
the card remains in progress until those checks support a precise final theorem statement.

## Critical boundary and remaining family members

The range above is the strict escape regime. At `a<sqrt(5)` the receiver is paid by the
power bound. At `a=sqrt(5)`, the energy should grow linearly in the number of base-five
annuli, hence logarithmically in the horizon. Each complete annulus has a limiting Gram
integral, while the last partial annulus is negligible. The resulting candidate kernel is

`K_crit(j,k) = [integral_1^5 F_a(x/j)F_a(x/k) dx/x^2] /
               [integral_1^5 F_a(x)^2 dx/x^2]`.

With `G(y)=exp(-y/2)F_a(exp y)`, this is the cyclic translation module generated by a
`log(5)`-periodic function on a circle, and dilation has exact norm factor `j^-1/2`.
The full Wiener series still converges uniformly on compact positive intervals at this
boundary. Therefore the jump argument still identifies the candidate annihilator with the
prime-five evaluation kernel. The strict-interior Wiener division bound fails here because
`a/sqrt(5)-1=0`; equality with the paid ideal requires a separate proof and may fail.

Do not assert that this cyclic carrier is the entire circle L² space. Periodization gives
its Fourier coefficients as

`-zeta(1/2+2*pi*i*l/log(5))/[(1/2+2*pi*i*l/log(5))*log(5)]`.

Indeed the periodized seed is `h(y)=exp(-y/2)frac(exp y)`, and
`integral_0^infinity frac(x)x^(-s-1)dx=-zeta(s)/s` for `0<Re(s)<1`.
The exact carrier is the closure of the Fourier modes whose displayed coefficients are
nonzero. No nonvanishing claim on this arithmetic progression of critical-line points has
been proved here. This appearance of the ordinary zeta function comes from embedding the
golden norm lattice into ordinary integer floor incidence, and reinforces the need to state
the chosen ambient action.

The boundary separation has an explicit paper proof, stronger than failure of the division
bound. Put `a=sqrt(5)`, `d_0=-1`, and
`d_r=1/sqrt(r)-1/sqrt(r+1)` for `r>=1`. Define `f(5^r)=a^r d_r` and zero elsewhere.
Telescoping gives `sum_(r>=1)d_r=1`, `sum_r |d_r|=2`, and
`sum_(r=0)^M d_r=-1/sqrt(M+1)`. Thus `f` is a critical Wiener kernel in the annihilator.

Digit splitting gives exactly
`a^r V_a(floor(n/5^r))=V_a(n)-V_a(n mod 5^r)`.
For `5^M<=n<5^(M+1)`, only `r<=M` contributes to its action, so

`P_f V_a(n)=-V_a(n)/sqrt(M+1)-sum_(r=1)^M d_r V_a(n mod 5^r)`.

Every term on the right is nonpositive. Since `V_a(n)>=c sqrt(n)`, the squared pronic
energy on this annulus is at least `c^2/(M+1)` times
`sum_(n=5^M)^(5^(M+1)-1)1/(n+1) >= 4/5`. Summing the harmonic lower bound proves
unbounded energy. The `V_b` part has bounded energy, and the critical Wiener action preserves
that bound, so it cannot cancel the divergence. The exact convolution/mean-correction identity
then proves that `f` does not repair the golden source. Hence its paid ideal is strictly
smaller than the module annihilator at the critical damping.

The strongest positive replacement is equality after norm closure. The generator
`delta_1-a delta_5` still repairs the source. Every finite kernel with zero prime-five
evaluation is divisible by this generator by finite polynomial division. For an arbitrary
kernel in the evaluation kernel, approximate by finite `p` and subtract the prime-five
evaluation of `p`, embedded on five-free integers. Evaluation and this embedding are
contractive, so the corrected finite kernels converge in Wiener norm. Thus the closed
principal ideal, the closure of the paid ideal, and the module annihilator agree. The Bohr
hull therefore records the norm closure, while the explicit kernel above distinguishes actual
payment from that closure. All these boundary claims remain to be Lean-certified and audited.

## Literature calibration

Weighted digit sums are classical: Hofer, Pillichshammer and Pirsic explicitly define them
within Q-additive functions in [their paper on Cantor representations](https://www.dmg.tuwien.ac.at/nfn/cqaddfct_final.pdf).
The digit law itself is therefore not a novelty claim. Bayart, Finet, Li and Queffélec study
the Wiener–Dirichlet algebra and its countably many complex coordinates in
[Composition operators on the Wiener–Dirichlet algebra](https://arxiv.org/abs/0904.2527).
The proposed programme contribution is the source identification, full cofactor tangent
classification, and exact paid-ideal comparison for this golden receiver. These searches do
not establish originality of that combination; a dedicated comparison remains open.


The critical-strip Mellin identity is already proved in corpus theorem
`RHTower.integral_Ioi_zero_fract_cpow` (`RHTower/FractionalPartZeta.lean`), and its logarithmic
Fourier version is `RHTower.fourier_fractLogCarrier` (`RHTower/ZetaCriticalLineNotSquareIntegrable.lean`).
Both statements and proofs were inspected. The new obligation is the periodization and
cyclic-carrier comparison, not that Mellin transform.

The boundary nonclosedness also has explicit paid approximants. Truncate `f` after `5^M`
and add `1/sqrt(M+1)` to its coefficient at one. The resulting finite kernel has zero
prime-five evaluation, hence is a finite multiple of the repairing generator. Its Wiener
distance from `f` is exactly `2/sqrt(M+1)`, the sum of the changed coefficient and the omitted
positive tail. Thus paid finite kernels converge to the explicit unpaid kernel; no abstract
closure argument is needed to witness the failure.

## Ambient-action audit: the intrinsic norm lattice is different

The preceding infinite-dimensional module uses ordinary integer floor incidence. The intrinsic
golden Beurling system instead has generalized-integer generating series
`Z(u)=(1-5u+5u^2)/((1-u)(1-5u))`; its divisor response after damping by `t=5^-epsilon`
has series `Z(u)/Z(tu)`. Ordinary floor incidence uses the ordinary integer counting kernel,
so these are different source experiments. The report's phrase “the golden module” needs this
choice fixed; both constructions and their comparison are required before treating its battery
as complete.

For the intrinsic model, let `B_M` be its cumulative generalized-integer count. Then
`sum_M B_M u^M=Z(u)/(1-u)`. Its centered damped response has generating series

`A(u)=Z(u)/(1-u) * [1/Z(tu)-1/Z(t/5)]`.

The bracket cancels the leading counting pole at `u=1/5`. For
`0<epsilon<=log(phi)/log(5)`, the remaining dominant pole is the simple pole `u=1/a`,
where `a=alpha*t>=sqrt(5)`. Its coefficient is nonzero: at that point none of
`1-alpha/a`, `1-beta/a`, `1-t/a`, or `1-5t/a` vanishes. All other poles have inverse
modulus strictly below `a`; a possible collision at the unit pole only adds a polynomial
factor to a subleading term. Thus `A_M=C a^M+o(a^M)` with `C!=0`.

With the natural shell energy `sum_(m<=M) A_m^2/5^m`, every norm-lattice cofactor is an
integer shift of `m`. Fixed shifts therefore have normalized covariance
`K(r,s)=a^(-r-s)`, both in the geometric escape regime and at the logarithmic boundary.
The intrinsic norm-lattice cofactor module is consequently one-dimensional, with dilation
by norm `5^r` acting as `a^-r`. This contrasts with the infinite-dimensional ordinary-floor
module. The source-series and asymptotic claims here still require their own paper/Lean audit;
the stated shell energy must be compared explicitly with any alternative corpus normalization.

At epsilon zero the ratio `Z(u)/Z(u)` cancels completely, so the positive-damping dominant-pole
argument cannot be extended to epsilon zero. Order of damping and horizon limits matters.

The intrinsic shell energy also agrees with a natural step-prefix pronic energy, up to an explicit constant on complete shells. Extend `A_m` to ordinary arguments by `A(n)=A_floor(log_5 n)`. For the complete shell `5^m<=n<5^(m+1)`, telescoping gives

`sum A(n)^2/[n(n+1)] = (4/5) A_m^2/5^m`.

The same formula holds for mixed fixed norm-lattice cofactor pairings, once `m` exceeds their shifts. A partial final shell contributes its exact telescoping weight; asymptotic proportionality of every shifted row still forces the same rank-one normalized kernel. This compares normalizations for the intrinsic counting response; it does not identify that response with the ordinary-floor inverse-zeta receiver.

A closer ideal-theoretic comparison is Mortini and von Renteln, [Ideals in the Wiener algebra W+](https://doi.org/10.1017/S1446788700030688), J. Austral. Math. Soc. 46 (1989), 220–228. Their Theorem 1 classifies nonzero finitely generated closed ideals by finite Blaschke products; the proof excludes boundary zeros. Thus the interior-versus-boundary distinction for a one-coordinate principal ideal is classical. The proposed source-specific contribution is the exact digital receiver, its complete cofactor module, and the explicit distinction between payment and annihilation, not a new general Wiener-division principle.

## Reduction to a single geometric tower modulo paid sources

Let `I_t(5^r)=t^r`, including `r=0`, and zero off powers of five. These are exactly AOT's `localFactorInverse 5 t`. The ordinary-floor golden source has the exact identity

`c_epsilon = delta_1 - I_a/sqrt(5) + I_b/sqrt(5)`.

Since `b<sqrt(5)`, the checked local-factor theorem makes `I_b` critical Wiener. Hence the golden source differs from `-I_a/sqrt(5)` by a critical Wiener source. Every critical Wiener source is paid, and convolution by a critical Wiener kernel preserves that class. Addition of such a source, and multiplication by a nonzero scalar, leave the paid ideal unchanged. Therefore its paid ideal equals that of `I_a` exactly, not only after closure.

The centered prefix of `I_a` is `-V_a`; the remaining term has bounded pronic energy. Cauchy–Schwarz then identifies all normalized cofactor Gram limits of the golden source with those of this single geometric tower. This reduction separates finite source bookkeeping from the digital asymptotic problem and removes the secondary root from every later payment argument. The exact source, mean, and paid-ideal reduction are formalized and axiom-audited in `GoldenArithmeticSource.lean`; the Gram-limit transport remains a paper result.

The exact formal-series inverse and coefficient formula are formalized in `BiarithmeticGeometry/GoldenInverseSeries.lean`, using ACS's actual `goldenDatum.zetaSeries`, its two `alpha` roots, and the checked geometric-series inverse law. Every complex damping parameter is included, with the original datum at parameter one. The direct repository check and all six main-declaration axiom audits passed with standard axioms only; the stage-3 card is `../3-formalized/biarithmetic-golden-inverse-series.md`.

## Circle model at every escaping damping

The periodic representation also describes the strict regime, not only its boundary. Write
`gamma=log(a)/log(5)`, `L=log(5)`, and `G_gamma(y)=exp(-gamma*y)F_a(exp y)`.
For `1/2<=gamma<1`, this is a bounded regulated `L`-periodic function. At phase `tau` in the
strict regime, put `Y=log(tau)` and `eta=2gamma-1>0`. For a packet profile `H(y)` formed from
translates of `G_gamma`, the half-line norm is exactly

`integral_(-infinity)^Y exp(eta*y)|H(y)|^2dy
 = [1/(1-exp(-eta*L))] integral_(Y-L)^Y exp(eta*y)|H(y)|^2dy`.

Decompose the half-line into periods and sum the geometric series. On one period the weight
is bounded above and below by positive constants, so every phase completion is isomorphic,
as a Wiener module, to the cyclic translation subspace generated by `G_gamma` in ordinary
circle `L2`. Dilation acts as `j^-gamma` times translation by `-log(j)`.
The prime-two rotation is irrational relative to `L`, so its positive orbit is dense. Strong
continuity gives invariance under the full circle translation group, including inverses.

Consequently the completed module is the closure of the Fourier modes indexed by

`S_gamma={l in Z : zeta(gamma+2*pi*i*l/L) != 0}`.

This follows from periodizing the integrable seed `exp(-gamma*y)frac(exp y)`; its coefficient
is `-zeta(s)/(s L)` at `s=gamma+2*pi*i*l/L`. Each nonzero mode lies in the cyclic closure by
Fourier averaging of translates; all other modes vanish identically. The nonzero jump of
`G_gamma` prevents it from being a finite trigonometric polynomial, so `S_gamma` is infinite.
No nonvanishing claim on the entire vertical progression is needed.

Every dilation is therefore similar, by a bounded invertible change of Hilbert norm, to
`j^-gamma` times a unitary. Its exact spectral radius is `j^-gamma`, and the radius of
`sqrt(j)V_j` is `j^(1/2-gamma)`. In the strict regime this shrinks at every prime, while the
annihilator hull still imposes only `omega(5)=sqrt(5)/a` and leaves every other prime coordinate
unrestricted. Thus this source-derived family exhibits the same distinction between operator
spectrum and annihilator hull that Q-III's weighted-white calibration exposes abstractly.
All of these circle comparisons and radius consequences still require Lean verification.

The full prime-five-supported payment domain is sharpened further in
`../1-in-progress/biarithmetic-digital-energy-and-prime-tower-payment.md`: weighted digit moments
make it an explicit weighted `ell2` condition on coefficient partial sums. At critical damping
this gives the exact nonclosed domain, beyond a single counterexample.
The stronger paper calibration in
`../1-in-progress/biarithmetic-critical-payment-has-continuum-defect.md` constructs a continuum
of independent unpaid classes inside its Wiener closure. This closure defect already appears
in the prime-five subalgebra, whose tangent module is rank one; the distinct index notions
therefore cannot be interchanged. The source payment criterion and this quotient theorem
remain to be Lean-certified.

## Direct source-to-digit recurrence

The source bridge can be formalized without first summing the fractional-part profile. The exact Euler identity `(delta_1-a delta_5)*I_a=delta_1`, together with the corpus local-factor prefix law and mean `5/(5-a)`, gives

`A_(I_a)(n)=a A_(I_a)(floor(n/5))-[a/(5-a)](n mod5)`.

Strong induction identifies this with `-a/(5-a) D_a(n)` at every horizon. The mean itself is the ordinary absolutely convergent geometric series for `|a|<5`. `BiarithmeticGeometry/GeometricTowerDigitReceiver.lean` passes its direct source check and all five transitive axiom audits. This removes an unnecessary analytic dependency from the finite source comparison; the profile remains necessary for all-phase Gram classification.

Paid perturbation invariance is formalized and audited in
`BiarithmeticGeometry/PaidSourcePerturbations.lean`: adding any paid source with absolutely
convergent mean preserves the complete complex paid ideal. Critical Wiener sources provide
an unconditional application, and nonzero scalar multiplication is included. The actual
golden coefficient lift and its application of this theorem are now directly checked and
axiom-audited in `GoldenArithmeticSource.lean`.

## Further literature calibration

The logarithmic periodicity and zeta-valued Fourier coefficients belong to classical digital-sum Mellin analysis. Cheung and Golin, [Analyzing a Weighted Digital Sum Variant](https://dmtcs.episciences.org/2785/pdf), explicitly use digital recurrences, Dirichlet generating functions, and Mellin–Perron residues to obtain periodic Fourier expansions; their introduction also distinguishes discontinuous unsmoothed rows from averaged expansions. Krüppel, [Functional Equations for Knopp Functions and Digital Sums](https://www.math.uni-rostock.de/math/pub/romako/heft65/kru2-65.html), studies the corresponding functional-equation/digit-sum connection. These references reinforce the classical status of the profile machinery; they do not establish the present paid-ideal or full cofactor-module classification. The search is calibration, not proof that the latter is absent from all literature.

## Exact step-integral route to the Gram limits

The pronic weights permit an exact Lebesgue-step embedding, avoiding a separate Riemann-sum approximation. Put `q=5^M`. Since

`integral_(n/q)^((n+1)/q) dx/x^2=q/[n(n+1)]`,

for rows vanishing at zero the covariance divided by `(a^2/5)^M` is exactly the integral of the two step profiles `a^-M v(floor(q*x/j))` and `a^-M v(floor(q*x/k))` against `dx/x^2` up to `(T+1)/q`. The identity `floor(floor(q*x)/j)=floor(q*x/j)` makes the cofactor comparison exact.

At every continuity point, the digit grid identity gives convergence to `F_a(x/j)`. The exceptional jumps form a countable set. The power envelope dominates the product by a constant times `x^(2gamma-2)`, integrable at zero in the strict regime. Dominated convergence therefore gives every phase kernel directly, including moving endpoint cutoffs. At the critical boundary use the same exact embedding only on the fixed annulus `(1,5)` and then Cesaro-average the complete blocks; the final partial block is bounded. This is an alternative dependency-closed proof of the same kernels, not a new hypothesis or a new classification claim. Lean formalization should prefer whichever exact integral interface the corpus already provides.


## Quantitative refinement of the profile argument

The fully proved paper card
`../1-in-progress/biarithmetic-digital-profile-bounded-covariance-error.md`
replaces qualitative profile convergence by the exact refinement
`H_(M+1)-H_M=C*a^(-M-1)*r`, `0<=r<=4`. It gives global uniform error
`0<=F-H_M<=4C*a^(-M)/(a-1)`, bounded absolute errors for every strict-regime
cofactor covariance, and logarithmic critical covariances with bounded remainder.
The actual golden cross terms are absolutely summable for positive damping because
`a*b/5=t^2<1`, so these stronger estimates transfer to its exact source. All claims
on that card are paper results awaiting Lean verification, not completed module classification.


## Existing exact step and circle interfaces

Corpus search located and source-checked `RHTower/StepFunctionCarrier.lean`.
`integral_tailCell_stepGramIntegrand` already gives the exact pronic cell integral for
arbitrary real sequences. `hasSum_stepGram` identifies the entire pairing for bounded
sequences; finite horizon cutoffs are automatically bounded and therefore give a route
to the exact finite step embedding without any boundedness premise on the original row.
The remaining steps are finite support, restriction to the observed interval, and real
rescaling. This is preferable to reproving the reciprocal-square cell integral.

`HTGeometry/FourierCircleTranslation.lean` supplies source-checked Fourier translation,
modulation, and scalar laws on every positive-length `AddCircle`. The more distant
`RHTower/FokasLenellsCausalFrequencySynthesis.lean` has an actual forward-cyclic-space
classification by nonzero frequencies, but in a bounded-chain space. Its public theorem
cannot be applied to the digital circle without a comparison; its finite rotated-mean
proof is a possible technique reference. No such comparison is asserted.

## Digit carry and the missing jump input

The full cofactor-annihilator proof still needs actual profile jumps. The exact
finite carry identity is
`(a-1)D_a(5^M n-1)=a^M((a-1)D_a(n-1)+4)-4` for `n>0`.
After normalization its limit is `D_a(n-1)+4/(a-1)`. A finite grid is constant
immediately left of a positive integer, and the already checked uniform grid
error transfers this limit to the actual profile. If `5` does not divide `n`,
the right value minus the left limit is `(a-5)/(a-1)`.
These are existing jump-proof obligations, drafted directly in
`/tmp/BiarithmeticDigitCarryBoundary.lean`; they remain unchecked. Extending
the jump calculation to arbitrary cofactor sums and proving uniform Wiener
tail control are separate obligations.

The required uniform tail majorant can be obtained without summing an
unweighted covariance error. Put `L=floor(log_5 j)`. Scaling the profile
by `5^L` keeps its argument in `[0,5]`, while `a>=sqrt(5)` gives
`sqrt(j)<=sqrt(5)*a^L`. Hence
`0<=F_a(x/j)<=sqrt(5)*B_a/sqrt(j)` on `[0,5]`.
Multiplication by actual Wiener coefficients gives a summable uniform
majorant. `/tmp/BiarithmeticDigitWienerProfile.lean` drafts this bound,
absolute summability, and uniform convergence of the actual coefficient
series. Checks remain pending; no infinite-cofactor conclusion is inferred
from finite covariance errors alone.

For the full Wiener grid refinement, each coefficient error is bounded
both by its individual geometric grid error and by the summable critical
Wiener majorant. Taking the minimum of those bounds gives a summable
majorant whose total tends to zero by dominated convergence for series.
This proves uniform refinement of the entire Wiener profile without an
unweighted coefficient summability assumption. The direct draft is
`/tmp/BiarithmeticDigitWienerRefinement.lean`; checks remain pending.
