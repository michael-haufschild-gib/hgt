# Actual signed Gamma jumps and positive convolution coupling

- **ID:** LI-CLOCK-SIGNED-GAMMA-JUMP-COUPLING
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / exact signed source decomposition
- **Parent:** [integrated actual-source sign](../1-in-progress/li-clock-integrated-source-sign.md)
- **Failed producer:** [ordinary degree compound-Poisson mechanism](../5-failed/li-clock-degree-compound-poisson.md)
- **Statement:** For the actual source and p>1, finite positive Gamma jump measures satisfy mu_p*CP(tau_minus)=CP(tau_plus), with signed intensity density exp(-pt)P(t)/t, quantitative total-variation tails and positive integer-time convolution/stochastic coupling.

## Gates and boundary

- [x] Complete475-line author proof N1–N17 and actual source admissions.
- [x] Independent root ALL475/ALL N1–N17 audit and primary-source spot checks.
- [x] Leaf A: actual positive Gamma foundation, all14 exports locally formalized and integrated.
- [x] Leaf B: exact signed jumps, all19 exports locally formalized and integrated.
- [ ] Leaf C: exact probability coupling and no-go closure formalized with all gates.

The ordinary discrete degree compound-Poisson proposal is false for every z>0 because its second log-PGF coefficient is negative on the actual source. The continuously Gamma-smoothed law is a different object. Positive CP representation of one whole mu_p is equivalent to the already-audited P>=0/RH receiver; fixed-p derivative signs only give the known strip boundary. Neither the positive raw law nor integer-time coupling supplies the missing pointwise signed density comparison. RH and original all-order source sign remain OPEN. No-go closure remains pending exact Lean formalization of the positive survivor; parent route is not retired.

## Formal plan

Frozen768-line `/tmp/li_producer_theta_signed_gamma_formal_plan.md`, SHA
`5b4b6f9dbf50b4293b5633b0f0dcaa83466fe42b4bea550c5e37305e98f6d9a1`:
three proposed leaves,18 actual definitions/25 complete public theorems and32
private proof groups. Root exhaustive final review PASS,
`/tmp/li_root_theta_signed_gamma_formal_plan_review.md`; independent ALL184
review `/tmp/li_pole_theta_signed_gamma_formal_plan_audit.md`, SHA
`a903238c58ffdb381dc8879f1b095ffccf8eb2c82803c25d750e85bbb2416752`, root
read completely, PASS. Staged implementation released: actual Gamma foundation,
independent private primitive Taylor core and finite-half-line Laplace uniqueness.
B12's local derivative neighborhood must also retain `p-u>1`; explicit7-line
addendum `/tmp/li_root_theta_signed_gamma_formal_plan_addendum.md` preserves
all public contracts. The foundation retains actual
single-Xi normalization, j0 atom and Gamma rate p. Later stages retain full
signed L1/TV, actual probability-law equalities and every integer-time product
coupling. Leaves A/B are now locally FINAL_READY; C remains an open formal obligation.

## Formal foundation now installed

`formal/GaloisForLFunctions/RHTower/LiClockThetaGammaMixture.lean`,666 lines,
SHA `f276f4f6b3267f00e45832ebd8a3e5b4cc0a5e9f0d560bbf4f3c74f9e1e20c85`,
provides all14 approved A definitions/theorems for every p>0. Complete source,
exact zero atom, true density L1, Laplace and real/complex MGF admissions
retain the single normalized Xi. Dual exhaustive reviews, exact14-contract
comparison, named5513/direct6207/importedALL14axes74692 all pass; every axiom
report is foundational-only. Root verified artifact hashes, wired import,
index4461/all14 rows and lint80924. Global lint has10 unrelated unreachable
modules, zero owned errors. Final evidence:
`/tmp/li_root_theta_gamma_mixture_final_certificate.md`.

Signed-jump B19 is now [locally formalized](../3-formalized/li-clock-signed-gamma-jumps.md):
exact1624 SHA `fdda232106c1dd11b7226566691396024ce05286ed7a09f16fa261a0de0c6b9d`,
dual all-body reviews, named10613/direct19051/importedALL19axes37011 and
scratchALL98 foundational-axiom gates pass. Root wired/indexed all19 exports;
lint has11 unrelated unreachable errors and the owned large-file warning.
Complete certificate `/tmp/li_root_theta_signed_gamma_jumps_final_certificate.md`.
Coupling/no-go C10 remains unfinished; generic carrier, order, transform and
atom helpers are in progress. Original source sign and RH remain OPEN.

## Audited complete paper

Author `/tmp/li_producer_theta_raw_log_next_attack.md`,475 lines, SHA256 `8f9803dc0bb525c2fafb6d66079f8dbcffcd5b3466f5bc55d9d16e9e491a471f`.
Root complete review `/tmp/li_root_theta_raw_log_next_review.md`, SHA256 `b8478ae8b04eb5567d16fa3384daccd7c387d1c01a6040bd90a95f1dffbd193c`.
Both the broad corpus mixture predicate and the ordinary Poisson-weighted law were checked; they are not interchangeable. Full paper follows verbatim.

# Actual theta raw-to-log next attack: signed Gamma jumps

Status: PAPER PASS for source identities, the discrete compound-Poisson obstruction,
and the unconditional positive convolution coupling below. OPEN for the requested
all-order logarithmic sign at an unbounded set of dampings p>1. No RH premise,
synthetic theta source, numerical job, Lean compiler, tree/card edit, or new agent.
All new probability statements below are paper results, not installed Lean APIs.

## 1. Exact source and the concrete conjecture tested

Use the SINGLE normalized actual complete theta source, not a squared partition:

    R_j = 2 integral_(x>0) x^(2j) thetaCuspFullSource(x) dx,
    nu_j = R_j/R_0 > 0, nu_0=1,
    Phi(z)=XiC(-I*z)/XiC(0)=sum_(j>=0) nu_j z^(2j)/(2j)!,
    M_n=normalizedPrimeArchMoment n,
    H(p)=log Phi(1/p), p>0.                              (N1)

For every fixed z>0 define the literal degree probability

    pi_z(j)=nu_j z^(2j)/((2j)! Phi(z)), j>=0.

Its PGF is A_z(s)=sum_j pi_z(j)s^j. Writing Phi(z sqrt(s))/Phi(z)
is convenient notation only: the entire series in s is the definition, so no
complex square-root branch is asserted. A_z(0)=1/Phi(z)>0 and A_z(1)=1.
Every degree has positive mass. All complete-source normalizers are retained.

Concrete next conjecture CG tested here: for 0<z<1, this actual degree law has
an ordinary compound-Poisson representation with jumps in {1,2,...} and finite
nonnegative intensities. Such a representation would give a direct positive
log-PGF producer before Gamma smoothing. CG is FALSE for EVERY z>0, by N7 below.
This is a test of a uniform-in-order mechanism, not additional finite protected
orders of the requested damping signs. Its exact positive salvage is N10-N15.

## 2. Genuine Gamma-mixture interpretation of the SAME raw germ

Let p=1/z and, for j>=1, let Gamma_(2j,z) have density on t>0

    f_(2j,z)(t)=p^(2j) t^(2j-1) exp(-pt)/(2j-1)!.

The j=0 law is delta_0, not a shape-zero density. Repeated integration by parts
of the positive exponential integral proves each density has mass1, its Laplace
transform is (1+z*s)^(-2j), s>=0, and its n-th moment is
z^n*(2j)(2j+1)...(2j+n-1). All integrals are genuine: a polynomial times exp(-pt)
is integrable for p>0; the boundary terms vanish at infinity and the stated
positive shapes control zero. This is also the primary Gamma integral used in
GammaMixtureConcentration.lean:24-27, not an assumed new distribution interface.

Mix these laws with the ACTUAL probabilities pi_z(j). Positive Tonelli gives

    mu_p = [delta_0 + exp(-pt) K(t) 1_(t>0)dt]/Phi(1/p),
    K=B', B(t)=sum_j nu_j t^(2j)/((2j)!)^2,
    Laplace(mu_p)(s)=Phi(1/(p+s))/Phi(1/p), s>=0.       (N2)

Indeed differentiating the complete B series on compact sets gives
K(t)=sum_(j>=1) nu_j t^(2j-1)/[(2j)!(2j-1)!]. Multiplication of pi_z(j)
by f_(2j,z) cancels z^(2j) with p^(2j), with no missing factor2. The integral
of exp(-pt)K is Phi(1/p)-1; thus the displayed normalizer really makes mu_p a
probability, with atom0 exactly1/Phi(1/p). Its positive continuous component is
nonzero. There is no continuous density at the atom and no first-power
reciprocal-zero summability requirement.

For real u<p its genuine MGF is

    E exp(u Y)=Q_z(u)=Phi(z/(1-z*u))/Phi(z).             (N3)

For any complex |u|<=rho<p, the COMPLETE double absolute mixture sum is bounded
by Phi(1/(p-rho))/Phi(1/p)<infinity. This admits the MGF and local uniform
series exchange before taking derivatives. For n>=1 the j0 row is zero:

    a_n=E[Y^n]/n!
       =z^n/Phi(z) sum_(j>=1)
          nu_j z^(2j)/(2j)! * choose(2j+n-1,n),
    a_0=1.                                             (N4)

This is exactly C7 of the frozen349 and A1 of frozen441. It is a distributional
realization of that existing all-order raw germ, not a substituted source.
The exact signed recursion stays

    n a_n=sum_(k=1..n) k b_k a_(n-k),
    b_n=(-1)^n H^(n)(p)/n!, n>=1.                     (N5)

Neither pi_z>=0 nor this genuine positive Gamma mixture or its MGF proves that
recursion's logarithmic subtraction nonnegative. All raw ratios from frozen441
still exclude a_1/a_0. No new claim of that ratio's sign/order is made here.

## 3. Actual degree law cannot be compound Poisson

The installed local identity XiC'+v G(v)XiC=0 and the exact jets G^(2n)(0)
=(2n)! M_n rotate to Phi'/Phi=x*sum_n(-1)^n M_n x^(2n) near x0. Thus the genuine
local holomorphic log with log Phi(0)=0 has the source-determined coefficients

    log Phi(x)=sum_(j>=1) (-1)^(j-1) M_(j-1) x^(2j)/(2j).

For every fixed z>0, Taylor expansion of the entire degree numerator near s0
therefore gives

    log A_z(s)=-log Phi(z)+sum_(j>=1) ell_j(z)s^j,
    ell_j(z)=(-1)^(j-1) M_(j-1) z^(2j)/(2j).            (N6)

The first two coefficients are exact SAME-source values:

    ell_1=M0*z^2/2>0,
    ell_2=-M1*z^4/4<0,
    M1=nu_1^2/2-nu_2/6>0.                             (N7)

M1_pos is an installed unconditional actual-source theorem, not a moment-sign
premise. A finite positive-jump compound-Poisson PGF has local logarithm
sum_(j>=1) eta_j(s^j-1) with eta_j>=0. Its coefficient of s^2 is eta_2>=0,
contradicting N7. Uniqueness of the logarithm near s0 is valid because A_z(0)>0;
allowing an atom at0 among jumps only changes the ineffective constant intensity,
not the s² coefficient. CG is false at every z>0, not only the target z<1.

Terminology guard: after embedding degrees into real numbers, Law(J_z) IS an
IsCompoundPoissonMixture under the corpus's broader arbitrary-weight definition:
Law(J_z)=convPowMixture(pi_z,delta_1), since delta_1^{*j}=delta_j and every pi_z(j)>0.
N7 excludes ordinary POISSON weights/positive log intensities, not this broader
predicate. No opposite claim about the installed predicate is made.

This does NOT prove the continuously Gamma-smoothed mu_p non-compound-Poisson.
Smoothing combines complete overlapping densities. It can cancel negative
individual ell_j even though their discrete atoms cannot cancel. It also says
nothing about a negative requested b_n at a particular damping.

## 4. Full signed jump construction, with a quantitative L1 ledger

Restrict now to the requested p>1, so 0<z<1. Write A=xiShiftAbsoluteMass 0.
The installed all-copy radius bound is |M_n|<=A*150^(-n). For
q=z^2/150<1 it gives

    |ell_j|<=A*z^2/(2j)*q^(j-1),
    sum_(j>=J)|ell_j|<=A*z^2/(2J)*q^(J-1)/(1-q), J>=1. (N8)

This is genuine absolute summability, not signed summability. The log series
in N6 converges on |s|<150/z². One can prove its identification without
assuming zero-freeness: its exponential agrees with the entire numerator
sum_j nu_j z^(2j)s^j/(2j)! near0 by the installed differential/jet recurrence;
the analytic identity theorem extends that equality throughout this disk.
On the real segment [0,1] the exponential is positive, so its real logarithm
is the displayed real series, without principal-log branch ambiguity. Hence

    sum_j ell_j=H(p)>0.                                (N9)

Define ell_j^+=max(ell_j,0), ell_j^-=max(-ell_j,0), Lambda_±=sum_j ell_j^±.
Both are finite and strictly positive: N7 retains the j1 positive and j2 negative
jump, with Lambda_+-Lambda_-=H(p)>0. They are the Jordan parts of the
DISCRETE intensity. Define finite positive
jump measures eta_z^±=sum_(j>=1)ell_j^± delta_j. For any finite positive jump
measure tau with mass Lambda, define the genuine probability

    CP(tau)=exp(-Lambda) sum_(m>=0) tau^{*m}/m!.

The convolution powers are finite measures of mass Lambda^m; positive Tonelli
and the exponential series give total mass1. Their PGF/Laplace exponential
formula follows from the same absolutely convergent convolution series. No
unproved generic infinite-divisibility classification is needed.

N6/N9 and uniqueness of power-series probability coefficients give the exact
positive convolution coupling

    Law(J_z) * CP(eta_z^-) = CP(eta_z^+).               (N10)

It retains ALL degrees, including the j0 atom, rather than discarding negative
log intensities. Both sides are genuine positive probability laws.

Gamma-smear the positive intensities separately:

    tau_p^±(dt)=sum_(j>=1) ell_j^± f_(2j,z)(t)dt,
    sigma_p=tau_p^+-tau_p^-.

Positive Tonelli gives tau_p^± mass Lambda_±. The sum of L1 norms of the signed
summands is exactly sum_j|ell_j|<infinity, so the signed infinite density series
converges in L1, admits integration against every bounded measurable test and
has the N8 total-variation tail bound. Polynomially weighted L1 sums also
converge at every fixed order n: their terms are |ell_j| z^n times a polynomial
of degree n in j, absorbed by q^(j-1). This is before every moment/log exchange.
For each t>0 the factorial source bounds admit the full pointwise series and
compact uniform convergence, so the following density identity is pointwise:

    sigma_p(t)=sum_(j>=1) ell_j f_(2j,z)(t)
              =exp(-pt) sum_(j>=1)(-1)^(j-1)M_(j-1)
                              t^(2j-1)/(2j)!
              =exp(-pt) P(t)/t.                        (N11)

Here P(t)=integral_0^t F(s)ds is the literal actual clock primitive. Its full
Taylor identity follows by integrating the installed compact absolute response
series. P(t)=sum_(n>=0)(-1)^n M_n t^(2n+2)/(2n+2)! and P/t=O(t) at0.
The factor1/(2j) in ell_j becomes exactly1/(2j)! after Gamma smoothing;
there is NO remaining factor1/2 in N11. Equivalently the full-copy primitive is
sum_(q:XiZeroCopy) Re[1-cos(t*w_q)], with every multiplicity preserved. The
factor1/2 in the canonical log's cancelled full-copy formula has already been
accounted for by N6; it is not inserted again into the clock primitive.

Gamma(2a,z)*Gamma(2b,z)=Gamma(2a+2b,z) follows from the positive beta integral
(or their Laplace transforms and finite-measure uniqueness). Therefore smoothing
commutes with every complete Poisson convolution sum. Alternatively applying
N2 to N10 directly proves, by its genuine Laplace exponential formula,

    mu_p * CP(tau_p^-) = CP(tau_p^+).                  (N12)

N11 yields the complete, absolutely admitted logarithmic formula

    log Laplace(mu_p)(s)=H(p+s)-H(p)
                       =integral_(t>0)(exp(-st)-1) sigma_p(t)dt,
    Laplace(sigma_p)(s)=H(p+s), s>=0.                  (N13)

The last identity holds because the Gamma Laplace factors are (1+zs)^(-2j)
and the absolutely convergent log series evaluates at that argument. Thus no
signed Laplace identity below p>1 or below gamma=1/300 was silently imported.
It also agrees exactly with audited P9/P10 of root217.

For every n>=1 the SAME logarithmic coefficient is

    b_n=(1/n!) integral_(t>0) t^n sigma_p(t)dt
       =z^n sum_(j>=1) ell_j choose(2j+n-1,n).          (N14)

All these sums/integrals are absolute at each fixed n. Locally uniform expansion
of exp(u t) is admitted for |u|<p-1/sqrt150, using N8 with geometric slack;
this is a strictly positive neighborhood for p>1. Differentiating there gives
N14/N5, with the requested n vs n! normalization retained. This is the exact
uniform-index signed Gamma transform, not an unsigned approximation to it.

## 5. Strongest unconditional positive salvage and its precise boundary

Taking any INTEGER m>=1 in the coupling N12 gives

    CP(m*tau_p^+) = CP(m*tau_p^-)*mu_p^{*m}.            (N15)

Consequently CP(m*tau_p^+) stochastically dominates CP(m*tau_p^-):
couple independent X~CP(m*tau_p^-) and Y~mu_p^{*m}; Y>=0,
so E h(X+Y)>=E h(X) for every bounded increasing h. The same integer-time
coupling holds for eta_z^± and J_z. This is dependency-closed positive source
information at EVERY integer time, with finite explicit intensity/L1 tails.
No pointwise intensity domination, arbitrary fractional-time law, or uniform
logarithmic-order sign is deduced by differentiating that integer-time statement.

For clarity, ordinary positive-jump compound-Poisson representation of ONE mu_p
is a substantially stronger property than all b_n>=0 at ONE p. It tests the log
Laplace derivatives at ALL future Laplace arguments p+s. If mu_p=CP(tau) with
finite tau on (0,infinity), its atom0 fixes tau mass H(p). N13 then implies
Laplace(tau)(s)=H(p+s)=Laplace(sigma_p)(s), all s>=0, so tau=sigma_p as finite
signed measures. Uniqueness is elementary: push both measures by t->exp(-t)
into [0,1]; equality at integer s gives every polynomial moment, polynomial
density gives all continuous tests and hence equality of finite measures.
Therefore

    mu_p is positive-jump CP <=> sigma_p>=0
       <=> P(t)>=0 for EVERY t>0 <=> RH, p>1.          (N16)

Conversely P>=0 makes N11 itself a finite positive jump measure and N13 its
CP law, so this is a genuine equivalence, not just a necessary implication.
Continuity of P turns the a.e. density sign into the pointwise sign. The final
RH equivalence is the already-audited actual primitive P7; it is NOT an RH proof.
No general theorem 'atom0 plus infinite divisibility implies CP' is used here.

Current's exact single-damping strip audit proves all derivative signs at one
p iff the narrower actual zero-strip bound holds. This is compatible with
unconditional all-order signs for p<=1 and leaves unbounded p open. It must
not be conflated with N16's future-argument condition or with N7's discrete law.

The remaining actual inequality, in this coordinate, is the full overlapping
signed density comparison

    sum_j ell_j^+ f_(2j,z)(t) >= sum_j ell_j^- f_(2j,z)(t), EVERY t>0. (N17)

N17 is precisely P>=0; it is recorded as a residual, NOT offered as a new
independent conjectural producer. A proposed fractional-time convolution
factor CP(theta*tau^-)*mu_(p,theta)=CP(theta*tau^+), all theta>0, would likewise
assume the missing positive infinite divisibility. It is not supplied by N15.
This report's actual tested conjecture CG has a complete counterproof; its
positive survivor N10-N15 is complete. It does not falsify literal F_N sign,
P sign, or RH. No new countermodel replaces theta.

## 6. What the actual Ward law supplies, and where its use stops

The installed source-specific Ward certificate is
303 nu_(j+1)<=(32j+17)nu_j, EVERY j>=0. It integrates the exact arithmetic atom
score against x^(2j) times the literal Born amplitude square, uses the true
score moment (2j+1)/2, sums EVERY atom including the zero n0 term, and divides
by actual R0>0. The source proof contains genuine position and score L1 before
integration, so no supplied score/Hankel positivity premise is being used.
It yields nu_j<=(32/303)^j j!, which admits all probability/MGF/full-series
constructions above. It also gives the already-audited raw degree controls of
frozen441, with its z²-dependent row ratio and positive-degree n>=1 restriction.

The attempted propagation was: use this raw all-order positive mixture to
construct a nonnegative Poisson jump measure, then its complete moments would
orient every signed logarithmic coefficient N14. N7 stops that propagation at
the discrete degree step on the ACTUAL source. Smoothing does give N11-N13,
but source Ward bounds and the established positive coupling do not supply N17.
No theorem excluding every possible use of Ward identities is asserted.
We have no proved fractional-time comparison or signed-history inequality for
the same Phi. Positive raw law, integer-time domination and finite variation
are all retained rather than relabeling a missing sign as a premise.

## 7. Primary source/dependency ledger

All following source claims were inspected in this task or already entirely
proved/audited in the frozen input papers; the new exact relevant bodies were
read directly. 'Installed' means the literal source is present; no fresh Lean
elaboration/axiom gate is claimed in this read-only task.

- PrimeArchThetaCumulantMinor.lean:151-162 literal R_j;267-271 nu/M defs;
  201-225 local differential identity;439-480 actual jets, nu1=M0 and exact M1.
- PrimeArchThetaAllOrderCumulant.lean:33-47 ALL Xi jets;55-86 product jets;
  92-145 all-order signed recurrence and source Hankel/RH receiver. Full file read.
- XiThermalSourceRelativeGapBound.lean:404-429 strict thermal second moment,
  relative actual sector energy and normalizedPrimeArchMoment_one_pos.
- LiEvenCrossActualClockBorelSource.lean:18-61 exact B coefficients/full kernel,
  every nu positive and score-factorial bound. Existing derivative/compact-sum
  admissions in the frozen394/final291 actual-source packets are reused.
- PrimeArchThetaScoreMomentRecurrence.lean:18-147 ALL actual Ward certificate,
  score/position integrability, atom normalization and complete source sum read.
- XiReciprocalSquareSecondMomentRadius.lean:115-139
  abs_normalizedPrimeArchMoment_add_le_secondMomentRadius, all-copy M envelope.
- LiEvenCrossActualClockVolterra.lean:78-120 literal F, complete Taylor and
  compact absolute envelope; root217 P1-P3/P9-P10 admits P and genuine Laplace.
- /tmp/li_root_integrated_clock_source_boundary.md: P7 exact P/RH equivalence;
  P9/P10 genuine log-Laplace domain p>1/300, not an unconditional all-p transform.
- Frozen441 /tmp/li_producer_single_damping_source_attack.md A1-A17 and
  frozen349 /tmp/li_producer_integrated_clock_cumulant_attack.md C7-C17:
  same Q_z, true whole-complex admissions, positive raw degree and signed gap.
- /tmp/li_current_single_damping_strip_audit.md S1-S8:
  exact full-copy factor1/2, fixed-damping strip classification and verified
  generalized-Li overlap. Its proof is reused, not rediscovered or strengthened.

Probability overlap actually inspected:
- HTGeometry/ConvolutionAtomBounds.lean:264-317 ordinary compoundPoisson def,
  Poisson Cauchy identity/semigroup/zero law. Positive finite-intensity machinery.
- HTGeometry/LaplaceTransformConvolution.lean:196-241 full CP Laplace formula,
  logLaplace formula and nonnegative half-line scalar cumulant. Different from
  nonnegativity of every required logarithmic derivative; no mu_p admission there.
- HTGeometry/CharacteristicFunctionPositiveDefinite.lean:122-145/204-215
  CP characteristic formula and Gram positivity; no logarithmic producer for Phi.
- HTGeometry/CompoundPoissonWitnesses.lean:20-30 uses the BROADER interface
  IsCompoundPoissonMixture = arbitrary everywhere-nonzero convolution weights,
  including an infinite measure. It is not the ordinary probability CP criterion
  in N7/N16; its existence theorem cannot construct this required law.
- RHTower/ThetaCuspLikelihoodAtomicNondivisibility.lean:205-226 is a DIFFERENT
  seam-likelihood square-gap measure, charging3 but not6; source/support no-go,
  not J_z or mu_p. No same-law nondivisibility imported.
- RHTower/ThetaTiltXiInfiniteDivisibilityNoGo.lean:1-64/208-245 concerns central
  theta probability with characteristic XiC and its Hardy odd-order zero; it is
  not the reciprocal Gamma law mu_p. Its conclusion cannot be transferred here.
- RHTower/ThetaJumpCompoundPoisson.lean:1-49/150-203 constructs the dispersion
  exponent exp(-tG) from thetaLevyDensity. This is not normalized Phi reciprocal;
  exact laws/norms differ. No identification assumed.
- RHTower/GammaMixtureConcentration.lean:1-40/139-152/889-909 supplies positive
  Gamma integral/concentration for a finite reverse-Bessel radial mixture. Only
  the elementary Gamma integral is applicable; no cumulant comparison is supplied.

## 8. Documented corpus-first search and exhaustive result disposition

Before the new mechanism the direct documented command was

    python3 scripts/formal_tools.py research "actual theta raw reciprocal gamma mixture compound Poisson logarithmic coefficients uniform all order Ward recurrence infinitely divisible Phi generalized Li" --mode deep --budget-seconds 120 --no-refresh --json

Log /tmp/li_producer_theta_raw_log_next_research.json; session32207 exit0,
elapsed93.781385s, partial=true. ALL60 returned records read:20 candidates,
20 source arguments with EVERY supplied method/proof excerpt,10 prose and10
source passages. All other hit arrays empty, including proof_ideas and
ingredient_sets. Initial AND query had0 matches; all5 relaxation trace entries
were inspected. No generated ingredient set was adopted as proof.

Inventory63642/63642 indexed, pending0, inventory_complete=true, errors[];
Lean53390/prose10252. Retrieval/index_generation1167203; coverage/current1167214
snapshot. Declarations826987/documents2389346/vectors2238183. Semantic coverage
NOT_MEASURED/reporting_budget; warningsemantic_coverage_unavailable. Methods
42 failed/397171 ready/186521 stale; invalidation_pending=false. Compiler buckets
43 compiled_snapshot,2 error,10252 not_applicable,47992 pending,2660 stale,
38 stale_snapshot,1 umbrella_source_only,2654 unavailable. These are snapshot
freshness, not theorem verification. Returned candidate/source compiler fields
are source_only/not_checked, axioms unavailable. Two errors: local reranking
deadline and malformed/incomplete local filter/judge JSON. Unfinished5 stages:
gamma compound, logarithmic mixture, reciprocal uniform queries, reranking,
filter_and_judge. Thus no inference of corpus exhaustion or novelty is licensed.

Weak/partial hits prompted direct lexical OR fallback:

    python3 scripts/formal_tools.py research 'compoundPoisson infiniteDivisibility gammaMixture' --mode lexical --any --no-refresh --json

Log /tmp/li_producer_theta_raw_log_next_lexical.json; session26532 exit0. FTS5
reports68 total,8 modules,14 eligible returned declarations, per_module2,
offset0,explore5; exploration[] and all ranked candidate/source/prose/passages
arrays empty. No coverage/semantic/compiler/elapsed fields reported. No claim
of fresh indexing or complete68-hit inspection: ALL14 actually returned names,
full relevant contracts and applicability inspected, as listed below.

Deep candidate dispositions, indices are exact array indices:
- C0/C3 Hedenmalm compact recurrence Prop/iff: supplied real-divisor receiver.
- C1 thetaCuspTotalMoment_curvature_recurrence: PRIMARY1729-1773 and def630
  verified; 'Total' is FIRST ATOM thetaCuspSourceTerm(x,1), not full theta nu.
  Actual first-atom raw bound; cannot replace complete Phi cumulants by it.
- C2 thetaCusp_allOrderCumulantRecurrence: applicable signed identity already
  frozen349; source explicitly says it does not prove the hierarchy nonnegative.
- C4/C10 generalized-Li def/first-coefficient identification: parameter receiver,
  not an independent source sign; Current already audits exact overlap.
- C5 Mobius finite-depth prime collar: adaptive divisor finite-depth observable.
- C6 first-atom even-tail recurrence: different raw first-atom tail telescope.
- C7/C12 renewal coordinate/zero: coordinate definitions, no log inequality.
- C8/C11 actual local Noether action/response: local deformation derivative,
  different function and no all-order reciprocal log comparison.
- C9 Shamir tail sampler and C18 Bottcher thetaFour: unrelated carriers.
- C13 eighth likelihood sector: fixed-order different source curvature.
- C14 PowerSeries uniformContinuous_coeff: generic coefficient topology only.
- C15 Hedenmalm first-clock spectral reality iff: receiver with supplied recurrence.
- C16 actual supercritical partition bound: normalized mixed Borel source/window,
  not the SINGLE theta law or logarithmic cumulants.
- C17 canonical HasUniformJet2: fixed-jet admission, not uniform logarithmic order.
- C19 actual ninth raw recurrence: fixed-order signed identity, no new sign control.

Deep source-argument dispositions (every supplied body/method read):
- S0 actual JAS prime-coordinate L2 amplification: canonical moved coordinate,
  not reciprocal clock/log observable; no phase/sign transfer.
- S1/S4 qubit derivative/bias;S2 quantum Stratonovich;S9 SSH;S11/S12 Fock moments;
  S15 Gauss-Bonnet enthalpy: different carriers/functions, rejected.
- S3/S8/S10 signed theta stage correction/matrices: definitions, no source estimate.
- S5 actual complex source and S17 Schwartz casting: applicable regularity/source
  identification only; do not produce signed cumulant comparison.
- S6/S7 theta log jets8/6: fixed spatial jets, not damping log coefficients.
- S13 bilateral Laplace: coordinate integral, no required log sign.
- S14 literal actual Borel coefficient: applicable normalization N2, already used.
- S16 first-atom continuity: regularity only, source not full Phi logarithm.
- S18 CCM localization defect: signed exact local energy identity. Its sole ready
  method uses two localization identities then linarith; assumes a compact CCM
  source and local potential, so does not admit our whole Theta/Gamma comparison.
- S19 reflected eighth modular casting: fixed-order source identification only.

Deep prose P0-P4 are compact Schwartz/global-tempered history and manifests;
P5/P7 JAS singleton/grade escape, P8 Mobius continuous coface no-go, P6 open
C5-D1 spatial slope corridor: different mechanisms, none applicable to N17.
P9 is the already-audited actual theta forcing/inverse boundary: relevant warning
against positive-inverse inference, not a newly retrieved source sign.
Deep passages T0/T2/T3 qubit/Fock gauge, T5 GammaSix horizontal normalization,
T6 Shamir, T8 digamma jet datum: wrong observables. T1 Hedenmalm finite-divisor
rigidity is an RH receiver;T4 CCM localization exact signed identity;T7 Dirichlet
coefficient uniqueness and T9 power-series topology are generic support only.
All supplied text was read; none was adopted as a new source positivity proof.

Lexical returned declarations L0-L13, all dispositions:
- L0/L1 CP coefficient Cauchy/zero: applicable positive CP construction support.
- L2/L7 CP log-Laplace nonnegative/full Laplace: applicable exact formula, not
  complete log-derivative signs of this actual law.
- L3 centered CP second moment: centered real jump assumption, irrelevant here.
- L4/L5 CP positive-definite Gram/characteristic formula: general support only.
- L6 seam-tilted not_compoundPoisson: different square-gap measure, as above.
- L8/L9 probability-memory zero/conjugacy: elementary characteristic symmetry,
  no reciprocal-Phi source identification or logarithmic inequality.
- L10/L11 reverse-Bessel Chebyshev limit/radial ratio: finite radial concentration,
  no whole Gamma mixture log sign.
- L12/L13 arbitrary convPowMixture witnesses: broader interface, NOT ordinary
  probability CP; cannot certify N7's conjecture or N16's positive jumps.

## 9. Self-audit and outcome

Reviewed claims N1-N17 are dependency-closed with explicit genuine admissions.
Index0 handled separately; n>=1 logs and positive degree rows not conflated.
Shape2j, scalez, SINGLE R0/Phi normalizers, full factorials and full-copy1/2
bookkeeping checked. All Gamma summands retained; absolute L1/TV BEFORE moments,
probability coupling and logarithmic exchange; real positive log branch pinned.
No signed all-p transform below gamma, no squared-Xi law, no actual source
replacement, no inaccessible private Lean theorem, no numerical/compile claim.
Integer coupling vs fractional-time positivity and one-p vs future-p derivatives
are separated. CP discrete obstruction is not continuous CP obstruction or RH.

Strongest new source-level salvage within this inspected packet: exact full
signed Gamma jump representation with quantitative TV tails, two positive finite
CP laws and genuine integer-time convolution/stochastic coupling N10-N15. The
probability identities are standard mechanisms applied to this literal source;
no world-novelty or corpus-absence claim is made. Existing theta nondivisibility,
positive dispersion semigroup and reverse-Bessel mixture results concern other
laws, while existing generalized-Li already captures the requested log-sign
receiver. New paper statements need independent audit and formalization before
any installed-API claim or route closure. The original all-order source-sign
objective remains OPEN; N17/N5's actual signed history comparison is not proved.
