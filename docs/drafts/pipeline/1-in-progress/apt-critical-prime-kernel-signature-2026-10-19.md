# Signature of the critical translated prime form

- **ID:** APT-CRITICAL-PRIME-KERNEL-SIGNATURE
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / OPEN CLASSIFICATION
- **Work status:** PAUSED at the user's request (2026-10-19). The two started continuous-kernel and exact-mass leaves are complete and wired. The sign and coercivity problem remains open; the persistent goal was cleared.
- **Source:** ../3-formalized/apt-critical-translated-prime-form-2026-10-19.md
- **Statement:** Determine the sign and coercivity of the complete limiting critical prime form on actual finite real factorial patterns.

## Scope and established input

Accepted significant-result count remains **0/100**. No numerical experiments, added
axioms, heartbeat increases, full builds, commits, or pushes. README stays read-only.
Use one owned foreground Lean/build at a time. Do not assume the sign of a kernel as
a premise in the eventual main endpoint. No claim about the full Weil form follows
from a prime-channel statement alone.

The translated-source package passed targeted builds, direct-file and axiom audits,
and catalog refresh. The parent card records three unrelated global lint reachability
errors. It gives, for every finite real pattern,

`P∞(b) = (4/π⁴) Σ_(m≥1) A(m) J_m(b)/m⁴`,

where `J_m(b)=∫_(v>1) v⁻²(1-cos(2πmv/12)) Q_b(mv) dv`,
`Q_b(t)=|Σ_(j∈S) b_j exp(2πijt)|²`, and `E_b=Σ b_j²`.
It also gives `E_b/48≤J_m(b)≤4E_b` for `m≥1` and a support-independent
`ℓ²` bound for `P∞`. The existing arithmetic charge satisfies:
`A(2)=-2 log 2`, `A(m)<0 iff m=2`, `A(m)=0 iff m=1 or 4|m`,
and `A(m)>0 iff m>2 and 4∤m`.

Every nonzero pattern therefore retains the negative second harmonic and every
positive admitted harmonic. This does not determine the sign of their total sum.
No argument may treat the masses `J_m(b)` as independently selectable variables.

## Plan

- [x] Recover the exact complete-source diagonal and review existing sign information.
- [x] Search prior corpus work before beginning this topic.
- [x] Prove and formalize the sharp cumulative-charge boundary below.
- [x] Establish the exact common-density and unit-cell representations.
- [x] Formalize the continuous real representative, including endpoint matching.
- [x] Formalize the exact full half-line pattern mass using the existing sinc-square Fourier identity.
- [ ] Decide the sign of the real even kernel; supply actual finite-pattern consequences.
- [ ] Audit any obstruction's strongest positive survivor, then formalize that exact statement.
- [ ] Complete targeted, actual-file, axiom, index, lint, novelty, and significance audits.

## Paper deductions to audit and formalize

Put `H_N=Σ_(1≤m≤N) A(m)/m³` and
`γ(u)=u⁻²(1-cos(2πu/12))` for `u>0`.
The exact small charges give

`H_0=H_1=0`, `H_2=-log(2)/4`,
`H_3=H_4=-log(2)/4+log(3)/9`,
`H_5=-log(2)/4+log(3)/9+log(5)/25`.

Since `3<4`, `H_3<-log(2)/36<0`. Since `3²>2³` and `5⁴>2⁹`,
`H_5>log(2)/150>0`. All later increments are nonnegative. Thus the sharp
discrete boundary is zero for `N≤1`, negative for `2≤N≤4`, and positive for `N≥5`.
These are exact symbolic deductions, not numerical observations. The complete Lean
scratch check now passes with an empty log, including the absolute charge bound,
cubic absolute summability, uniform cumulative bound, convergence, and strict
positive limiting margin. The new leaf is
`FactorialCriticalPrimeCumulativeCharge.lean`; targeted build and direct-file checks
pass, and all eleven public declarations have only `propext`, `Classical.choice`,
and `Quot.sound`. Catalog refresh succeeded. The subsequent global generated-file
lint check reports stale `LEAN_API.md` and `LEAN_OVERVIEW.md`, so that gate remains
non-green; unlike the earlier parent-package run, this run has no unreachable-module
error. This support result does not settle the kernel sign.

Changing variables gives
`J_m(b)=m ∫_(u>m) γ(u)Q_b(u) du` for `m≥1`.
Consequently, after justified absolute interchange,

`P∞(b)=(4/π⁴)∫_(u>1) γ(u)Q_b(u) H_floor(u) du`.

The floor expression holds almost everywhere: the strict endpoint `u>m` must be
handled separately at integers. A sufficient uniform majorant is
`Σ_m |A(m)|/m³<∞`. A shorter proof now uses the existing exact identity
`Σ_(r|m) Λ(r)=log m`: since `|χ|≤1`, `r≤m` for divisors, and `Λ(r)≥0`,
the triangle inequality gives `|A(m)|≤m log m`. Thus the cubic series is
dominated by the already formalized summable `envelopeLogMajorant (3/2)`.
The alternative divisor-fiber proof uses `Σ_r Λ(r)/r²<∞` and `Σ_l l⁻³<∞`.
Another route is to use the exact change of
variables and the already proved absolute weighted diagonal to establish directly
`Σ_m ∫ |f_m|<∞`. Neither route may silently infer cubic summability from a
fourth-power coefficient series.

A cleaner endpoint convention is now available for the formal interchange: use
closed tails `Ici m`, whose integrals equal those over `Ioi m`. Then
`Σ_(m≥1) (A(m)/m³) 1_[m,∞)(u) = H_floor(u)` pointwise, including integer
endpoints. For negative `u`, both sides are zero. This avoids imposing a pointwise
identity on strict tails. It does not change the desired integral.

For a direct Fubini proof, put `F(u)=1_[1,∞)(u) γ(u)Q_b(u)` and
`g_m(u)=(A(m)/m³)1_[m,∞)(u)F(u)`, with the zero coefficient at `m=0`.
The existing harmonic-mass integrability gives `F∈L¹`; then
`∫|g_m|≤(|A(m)|/m³)∫|F|`, and cubic absolute summability justifies
`integral_tsum`. The exact common-tail change of variables identifies each
integrated summand with `A(m)J_m/m⁴`.

The full common-tail and Fubini scratch file now passes with an empty log
(`/tmp/apt_critical_prime_kernel_density_physical.log`, status zero). It proves the
pointwise closed-tail floor identity, integrability of the source-independent kernel
`density(u)=γ(u)H_floor(u)`, integrability against every actual finite pattern, and
the unconditional identity `P∞(b)=(4/π⁴)∫_R density(u)Q_b(u) du`. The same check proves
period-one and reflection symmetry of `Q_b`. The subsequent combined scratch check
also passes with an empty log for the unit-cell and symmetrized identities. The
combined leaf `FactorialCriticalPrimeKernelDensity.lean` is installed and imported;
its targeted build, direct-file check, all seventeen public axiom checks, and catalog
refresh pass. All seventeen declarations use only the three standard axioms. The
latest global lint check has one unrelated unreachable BVI module (recorded below).

For `0≤t≤1`, define the unit-cell expression
`K(t)=Σ_(j≥1) H_j γ(j+t)`.
The cubic absolute bound gives `|H_j|≤C`; hence the series converges uniformly on
this interval by the majorant `2C/j²`. Splitting into unit intervals and using
periodicity of `Q_b` should yield
`P∞(b)=(4/π⁴)∫_0^1 Q_b(t)K(t) dt`.

For real coefficients, `Q_b(1-t)=Q_b(t)`. The kernel that determines the real
quadratic form is therefore `R(t)=(K(t)+K(1-t))/2`.
Do not assume `K(0)=K(1)`; the cumulative charge has jumps at integers.
The symmetrized expression does satisfy `R(0)=R(1)` and is even on the unit circle.
The sign of `H_N` alone does not determine the sign of `R`.

`factorialCriticalPrimeRealKernel` symmetrizes the existing **L1 representative**;
its values at integers may differ from the continuous branch's limiting value.
`FactorialCriticalPrimeContinuousKernel.lean` now supplies that continuous branch,
matching endpoints, agreement on the open cell, and the exact translated-form
integral identity. Both definitions remain distinct. An isolated negative endpoint
value of the original L1 representative is not a quadratic-form witness.

The unresolved endpoint is an unconditional classification of this explicit `R`.
A positive lower bound would give coefficient `ℓ²` coercivity by exact Fourier
orthogonality. A negative value would require a proved real finite-pattern
approximation argument and then transfer to the actual high-scale sources.
An equivalent positivity criterion with an assumed kernel sign is only an intermediate
reduction, not completion of this card.

## Prior-work audit

The parent cards contain the fully paginated 241-hit APT frontier audit and exact
comparisons with earlier physical Riesz and noncritical prime budgets.
`/tmp/apt-critical-cumulative-charge-prior.json` was previously screened, including
the distinct maximum-index covariance, Abel divisor defect, and retained-prime
cutoff constructions recorded on the parent card.

Fresh searches were screened in full, twenty candidates and twenty source arguments
per result: `/tmp/apt-critical-periodized-kernel-prior.json`,
`/tmp/apt-critical-cumulative-charge-recheck.json`, and
`/tmp/apt-critical-periodized-quadratic-reuse.json`.
The first was largely irrelevant; the rephrased charge query recovered the exact
current diagonal. The periodization query recovered potentially reusable
`HTGeometry/L1PeriodizationFourier.lean:149`, the general Connes periodized integral,
and the multiplier quadratic-form integral in `ExponentialMomentPolynomialSignCone`.
Applicability of those APIs is not yet checked. All searches had unmeasured semantic
coverage and stale-generation coverage snapshots. No novelty or absence conclusion
is established by these results.

Source inspection now confirms that
`GaloisForLFunctions.HTGeometry.integral_unit_l1Periodization_mul_fourier_eq` requires
only `Integrable f` and reads each integer Fourier coefficient of `l1Periodization f`.
The same file supplies its unit-cell integrability and pointwise period-one identity.
These avoid assuming that the continuous branch `K` has matching endpoint values.
Kernel applicability still requires the exact integrable density and a Lean API check.

`RHTower.ExponentialMomentPolynomialSignCone` concerns real polynomial squares for
finite measures with entire exponential moments. It does not immediately apply to
the present finite real trigonometric-pattern family. A possible reuse route is a
cosine pushforward and an explicit palindromic coefficient construction realizing
polynomial squares. That construction and the needed measure hypotheses remain
unproved; do not silently replace the actual source family by arbitrary `L²` tests.

The complete twenty-candidate and twenty-source-argument screen of
`/tmp/apt-critical-cumulative-divisor-log-api.json` recovered the directly applicable
`ArithmeticFunction.vonMangoldt_sum`. Its source and the existing
`abs_dyadicHarmonicChi_le_one` and logarithmic-majorant convergence proof were inspected.
The divisor identity removes the need to recreate a two-index summation argument.

`/tmp/apt-critical-full-kernel-sign-prior.json` was also screened in full. Its broad
query mostly returned unrelated sign and critical-prime constructions. Source inspection
of `RHTower/CriticalPrimeTailEulerLogPositiveDefinite.lean` confirms that its positive
Fourier measure represents the safe Euler-log trace for `r>1/2`; it is not the signed
factorial kernel here. The search reports semantic coverage as unmeasured. These
results establish neither novelty nor absence of other relevant work.

Further complete candidate/source screens:
`/tmp/apt-critical-cumulative-sum-api.json`,
`/tmp/apt-critical-kernel-cells-api.json`, and
`/tmp/apt-critical-kernel-change-variable-api.json`.
Source inspection recovered mathlib's exact `integral_comp_mul_left_Ioi` (no
integrability premise), the existing `RHTower.hasSum_integral_Ico_unit`, and the
finite-range/erased-zero proof pattern for cumulative summation. The latter local
theorem is private and complex-valued, so its generic mathlib ingredients are used
directly for the real charge; no duplicate general-purpose public helper is added.
All three searches report unmeasured semantic coverage.

An exact-name lexical audit of `l1Periodization` was fully paginated: all 25 hits
in `/tmp/apt-critical-periodization-exact-api{,-page2}.json` were screened. This found
the real-valued APIs at `HTGeometry/L1PeriodizationFourier.lean:325–379`, beyond the
earlier inspected range: `realL1Periodization`, its exact complexification identity,
period-one theorem, and unit-cell integrability. The source of every relevant new
API was read. Reuse this real periodization rather than define another real-part
wrapper. The centered scaled Fourier identity is also available.

For the unit-cell reduction, the zero Fourier mode of the existing L1 coefficient
theorem applied to `density*Q_b` should suffice: periodicity of `Q_b` factors it
out of periodization pointwise. Thus no separate double finite Fourier expansion
or new general partition theorem is required.

That zero-mode application now passes in the combined scratch and target build,
as do the actual finite-pattern unit-cell and reflection identities. The target
build of the 339-line `FactorialCriticalPrimeKernelDensity` leaf completed in sixteen
seconds; direct-file and seventeen-public-declaration axiom checks also passed.

The exact-name audit also recovered `HTGeometry/SymmetricHalfEndpointPeriodization`.
Its source proves continuity at the origin for even **compactly truncated continuous**
functions with half endpoint weights. Our density has infinitely many arithmetic
jumps and is not compactly supported, so that theorem does not apply directly.
Its use of `tsum_of_nat_of_neg_add_one` is relevant to identifying the present
one-sided unit-cell branch; an additional summable domination proof remains required.

The complete screen of `/tmp/apt-critical-kernel-interchange-api.json` recovered
mathlib's `integral_tsum_of_summable_integral_norm` and the existing public
`HTGeometry.integrable_tsum_of_summable_integral_norm`, exactly matching the planned
real-valued dominated series. Both are being reused. Source inspection confirms the
interchange theorem's two premises: every summand integrable and the series of
integrated norms summable. No extra pointwise convergence premise is inserted.

## Cumulative-charge audit checkpoint

- Source: `formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeCumulativeCharge.lean`
  (248 lines, eleven public declarations), imported by the APT umbrella.
- Scratch, target build (115 seconds), direct actual-file check, and all public
  actual-import axiom checks passed; source-check logs are empty.
- Evidence: `/tmp/apt_critical_cumulative_charge{,_build,_actual,_actual_axioms,_index}.log`
  and corresponding zero `.status` files.
- `scripts/formal_tools.py lint --check-generated` returned one, with 381 large-file
  warnings and two stale-catalog errors; `/tmp/apt_critical_cumulative_charge_lint.log`.
  The catalog refresh immediately preceding this check succeeded; no global green
  claim is made in the changing shared worktree.
- Scoped whitespace and forbidden-declaration checks passed. No completed theorem
  or documentation assigns novelty credit; accepted count remains **0/100**.

## Continuous representative: paper proof for the next step

The kernel-density audit is complete: scratch and actual-file logs are empty,
all seventeen actual-import axiom entries are standard, and every public entry was
individually verified in `LEAN_API.md`. Evidence is in
`/tmp/apt_critical_prime_kernel_density{,_build,_actual,_actual_axioms,_index}.log`
and zero status files. Scoped whitespace and forbidden-marker checks passed.
Latest `lint --check-generated` returned one with 381 large-file warnings and only
`GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusJointMagnitudeLaw`
unreachable from its BVI umbrella. The previous stale-catalog errors are absent.
That module is outside this work's scope and was preserved. Global gate remains
non-green; no new significance credit is assigned.

Let `B=Σ_m |A(m)|/m³`, already finite, and use
`K(t)=Σ_(k≥0) H_(k+1) γ(k+1+t)` on `0≤t≤1`.
For every summand, `k+1+t≥k+1>0`, so
`|H_(k+1)γ(k+1+t)|≤2B/(k+1)²`. Every summand is continuous on the closed cell,
and the existing shifted inverse-square series is summable. The Weierstrass bound
therefore makes `K` continuous on `[0,1]`.

For `0<t<1`, split the existing integer periodization into nonnegative and negative
indices using `tsum_of_nat_of_neg_add_one`. Negative arguments have natural floor
zero and zero charge; the zero-index term also has floor zero. At positive index
`j`, `floor(t+j)=j`, giving exactly `K(t)`. Summability of the positive part follows
from the same bound; the negative part is identically zero.

Thus `R_cont(t)=(K(t)+K(1-t))/2` is continuous on `[0,1]`, symmetric there, and
has equal endpoint values. It agrees with the formalized real L1 kernel on the
open cell. Removing the two measure-zero endpoints preserves every pattern integral,
so the exact complete-source identity transfers to this continuous representative.
The sign of `R_cont` remains the unresolved theorem; this construction adds no sign
premise and does not replace that theorem by a positivity criterion.

The complete twenty-candidate/twenty-source screen of
`/tmp/apt-critical-kernel-uniform-series-api.json` recovered mathlib's
`continuousOn_tsum` with precisely the continuity, summability, and uniform-bound
premises above. Source inspection confirms the API. Search coverage remains
unmeasured. The zero-mode API search was also screened in full at
`/tmp/apt-critical-periodization-zero-mode-api.json`.

A further analytical route is being audited before use: the removable-at-zero
weight `γ(u)=(1-cos(πu/6))/u²` is a scaled sinc square. Its triangular Fourier support
should lie in `[-1/12,1/12]`, separating it from every nonzero integer frequency of
`Q_b`. The proposed exact full half-line mass is
`∫_(0,∞) γ(u)Q_b(u) du=(π²/12)E_b`; no numerical experiment was used to propose it.
This would sharpen comparisons but does not itself decide the signed kernel.

The first complete deep-search screen,
`/tmp/apt-critical-kernel-bandlimited-mass-prior.json`, returned mostly irrelevant
inverse-square and cosine-periodicity results. It gives no absence conclusion.
The query has been rephrased using `sinc` and the literal cosine expression; those
results have now been screened. All eight literal-cosine lexical hits and all twenty
candidates plus twenty source arguments in the rephrased sinc search were examined.
`HTGeometry/BandLimitedPositiveDensity.lean` already proves `integrable_sincSq`,
`integral_cexp_mul_sincSq`, its vanishing outside triangular Fourier support, and
`integral_sincSq = 1`. Its actual definitions and proof statements were inspected;
reuse this existing inversion theorem instead of rebuilding Fourier inversion.
`HTGeometry/FejerLatticeVanishing.lean` also exposes scaled triangle and sinc lattice
identities; those bodies have not yet been inspected. Search evidence:
`/tmp/apt-critical-kernel-cosine-mass-lexical.json` and
`/tmp/apt-critical-kernel-sinc-fourier-prior.json`. Semantic coverage is unmeasured;
these results do not establish novelty or absence of other work.

The continuous-representative scratch passed Lean with an empty log and exit zero.
Installed `FactorialCriticalPrimeContinuousKernel.lean` with eight public declarations
and its umbrella import. Targeted build, direct-file, axiom, index, and lint audits
are pending. The sign endpoint and significance count remain unchanged.

### Exact full-mass specialization: paper proof

Put `g(u)=(π²/72) sincSq(u/12)` using the existing band-limited density.
The identity `1-cos(2x)=2 sin²(x)` gives `g(u)=γ(u)` for `u>0`.
The existing scaled sinc-square integrability and integral substitution give
`∫ g=π²/6`. For distinct natural frequencies `i,j`, the nonzero integer `i-j`
has absolute value at least one. Apply the existing scaled Fourier-vanishing
identity with `ε=π/6` and `s=2π(i-j)`; taking real parts gives
`∫ g(u)cos(2π(i-j)u)du=0`. Every such term is integrable by domination by `g`.
The already formalized finite cosine expansion of `Q_b` now collapses its
whole-line integral against `g` to `(π²/6)Σ_j b_j²`.
Both `g` and `Q_b` are even, so the two half-line integrals agree and yield
`∫_(0,∞)γQ_b=(π²/12)Σ_j b_j²`. This is an exact specialization of existing
Fourier machinery, not a new inversion theorem or a sign decision.

The fresh `sincSq integral cosine polynomial` hybrid query was screened in full
(20 candidates and 20 source arguments; no proof ideas or ingredient sets).
The exact `sincSq_scaled` lexical query has one hit, inspected in its entirety:
`HTGeometry.BandLimitedPositiveConfiguration.integral_cexp_mul_sincSq_scaled_eq_zero`.
Its source at line 305 and the existing Fejer lattice identities were read.
The former matches the mass proof; the latter addresses a different lattice sum.
Evidence: `/tmp/apt-critical-kernel-sinc-pattern-api.json` and
`/tmp/apt-critical-kernel-sinc-scaled-api.json`. Inventory coverage is complete,
but semantic coverage remains unmeasured and many compiler snapshots are pending
or stale; no absence or novelty inference follows.

The exact `sincSq` lexical query returned thirteen hits, all screened without
pagination loss. The remaining apparent alternatives were source-checked:
`LamzouriSincAffineMinorant` concerns an anchored positive-definite Gram bound,
while `SincBackgroundDetectionWindow.sincSqCoeff` names hyperbolic-sine power-series
coefficients, not this full-line Fourier mass. Neither replaces the proposed
finite-pattern specialization. Evidence:
`/tmp/apt-critical-kernel-sinc-exact-api.json`.

### Candidate concrete sign witness: analytical proof obligations

To decide an actual form rather than assume a kernel sign, test the exact singleton
pattern analytically. Write `J_m` for its already defined harmonic mass. A candidate
certificate isolates the unique negative charge at two, treats `3≤m<20` explicitly,
and bounds the entire remaining infinite tail. No numerical experiment supplies any
of the following estimates; they remain proof obligations:

- `J_2 ≥ 10/9`; `J_3,J_5 ≤ 4/3`; `J_6 ≤ 7/6`.
- `J_7,J_13,J_14,J_15,J_17,J_18,J_19 ≤ 7/6`; `J_9,J_10,J_11 ≤ 1`.
- For `m≥20`, `J_m ≤ 11/10`.

The proposed mechanism for the latter bounds is a Laplace representation, with
`θ=πm/6`:
`J_m=1+∫_(0,∞) exp(-t)(θt sin θ-t² cos θ)/(t²+θ²) dt`.
Cauchy–Schwarz in the numerator gives `|J_m-1|≤1/θ`. Sign-sensitive versions
retain `sin θ` and `cos θ`; small `m=2,3,5,6` instead use the exact full mass and
integrated cosine Taylor bounds. This representation and every required estimate
must be proved or recovered from the corpus before claiming a negative witness.

The existing charge bound gives an infinite-tail majorant
`(11/10)Σ_(m≥20) log(m)/m³`.
Integral comparison would bound the series by `(log(19)+1/2)/(2·19²)`.
Finite log comparisons can be exact power inequalities against `log 2`, using
`log 3≤(8/5)log 2`, `log 5≤(7/3)log 2`, `log 7≤(17/6)log 2`,
`log 11≤(7/2)log 2`, `log 13≤(15/4)log 2`,
`log 17≤(25/6)log 2`, `log 19≤(13/3)log 2`, and `log 2≥2/3`.
These proposed coefficients need exact Lean checking; this is not a completed
sign proof, a contribution claim, or grounds for retiring the route.

The initial oscillatory-tail deep search was screened in full (20 candidates,
20 source arguments, one proposed ingredient set). Its proposed ingredient chain
mixes an unrelated THIM dyadic cosine tail with a radial phase estimate and does
not discharge this Laplace identity. A broad OR lexical query returned 65,092 hits;
only its twenty returned entries were screened, so it provides no exhaustive
coverage claim. It was narrowed to `sinc tail` instead. Evidence files:
`/tmp/apt-critical-kernel-oscillatory-tail-api.json` and
`/tmp/apt-critical-kernel-oscillation-lexical.json`.

The rephrased `sinc tail` search recovered an applicable exact identity:
`RHTower.integral_sinc_eq_square_current` in `SoninSineTraceCurrent.lean:21`.
Its full source was read, including the existing `π/2` sine-current limit.
It converts the finite sinc-square head into
`J_m=1-cos θ+θ(π/2-∫_0^θ sinc)`, avoiding a duplicate integration-by-parts proof.
The similarly named `SoninSincTailMellin.norm_sincTail_le` was source-checked:
it concerns a complex Mellin-weighted band-indicator kernel and does not give the
required signed scalar estimates. Both returned pages (34 displayed declarations,
40 candidates and 40 source arguments) were screened; the reported total is forty
and module caps mean this is not a claim that every lexical match was displayed.
Evidence: `/tmp/apt-critical-kernel-sinc-tail-api{,-page2}.json`.

### Stronger candidate survivor: uniform negative coercivity

If the singleton certificate closes, audit the stronger statement rather than stop
at a negative example. The following analytical route is still a conjectural proof
plan, with its intermediate estimates not yet formalized.

1. Prove `|H_j|≤3/8` and `Σ_(1≤j≤12)|H_j|≤1`.
   The odd/even charge identity gives
   `H_∞≤(9/8)Σ_(q odd, q≥3)log(q)/q²-(log 2)/4`.
   Decreasing-function comparison on the odd lattice bounds the series by
   `5 log(3)/18+1/6`. Then `log3≤(8/5)log2` and `log2≤3/4` give `H_∞≤3/8`;
   the known cumulative-charge sign and monotonicity handle all finite `j`.
   The twelve-term absolute sum is a finite exact combination of
   `log2,log3,log5,log7,log11`, bounded by the same power comparisons.
2. Put `a=π/6`. The cosine representation
   `γ(u)=∫_0^a(a-v)cos(vu)dv` gives `|γ''(u)|≤a⁴/12`.
   Direct differentiation also gives
   `|γ''(u)|≤a²/u²+4a/u³+12/u⁴` for positive `u`.
   Use the first bound for `j≤12` and the second for `j≥13` to majorize the
   second derivatives of the reflected cell series by
   `T≤π⁴/15552+(π²+π+1)/1152<1/50`.
   Use this as a summable curvature budget for the individual reflected summands;
   differentiating the infinite kernel is unnecessary.
3. A symmetric twice differentiable cell function with curvature bound `T`
   differs from its mean by at most `T/12`. One proof bounds differences by
   `(T/2)| (t-1/2)²-(s-1/2)² |` and integrates; convexity in `(t-1/2)²`
   reduces the maximum to the center and endpoints. More explicitly, for
   `x=(t-1/2)²` and `y=(s-1/2)²` in `[0,1/4]`,
   `|x-y|≤x+y-8xy`; its integral in `s` is `1/12+x/3≤1/6`.
   Prove the pairwise quadratic-distance bound for each reflected summand,
   sum it using the curvature budget, then integrate the already continuous
   kernel. This avoids an unnecessary infinite-series differentiation theorem.
4. The proposed singleton bounds yield the exact positive coefficient budget
   `32/405+28/1125+49/19440+17/1764+32/10935+29/30000+7/2662+
   105/52728+749/1382976+1729/4556250+175/176868+301/1574640+
   91/123462+671/86640 ≤ 5/36-1/300`.
   The negative second harmonic contributes at most `-(5/36)log2`, so the
   intended mean bound is `∫_0^1 R_cont≤-log2/300`.
   Combining the curvature estimate and `log2≥2/3` would give the stronger
   unconditional target `R_cont(t)≤-log2/2000` throughout the unit cell,
   hence a uniform negative bound for every nonzero finite real pattern.

The eight prepared arithmetic checks now pass in Lean: the positive rational
budget, curvature rational budget, twelve-charge coefficient budget, quadratic
distance inequality, and four Taylor-bound rational comparisons. These verify
only the stated arithmetic implications. The analytic harmonic estimates, finite
charge-to-budget reductions, curvature bound, and infinite-tail exchange remain
open. No negative witness, coercivity theorem, no-go retirement, or significance
credit follows from these checks.

### Continuous-leaf dependency recovery

The index refresh completed with exit zero; all eight public declarations were
individually found in `formal/LEAN_API.md`. The authoritative lint run returned one
with 381 large-file warnings and a single unrelated BVI reachability error for
`CofinalMobiusMagnitudeObservablesAndGradient`. No APT error or stale-generated-file
error appeared. Preserve that concurrently developed BVI module. Evidence:
`/tmp/apt_critical_prime_continuous_kernel_{index,lint}.log` and status files.
The targeted build was stopped after rebuilding changed dependency artifacts for
about 48 minutes. Retrying with `lake --old build` still selected actively edited
foreign dependencies; that owned process group was also stopped and its exit
verified before continuing. Neither interrupted build is recorded as a pass.
The first direct check exposed missing transitive artifacts. A targeted
`lake --old build` of the six identified BiScale/RHTower dependencies completed
successfully; no foreign source was edited. Evidence:
`/tmp/apt_finish_missing_dependencies.log` and status `0`.
Direct actual-file `lake --old env lean -o ...` compilation now passes with an
empty log for both the continuous and mass leaves. The final actual-import axiom
and generated-catalog checks are recorded below.

Further reuse checks: the full 20-candidate/20-source/one-ingredient screen of
`/tmp/apt-critical-kernel-symmetric-oscillation-api.json` did not supply the needed
cell-mean estimate. Its suggested use of symmetry of the Hessian confuses bilinear
derivative symmetry with reflection about `1/2`, so that proposed chain was rejected.
Broad lexical searches for exponential integrals and midpoint/trapezoid terminology
returned 1,127 and 1,182 matches respectively; only their twenty returned hits were
screened, with no exhaustive-coverage claim. Filtering the lexical query to
`Mathlib` returned zero despite the source APIs below existing: do not infer API
absence from that result. An exact-name hybrid query is checking the dependency API.

Actual source inspection recovered mathlib's
`integrableOn_exp_mul_complex_Ioi` and `integral_exp_mul_complex_Ioi` in
`Analysis/SpecialFunctions/ImproperIntegrals.lean:64,88`. The apparent native
alternative `ThetaRenewalPhaseSlope.integral_exp_mul_ccos` fixes the damping rate
to `1/4`; its proof uses precisely those general mathlib exponential primitives.
`MarkovExactFirstCellCosLogIntegralAndTwentyThreeRatioPBAP` already proves the
degree-five sine upper bound, degree-seven sine lower bound, and the exact lower
bound `69313/100000≤log2`. Their full statements and proofs were inspected; reuse
them for the proposed small-harmonic estimates. None is yet claimed compiler-checked
in this new application.

The exact-name hybrid query for `integral_exp_mul_complex_Ioi` was screened in full
(7 displayed declarations, 20 candidates, 20 source arguments). It recovers the
mathlib primitive directly and the existing
`HTGeometry.integral_Ioi_pow_mul_cexp` together with
`integrableOn_natPow_mul_cexp` in `MonomialLaplaceComplex.lean`.
Those moment statements and their source proof were inspected; they supply the
first and second exponential moments needed by the proposed Laplace estimates.
Evidence: `/tmp/apt-critical-kernel-laplace-exp-exact-api.json`.

A focused APT deep search for the stronger negative-coercivity target was also
screened completely (20 candidates, 20 source arguments, one ingredient set):
`/tmp/apt-critical-kernel-negative-coercivity-prior.json`.
It recovers the actual translated-energy convergence, harmonic diagonal, and
absolute coefficient-square bound already used here. Its suggested chain proves
convergence, not a sign. The generic two-mode negative diagonal extremizer concerns
a separate involution pairing. None of these retrieved statements supplies the
new concrete signed-kernel estimate; unmeasured semantic coverage still prevents
an absence or novelty conclusion.

The exact `factorialCriticalHarmonicDefect` lexical query returned three matches,
all inspected: the existing scalar definition, its `[0,2]` bounds, and strict
positivity for positive harmonics. Its definition and bound proof were checked
at `FactorialCriticalCorrelationLimit.lean:265–282`. The staged mass leaf now
includes the singleton identity `J_m({j},b)=b_j² factorialCriticalHarmonicDefect(m)`;
the sign proof should sharpen this existing scalar object. It must not introduce
an equivalent replacement definition. Evidence:
`/tmp/apt-critical-kernel-scalar-defect-api.json`.

External ingredient audit: NIST DLMF already records the positive-real Laplace
representations of the auxiliary sine/cosine-integral functions in
[6.7.13](https://dlmf.nist.gov/6.7.E13) and
[6.7.14](https://dlmf.nist.gov/6.7.E14). The proposed scalar-tail representation is
a specialization and elementary recombination of that classical machinery;
the representation itself is not a novelty claim. The native arithmetic kernel's
uniform sign, if proved, still needs its own novelty and significance audit.

The logarithmic-tail deep search was screened completely (20 candidates, 20 source
arguments, one ingredient set): `/tmp/apt-critical-kernel-log-cubic-tail-api.json`.
It recovered public `RHTower.integrableOn_log_sub_div_cube` and
`RHTower.integral_Ioi_log_div_cube` in `XiRadialJensenMassCentralCurvature.lean`:
the latter integrates `log(x/a)/x³` to `1/(4a²)`. Together with the inverse-cube
integral this supplies the proposed `log(x)/x³` tail value by linearity.
`HTGeometry/LogLinearTailIntegral.lean` was read in full; its antitone integral-test
framework supplies the sum comparison and the exact inverse-square logarithmic
integral used in the odd-charge bound. The suggested generic convergence chain
does not supply the quantitative tail constant. The apparent
`Sieve.DivisorSquareTail.logCubeKernel` hit was source-checked and means
`(1+log x)³/x²`, a different integrand.

The final pending sine/Laplace search finished with partial results: all twenty
candidate statements and twenty source-argument statements were screened in
`/tmp/apt-critical-kernel-sine-laplace-prior.json`. It recovered
`connes_sinDiv_eq_laplace` and `laplace_sineKernel` as possible later ingredients;
their applicability to the proposed scalar-tail identity is not checked. The
search reports a runtime deadline, malformed local-model JSON during judging,
pending coverage, and an incomplete background refresh. These results cannot
support an absence or novelty claim. No further sign-proof work is started before
the requested pause.

## Final closure before pause

The two completed leaves are imported by
`formal/GaloisForLFunctions/ArithmeticPositivityTheory.lean`:

| Leaf | Public declarations | Verified endpoint |
| --- | ---: | --- |
| `FactorialCriticalPrimeContinuousKernel.lean` | 8 | Continuous reflected cell kernel, matching endpoints, agreement with the L1 representative on the open cell, and the exact full translated-form integral |
| `FactorialCriticalPrimeKernelMass.lean` | 4 | Singleton/scalar identity, scaled sinc-square weight identity, integrability, and `∫_(0,∞)γQ_b=(π²/12)Σ b_j²` |

Both actual files passed `lake --old env lean -o ...` with empty logs and status
zero. A separate actual-import audit covered all twelve public declarations and
found only `propext`, `Classical.choice`, and `Quot.sound`. The source declaration
sets match that audit exactly. Evidence:

- `/tmp/apt_critical_prime_continuous_kernel_actual.{log,status}`
- `/tmp/apt_critical_prime_kernel_mass_actual.{log,status}`
- `/tmp/apt_critical_prime_kernel_closure_axioms.{log,status}`
- `/tmp/apt_critical_prime_kernel_closure.{log,status}` — mass scratch, API probes,
  and the eight arithmetic certificates below; status zero and empty log.

`scripts/formal_tools.py index` passed and refreshed `LEAN_API.md`, `LEAN_GAPS.md`,
and `LEAN_OVERVIEW.md`. Each of the twelve declarations was individually confirmed
exactly once under its actual module in `LEAN_API.md`. Source whitespace and
forbidden-declaration/heartbeat checks passed. No full or umbrella build was run.

The final authoritative `scripts/formal_tools.py lint --check-generated` returned
one: 381 existing large-file warnings and six unrelated reachability errors:

- `BiScaleUncertainty.SieveLocalVisibilityClassification`
- `BiScaleUncertainty.SievePrimePowerLocalRegularity`
- `BiScaleUncertainty.SieveVisibilityPhaseSeparation`
- `BiScaleUncertainty.SieveVisibilityRadialEstimates`
- `TransHorizonIncidenceMechanics.FermiBoundedPrimeCapacityObservability`
- `TransHorizonIncidenceMechanics.FermiFinitePrimeAntichainBound`

No APT or stale-generated-file error appears. Those foreign modules were preserved;
the global lint gate is not green. Evidence:
`/tmp/apt_critical_prime_kernel_closure_{index,lint}.{log,status}`.

The results remain supporting normalizations and representations, with no separate
significant novelty established. Accepted significant-result count remains
**0/100**. The next mathematical obligation, if work is explicitly resumed, is an
unconditional sign/coercivity proof for the actual arithmetic kernel, including
the proposed analytic estimates and a fresh novelty/significance audit. No route
is retired and no sign or RH consequence is claimed.

### Checked arithmetic certificates

These exact examples were checked together in the closure scratch. They do not
prove the analytic premises or their connection to the native harmonic masses.
Their statements and proofs are retained here before scratch-source cleanup.

```lean
/-- Exact rational bookkeeping for the proposed singleton certificate;
this does not prove its analytic premises. -/
example : (32 / 405 : ℝ) + 28 / 1125 + 49 / 19440 + 17 / 1764 + 32 / 10935 +
    29 / 30000 + 7 / 2662 + 105 / 52728 + 749 / 1382976 + 1729 / 4556250 +
    175 / 176868 + 301 / 1574640 + 91 / 123462 + 671 / 86640 ≤ 5 / 36 - 1 / 300 := by
  norm_num

example : (22 / 7 : ℝ)^4 / 15552 + ((22 / 7 : ℝ)^2 + 22 / 7 + 1) / 1152 < 1 / 50 := by
  norm_num

example : ((-(5 / 4 : ℝ) - 7 / 108 - 3 / 500) +
    (2 / 3 + 7 / 72 + 16 / 243) * (8 / 5) +
    (67 / 200) * (7 / 3) + (6 / 49) * (17 / 6) + (2 / 121) * (7 / 2)) * (3 / 4) ≤ 1 := by
  norm_num

example {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 4)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) : |x - y| ≤ x + y - 8 * x * y := by
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hx0 (show 0 ≤ 1 / 4 - y by linarith)]
  · nlinarith [mul_nonneg hy0 (show 0 ≤ 1 / 4 - x by linarith)]

/-- Taylor-bound arithmetic for the second harmonic, using 3.14 < π < 22/7. -/
example : (10 / 9 : ℝ) ≤ 1 / 2 + (157 / 50 : ℝ)^2 / 18 +
    (157 / 50 : ℝ)^4 / 1458 - (22 / 7 : ℝ)^6 / 437400 := by
  norm_num

example : 1 + (22 / 7 : ℝ)^4 / 288 - (157 / 50 : ℝ)^6 / 38400 +
    (22 / 7 : ℝ)^8 / 9031680 ≤ 4 / 3 := by
  norm_num

example : 1 + (7 / 8 : ℝ) - 5 * (157 / 50 : ℝ)^2 / 18 +
    625 * (22 / 7 : ℝ)^4 / 23328 - 15625 * (157 / 50 : ℝ)^6 / 27993600 +
    390625 * (22 / 7 : ℝ)^8 / 59256852480 ≤ 4 / 3 := by
  norm_num

example : 2 - (157 / 50 : ℝ)^2 / 2 + (22 / 7 : ℝ)^4 / 18 -
    (157 / 50 : ℝ)^6 / 600 + (22 / 7 : ℝ)^8 / 35280 ≤ 7 / 6 := by
  norm_num
```

The six completed closure scratch sources were removed after verification.
Validation logs and corpus-search JSON are retained. Work is paused; no further
conjecture or implementation work is authorized by this checkpoint.

## Log

- 2026-10-19 — At the user's explicit request, `formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md`
  was rewritten as a foundational introduction (why / what with glossary / how with thirteen
  mechanisms / traps and Lean conventions / frontier / working conventions), in the style of the
  Arithmetic Criticality Theory README. This supersedes the "README stays read-only" rule recorded
  above and on the sibling APT cards. The README carries mathematics only: no module index, dates,
  or progress. Lean sources were not touched; the umbrella docstring still describes the field by
  its original nine-item list. The docs-level programme files under
  `docs/reports/arithmetic-positivity-theory/` were not changed.
