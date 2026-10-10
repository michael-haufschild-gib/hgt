# OpenAI applications: full-core units, localization and prime/log formal covariance

Goal remains ACTIVE and unbudgeted. Scope all16 live+23 candidate routes, no Weil priority. No subagents. Source OpenAI/math results are PROVEN; only new application candidates await proof. Source HEAD fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and ledger hash971e9a674d00c1729580931274f49892d9dd181626f288ba5040703847aca0ec rechecked unchanged. Prior goal turn classified progress and previous8 source hashes revalidated before new work.

FIVE new native leaves, namespace GaloisForLFunctions.HTGeometry, all under formal/GaloisForLFunctions/HTGeometry:

1. PaperTerminatingCoreUnits.lean:3 theorems, no defs. Generic {k A}[Field k][CharZero k][CommRing A][IsDomain A][Algebra k A], no ambient-LND premise. Local canonical Algebra.toModule2000/Semiring.toModule2100 and core CharZero derived from injective algebraMap.
- paperTerminatingCore_isUnit_iff D (a:core D): IsUnit a iff IsUnit(a:A) and D(a:A)=0.
- paperTerminatingCore_unit_and_inverse_iff D (u:Aˣ): ambient u and u^-1 both in core iff D u=0.
- paperTerminatingCore_localization_iff D (a:core D): source/native quotient-rule extension of core clock to Localization.Away a is LND iff D(a:A)=0. Includes zero denominator.
Proof uses source paperLocallyNilpotent_kills_unit on the paid core clock. Reverse direction: Derivation.leibniz_of_mul_eq_one proves inverse fixed, then construct actual core unit. Expose u.inv using change before rw; rewriting directly on coe(u^-1) failed under restricted transparency.

2. PaperPrimeTerminatingUnits.lean:5 theorems, no defs.
- paperPrimeTerminatingCore_isUnit_iff p f: core invertibility iff f(1)!=0 AND vanishing on all p-multiples.
- paperPrimeConstants_isUnit_iff p a: coefficient-ring invertibility iff a(1)!=0, via existing slice equivalence, Polynomial.isUnit_C and isUnit_map_iff.
- paperPrimeTerminatingCore_localization_support_iff p f: native Away localization keeps prime clock LND iff denominator has p-free support.
- paperMoebius_prime_core_localization_not_locallyNilpotent p.
- paperPrimeTerminating_shifted_generator_localization_not_locallyNilpotent p c: all scalar shifts of native prime coordinate obstruct the LND extension, on the FULL core, not merely finite charts.

3. PaperFormalCoefficientDerivation.lean:1def+5theorems. Generic CommRing k,A and Algebra k A; no char0/domain restriction.
- paperFormalCoefficientDerivation D :Derivation k(PowerSeries A)(PowerSeries A).
Reuses existing PowerSeriesDeriv.coeffwiseAdd and native Leibniz theorem from CoefficientwisePowerSeriesDerivation via local Differential A := <D.restrictScalars Z>. No duplicate convolution proof.
- paperFormalCoefficientDerivation_coeff: coeff n(clock D f)=D(coeff n f).
- ..._C: C a maps to C(Da); ..._X: X maps0.
- ..._time_commute: commutes with PowerSeries.derivative A.
- paperFormalTimeEuler_coeff f n: coeff n(X * derivative A f)=n • coeff n f.
Use explicit K:=A on native coeffwiseAdd_X. C coefficient proof needs explicit PowerSeries.coeff_C in simp; time commute needs mul_comm.

4. PaperPrimeLogFormalCovariance.lean:4theorems, no defs.
Let D_p=native primeArithmeticDerivation and L=rotatedLogArithmeticDerivationComplex, w=i log p.
- paperPrimeArithmetic_log_iterate p f m: D_p^[m](L f)=L(D_p^[m]f)+(m*w) •D_p^[m]f, ALL arithmetic f.
- paperArithmeticPrimeFormalFlow_log_coeff: same identity on formal coefficient_m(E_p f).
- paperArithmeticPrimeFormalFlow_log_covariance p f:
  E_p(L f)=paperFormalCoefficientDerivation L(E_p f)+w •(PowerSeries.X * PowerSeries.derivative (ArithmeticFunction Complex)(E_p f)).
- paperPrimeTerminatingCore_log_mem p(f:core D_p): L(f:A) in core D_p.
Reuses proven native primeDeriv_rotatedLogArithmetic_commutator in FinitePrimeCoefficientDifferentialField. Derivation.map_smul is REQUIRED; generic map_smul targets unavailable MulActionHomClass and left the induction missing its m term. No computations or heartbeat raises.

5. PaperPrimeCoreLogClock.lean:1def+5theorems.
- paperPrimeCoreLogClock p: actual restriction of L to FULL core D_p.
- ..._coe and ..._iterate_coe: agrees with every ambient logarithmic iterate, via proven derivation_iterate_naturality.
- ..._commutator p f: core D_p L - L D_p = (i log p) • core D_p, at each f.
- ..._polynomial_iff p f: formal orbit for restricted L is polynomial iff ambient f=f(1) •1.
- ..._not_locallyNilpotent p: native prime generator contradicts ambient scalar-only log termination.
Use explicit k:=Complex and A:=core D_p on IsLocallyNilpotent. For polynomial iff, infer hpoly := paperFormalExponential_polynomial_iff ... first, prove typed iterate equivalence using Eq.trans and Subtype.ext, then compose. Direct rw failed Nat.Primes vs subtype transparency; target-directed refine hit heartbeat limit. Final inferred proof is clean under default limit. No prior Lean leaf modified in this batch.

FULLY VERIFIED:
5 final plain lake --old env lean <leaf> calls all empty;24public declarations=22theorems+2defs axiom-audited (standard propext/Classical.choice/Quot.sound only),24/24 exact path+name corpus retrievals. Five imports wired once; no umbrella build. All110 previous hashed modules unchanged. New total115hashed+139olderunhashed=254completed family modules (117source+137applications),2621cumulative public declarations. All580owned leaves wired once;4762 theorem/lemma results,6572total public declarations (distinguish metrics).
Global lint only FOREIGN unwired HTGeometry.QKrawtchoukCompanionTriangular, checked outside own-files.txt. Do not alter concurrent work.
Artifacts tmp/hgt-openai-math/core-units-{audits,manifest,proof-audit,searchback-audit}.json. Tracker latest_verified_batch=core-units-audits.json and plan complete for batch; overallgoal ACTIVE. Four /tmp api/build/audit/finish helpers removed; retain /tmp/paper-core-units-axioms.lean. All owned process handles terminal; no active owned process.

Route significance: MSC gains exact arbitrary-input coefficient transport/logarithmic-clock covariance and denominator tests. No original-divisor/conormal preservation or analytic source estimate yet. Two clocks coexist on the same large algebra: prime clock LND; log clock preserves algebra but has polynomial orbits only on scalars.

NEXT promising application candidate, NOT YET PROVEN: literal arithmetic Euler-factor decomposition mu=(1-x_p)*a_p with a_p p-free and a_p(1)=1. Source formal flow would give E_p(mu)=(1-x_p-t)*a_p and inverse zeta formula. Investigate faithful Dirichlet-series handoff to factor (1-p^(-s))/(1-t-p^(-s)), exact nonvanishing domain, and divisor/conormal preservation; do not assert analytic bridge from formal algebra alone. Search core-units-next-euler-factor-search.json returned8 Lean hits. Read native RHTower/Sieve/DampedEulerIdentity.lean lines33–48: tsum_twistedSummand_moebius_primePow gives1-p^(-s) (has extraneous finite P,hPprime that can be paid by empty set); one_sub_cpow_ne_zero currently requires1<Re s. Read RHTower/SquarefreeMoebiusNormalization.lean lines376–389: tsum_squarefreeCpow_prime_pow gives1+p^(-s). Direct rg found no primeCoordinate/Moebius/zeta factor identity. Need broaden/search further before coding. Other pending work preserved in tracker: simultaneous-prime core and mixed-prime Möbius derivatives; fraction-field core slice and flow naturality; finite-etale multiplier extension to char0 domains; arbitrary localized clock multipliers; explicit discriminant constants.

Discipline: one foreground Lean process; poll exact handle terminal before another build or active-file edit. Read logs ONLY after that process is terminal. Serial guarded Python drivers. No numerical experiments/full builds/source-side oleans/raised heartbeats. Search Lean corpus directly, no cards; filter JSON by relpath .lean and selected metadata only (prose contains cards). Final plain leaves, #print axioms only /tmp, multiline axiom parser, exact path+canonical-or-local names for searchback.