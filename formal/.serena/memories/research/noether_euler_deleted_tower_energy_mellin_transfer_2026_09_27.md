# Euler deleted-prime channels, finite tower energy, Mellin transfer

Active goal remains proving RH via arithmetic conservation/Noether. RH is NOT proved. This turn made verified mathematical/Lean progress; do not mark goal complete or blocked. Repo /Users/michael/Documents/code/hgt/formal. No subagents, commits, pushes, full builds, umbrella builds, numerical experiments, sorry/custom axioms, or heartbeat increases. One own foreground Lean process at a time. All own processes finished.

## New verified leaves
Four files in GaloisForLFunctions/RHTower, 19 public theorems total:
1. CCMPrimeDeficitEulerDeletedChannels.lean (6 public)
2. CCMPrimeDeficitEulerDeletedEnergy.lean (4 public, one definition)
3. CCMPrimeDeficitEulerFactorialEnergy.lean (5 public)
4. CCMPrimeDeficitEulerDeletedMellin.lean (4 public, two definitions)
All final audits passed with lake --old env lean FILE -o .lake/build/lib/lean/.../FILE.olean. Fresh objects verified, each imported exactly once into GaloisForLFunctions/RHTower.lean. Final audits had no warnings. Combined 19-theorem #print axioms audit exited 0; only [propext, Classical.choice, Quot.sound]. Scratch /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/EulerDeletedEnergyAxiomAudit-ljvltdyk.lean removed. No own scratch or live process remains. No forbidden constructs/trailing whitespace in new source; umbrella git diff --check passed.

## Mathematics and exact APIs
Notation: q_P=ccmEulerRough P (indicator of n>1 and coprime(n,P)); b_P=ccmEulerRenewalKernel P=q_P^2 (Dirichlet convolution). J_P=ccmEulerDeletedPrime P (von Mangoldt restricted to non-coprime indices). F_P=b_P*J_P.

Channels:
- ccmEulerDeletedPrime_ne_zero_iff (P n): J_P(n) != 0 iff IsPrimePow n and not coprime(n,P).
- ccmEulerRenewal_deletedForce_prime_pow_mul, line53: for prime p dividing P, k>0, coprime(n,P), F_P(p^k*n)=log(p)*b_P(n). Includes n=0 separately.
- ccmEulerRenewal_deletedForce_eq_zero_of_two_primes: if distinct primes p,q both divide P and N, F_P(N)=0.
- ccmEulerRenewal_deletedForce_term_unique: at most one divisor pair contributes nonzero to F_P(N).
- ccmEulerRenewal_deletedForce_sq, line125: F_P(N)^2=sum_{ab=N} b_P(a)^2*J_P(b)^2. NO arithmetic cross terms.
- ccmEulerRenewal_deletedForce_pmul: pointwise square of b_P*J_P equals Dirichlet convolution of their pointwise squares.
Private deleted_prime_power extracts p,k,p prime,p|P,k>0,p^k=b. Private deleted_channel_unique proves divisor-pair uniqueness using coprime divisibility and cancellation. If extending generic signed sequences, avoid duplicating unnecessarily.

Energy:
- ccmEulerDeletedEnergyBudget P = sum_{p in P.primeFactors} log(p)^2/(p-1).
- Budget_nonneg all P.
- ccmEulerDeletedPrime_critical_energy_le (P N), line108: sum_{n=1..N} J_(P+1)(n)^2/n <= B(P+1), uniform in N. Positive modulus encoded by P+1. Proof dominates by finite prime-power towers, geometric sum. No infinite-series assumptions.
- ccmEulerRenewal_deletedForce_energy_eq (P N), line115: sum F_P(n)^2/n = sum_{a<=N} b_P(a)^2/a * sum_{b<=N/a} J_P(b)^2/b. Exact triangular identity.
- ccmEulerRenewal_deletedForce_energy_le_budget: force energy <= B(P+1) * rough kernel energy at same horizon.

Factorial energy:
- ccmEulerRenewalKernel_critical_energy_le (P N): sum b_P(n)^2/n <= (1+log N)^4, all P,N including N=0. Reuses prior b<=divisor count and Sieve.sum_card_divisors_sq_div_le_polylog.
- ccmEulerRenewal_deletedForce_critical_energy_le (P N): sum F_(P+1)(n)^2/n <= B(P+1)*(1+log N)^4.
- ccmEulerDeletedEnergyBudget_factorial_le_moment: B(m!) <= 2 sum_{n<=m} Lambda(n)*log(n)/n. Uses p-1>=p/2 and primes dividing m! are <=m.
- ccmEulerDeletedEnergyBudget_factorial_le: B(m!) <= log(m)^2+30log(m)+2, all m. Uses abs_sum_vonMangoldt_log_div_sub_le from VonMangoldtLogHarmonicSummatory.
- ccmEulerRenewal_deletedForce_factorial_critical_energy_le, line88 after repair: sum F_(m!)(n)^2/n <= (log(m)^2+30log(m)+2)*(1+log N)^4, all m,N.

Mellin:
- ccmEulerDeletedCriticalSeq P N n = F_P(n)*n^(-1/2) as complex, on Icc 1 N, else0.
- ccmEulerDeletedCriticalPolynomial P N t = LSeries seq (it).
- ccmEulerDeletedCriticalPolynomial_eq_sum: polynomial equals sum_{n<=N} F_P(n)*n^(-(1/2+it)). Thus actual force profile, no discarded phases.
- integral_ccmEulerDeletedCriticalPolynomial_le_energy (P N) (hT:1<=T): integral_{-T..T} |polynomial|^2 <= (5*pi*exp(1)*N+(5*pi/2)*T)*sum F_P(n)^2/n.
- integral_ccmEulerDeletedCriticalPolynomial_le (P N) hT, line103: same prefactor times B(P+1)*(1+log N)^4 for modulus P+1.
- integral_ccmEulerDeletedCriticalPolynomial_le_of_length_le adds N<=T: bound (5*pi*exp(1)+5*pi/2)*T*B(P+1)*(1+log N)^4.
Reuses Sieve.integral_Icc_normSq_LSeries_le_general_affine at sigma0 with critical weight absorbed in coefficient. The finite sum lemma is Sieve.LSeries_eq_sum_term_of_support (namespace qualification essential).

## Interpretation / remaining gap
These are coefficient and averaged critical-frequency estimates. They do NOT give pointwise square-root control of D(T), or signed source-minus-prime-work cancellation. Existing exact identity D-A_P=E_P-fullPrimeWork still retains every term. Coefficient cross terms vanish; distinct delayed time profiles can interfere. Mean-square transfer records the N+T cost explicitly. Need control/cancellation of the carrier-length N contribution for the actual combined signed source, plus retained action; cannot throw that term away or infer RH from these estimates.
Potential next conjecture: extend unique-factor energy to arbitrary signed coprime-supported sequences (or coprime projection of arbitrary AF), identify critical adjoint of deleted-prime convolution and T* T=B(P) Id on coprime subspace. This is a candidate arithmetic partial isometry / skew-adjoint coupling, not yet formalized, and actual source dynamics remain to be established. Corpus search 'coprime isometry' returned no matches. Also global lint exposed new concurrent CCMCoherentPhaseCostReduction and CCMCoherentReflectedCancellation sources, not ours and unwired; could search/read their direct Lean next for a relevant source-cancellation bridge. Do not assume their audits or wire unfinished work.

## Verification / indexing
formal_tools.py index succeeded, refreshed LEAN_API/LEAN_GAPS/LEAN_OVERVIEW and search DB. lint --check-generated exited1 with 24 unrelated unwired modules and stale LEAN_API.md/LEAN_OVERVIEW.md under concurrent edits. None of four new modules named. Do not chase or wire unrelated unfinished work. Unwired RHTower: CCMCoherentPhaseCostReduction, CCMCoherentReflectedCancellation, ClusterInterpolationContour, ClusterNodeFrame, CompositeResolventDivision, CuspSeriesBulkTailBounds, MobiusDiscretePacketCriticalHorizon, MobiusDiscretePacketEdgeEstimates, MobiusDiscretePacketGeneralOrder, MobiusDiscretePacketHorizon, MobiusDiscretePacketSourceAperture, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, RiemannKernelCuspSeries, TruncatedRiemannKernelWeilEnergy, XiWindowQuotient, ZetaZeroDensityPowerSaving. HTGeometry: ExponentialLagrangeContour, FixedAdjoinIndependentDescent, FunctionFieldJetBasis, FunctionFieldJetExtension, FunctionFieldJetField, PolynomialExtrapolationRemez.

Lean repairs: use explicit f in nested Finset.single_le_sum; positivity cannot close reflexive <= branch (le_rfl); prove Ico 1 (N+1)=Icc 1 N via ext/simp/omega (no Nat.Ico_succ_right); field_simp closed tower rational identity without ring; rational inequality transport needed explicit calc ring identities instead of nlinarith; positivity hint hb0=ccmEulerRenewalKernel_nonneg before gcongr on squares. No mathematical conjecture refuted in this turn; failures were Lean elaboration/normalization and all repaired.
