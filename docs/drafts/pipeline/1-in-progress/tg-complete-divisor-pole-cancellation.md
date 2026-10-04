# TG actual neutral quadratic work

- **ID:** TG-C9.24B / C9.25 continuation
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** TG, native signed arithmetic admission
- **Goal:** Prove an unconditional critical-scale estimate for the complete signed quadratic source below, then discharge the existing RH receiver. RH itself remains the goal.

## Exact open statement

For N=floor(exp(T/2)), put h_N=sum_(1<=n<=N) mu(n)/n and use the audited coefficient

    a_N(n)=mu(n)              for n<=N,
    a_N(n)=-(n/N)*h_N         for N<n<=2N,
    a_N(n)=0                 for n>2N.

Let R=ccmPrimeDeficitDivisorPoleRemainder. The literal complete quadratic work is

    Q(T)=sum_(m,n=1..2N) a_N(m)a_N(n) R(T-log m-log n).

Conjecture: there are K>0 and a finite nonnegative integer k such that

    |Q(T)| <= K exp(T/2)(T+1)^k               for every T>=0.

This must be proved for the actual coefficients. Do not assume a Möbius cancellation estimate, take absolute values of all pairs, omit tail-tail/mixed terms, or discard negative shifted times. Tuning constants or polynomial powers is not frontier progress.

## Already closed; do not re-prove

C9.24A, P3 tg-complete-divisor-pole-cancellation:
H(t)=exp(t)((1+gamma)t+d)+R(t), with one global polynomial R bound. The complete finite pair pole is exp(T)(((1+gamma)T+d)m0²-2(1+gamma)m0*m1). Harmonic neutrality removes both exponential coefficients, including for adaptive labels beyond the half-horizon.

C9.25, P3 tg-diffuse-neutral-mobius-work:
The actual diffuse coefficient has harmonic moment zero. Its stationary action is unchanged. With F0(t)=F(t)-(1+gamma)exp(t),

    D(T)=L(T)-Q(T),
    L(T)=2 sum_(n=1..2N) a_N(n) F0(T-log n).

The complete linear work has an unconditional O(exp(T/2)(T+1)^2) bound, and every absolute diagonal has total O(exp(T/2)(T+1)^4) cost. Both include the entire diffuse tail. Four public theorems pass final leaf and standard-axiom audits in CCMPrimeDeficitNeutralWork. No full quadratic or native ground-energy bound follows.

## Failed proof ideas and learning

- Fixed positive Euler modulus: C9.23 proves an actual signed renewal pole, not merely failure of a positive comparison. Fixed-P limits cannot be exchanged with the moving cutoff.
- Single tail at N+1: harmonic cancellation is exact, but one coefficient of size (N+1)h_N has potentially supercritical squared mass. The diffuse construction pays that diagonal without changing the head.
- Two-tail quadratic-zero shortcut: its second coefficient constraint contains the unknown head quadratic value. No independent coefficient bound was obtained.
- Diffusion does not pay the whole tail block. Its full correlations can still carry exp(T)h_N². The signed mixed terms are indispensable.
- Midpoint reflection: the reflected product is symmetric, so reflection doubles a half-integral rather than canceling it. The corpus's exact first-half profile is exp(t)*sum_(n<=exp(t))mu(n)/n - 1 - M(floor(exp(t)))/2. Harmonic and Mertens terms must remain coupled.
- Search suggestions combining diagonal bounds with chronological work or midpoint symmetry do not prove the signed estimate.

These are failed proof steps, not a retirement or falsification of the arithmetic conjecture. No general-source positivity theorem or another RH-equivalence wrapper will discharge the remaining task.

## Current corpus evidence

The C9.25 searches /tmp/tg-c925-neutral-work-search.json and /tmp/tg-c925-midpoint-work-search.json completed nonpartial with full source inventories; background compiler refresh remained incomplete. Candidate lemmas, source arguments, proof ideas and ingredient sets inspected.

Relevant already-read sources:
CCMPrimeDeficitCompletePole; CCMPrimeDeficitNeutralWork; CCMPrimeDeficitCoefficientAction; LogarithmicReconstructionTailSymmetry; LogarithmicFiniteEntryProfile; CCMPrimeDeficitShortReflection; LogarithmicMobiusSawtoothPrefix; CCMPrimeDeficitCoprimeBalance; CCMPrimeDeficitCoprimeRows.

The full signed reciprocal pairing and the complete coprime balance retain all arithmetic terms, but neither presently supplies the needed signed upper/lower work control. Any next estimate must confront that arithmetic interaction directly.

## Route-wide open problems

Actual native energy summability, completed joint Hardy cubic compatibility, and strict contraction remain open. C9.24A and C9.25 close source subtraction and two paid channels only. Goal ACTIVE; no RH proof or falsification.

## Log

- 2026-10-04 C9.24A: five audited complete-pole theorems; global adaptive-label law.
- 2026-10-04 C9.25: diffuse actual completion, unchanged action, complete linear and absolute-diagonal critical budgets; four audited theorems. Full signed Q remains open.

## 2026-10-04: C9.26 signed cross-work attack

C9.25 revalidated as progress (four audited actual-source theorems), not an RH estimate. Current corpus search: /tmp/tg-c926-signed-cross-search.json. Complete coprime rows and square-index cross control re-read.

First attempted argument: sum the existing decaying complete-row estimates over all nontrivial indices, then isolate endpoint energy. This fails structurally: row 1 contains q(T) times the entire dilation sum, so isolating q(T)^2 reintroduces exactly the unbounded signed cross term. Bounding complete rows can hide endpoint energy through cancellation; no upper bound on that energy follows. Do not re-prove the all-row polynomial bound as a substitute.

Further C9.26 attempts, all on the complete signed arithmetic estimate:

1. **Reciprocal fast-clock integration.** Apply the signed sawtooth primitive estimate before summing the Möbius labels, instead of bounding the two profiles pointwise. For the high-clock profile at s<=T/2 the available primitive estimate costs exp(s-T)*sum_(a<=N)|mu(a)|a. At the midpoint this can be of order N, not order one. Pairing it with the low-clock profile or its jump variation therefore does not pay the quadratic work at order N. Keeping the actual signs replaces this loss by an unproved signed primitive estimate; no cancellation theorem was obtained. The existing uniform bound for one unweighted reciprocal correlation cannot be summed absolutely over N² pairs.

2. **Moving Euler renewal.** The exact equation is D-A_P=rough_P*(rough_P*D), in logarithmic dilation notation. At P=N!, N=floor(exp(T/2)), the residual vanishes and A_P(T)=D(T); this is the already-audited half-head identity, not an independently bounded forcing term. A smaller cutoff leaves actual earlier signed D-values. The factorial deleted-force coefficient-energy bound and disjoint coefficient supports do not give orthogonality of those delayed profiles. No contracting recurrence was proved. In particular, the fixed-P critical-mass obstruction does not itself prove a moving-P obstruction; no such transfer is asserted here.

3. **Retain the logarithmic weight in the reciprocal pairing.** It is not enough to analyse the ordinary first-half profile alone. With H=T/2, x=exp(s), m=floor(x), and 0<=s<=H, let h=sum_(n<=m)mu(n)/n, hlog=sum_(n<=m)mu(n)log(n)/n, M=sum_(n<=m)mu(n), Mlog=sum_(n<=m)mu(n)log(n), and psi=sum_(n<=m)Lambda(n). Expansion of the actual weighted profile gives

       A_T(s)=x*((H-1)*h-hlog) -(H-1)-psi
                  -((H-1)*M-Mlog)/2.

   Paper derivation: expand fract(x/n)-1/2, use sum mu(n)floor(x/n)=1, and use sum mu(n)log(n)floor(x/n)=-psi. The latter follows by divisor reindexing from `sum_divisors_moebius_mul_log` in LocalizedHalfDensityCurvature. This is a paper identity, not a new Lean-audited theorem. It restores the actual prime current in the first-half factor. Applying separate absolute bounds to these five terms again loses the needed cancellation. No signed estimate follows from this expansion alone, so no identity-only leaf was added.

Contribution assessment: C9.26 has not closed a hard mathematical gap and has added no Lean theorem. These are failed proof steps, not falsifications of Q's critical bound. The next attack must estimate the coupled weighted profile against the opposite causal profile, including its endpoint and jump terms and the reflected main/error work. Do not repeat diagonal estimates, positive renewal majorants, or a bare reflection identity.

Search evidence: signed-cross, reciprocal, and moving-renewal deep searches in /tmp/tg-c926-*-search.json returned nonpartial results with complete source inventories; background compiler refresh remained incomplete. Candidate lemmas, source arguments, proof ideas, and ingredient sets were inspected. The suggested coprime-count and truncated-reconstruction ingredients only recover identities; the proposed prime-gap/Euler linkage does not supply the required signed estimate. No unrelated Route P source result was transferred to TG.

The fourth search, /tmp/tg-c926-logweighted-prefix-search.json, also completed nonpartial with a complete source inventory and incomplete background compiler refresh. Its Abel-normalization limits do not supply a critical-rate bound for the coupled pairing. `LogarithmicMellinPrefixOscillator` was read: the fixed-prefix conserved quantity is the indefinite charge h_N*M_N, and its arithmetic entry jump includes an uncontrolled signed cross term. Neither between-entry conservation nor entry continuity supplies a positive global energy bound. All four owned searches terminated normally. No owned Lean process was started, no Lean source was changed, and no new formal audit is claimed for this turn.

## 2026-10-04: C9.27 coupled weighted integration attempt

Previous turn classification: no progress toward the hard signed estimate;
it supplied failed-step evidence and a paper expansion, not a new bound.
The current card and actual source definitions were revalidated before this
attempt. No external blocker prevents further research.

The attempted integration-by-parts estimate keeps the first-half weighted
profile A_T and the opposite full causal profile together. Two precise
points emerged:

- The suggested `tendsto_criticalLogBoundaryTerm_zero` cannot remove the
  moving boundary. In the actual pairing the dilated physical argument is
  exp(T-s)/b. With s near T/2 and b near floor(exp(T/2)), this argument stays
  near one; it need not tend to infinity. The theorem's phase-dependent
  boundary bound is valid, but its limiting hypothesis does not describe
  this part of the pairing. No source boundary was discarded.
- For 1<n<=N, the interior jump at s=log n of the actual first-half
  weighted profile is

      jump A_T = -Lambda(n) + mu(n)*(T/2-1-log n)/2.

  The ordinary first-half profile has jump mu(n)/2. Paper derivation:
  existing divisor terms jump by minus the full weighted divisor sum;
  the newly entering n-term starts at sawtooth(0)=-1/2 rather than
  inheriting a whole sawtooth jump. Use sum_(d|n)mu(d)=0 and
  sum_(d|n)mu(d)log d=-Lambda(n). At n=1 the initial weighted entry is
  -(T/2-1)/2 and must be treated separately. This is a paper calculation,
  not a new Lean theorem. Thus integration by parts retains a literal
  prime-current pairing, a Möbius entry pairing, and endpoint/continuous
  work. The prime-current term is not a diagonal error and has not been
  bounded. Analysis of this half alone also does not dispose of the
  reflected half or the reflected source main/error work.

A second attempt used the corpus's actual Mellin prefix charge h_N*M_N.
An auxiliary one-sided polylogarithmic lower bound would constrain a
coupled arithmetic statistic, but neither that bound nor its sufficiency
for the complete Q estimate was proved. Prime deletion preserves a mixed
scale cross term: if A,B are respectively the p-coprime Mertens and
harmonic prefixes and A',B' their prefixes at floor(N/p), then

    M_N=A-A',  h_N=B-B'/p,
    h_N*M_N=A*B+A'*B'/p-A'*B-A*B'/p.

Multiplicativity accounts for the deleted coefficients, but gives no sign
or independent bound for the last two terms. Consequently this is not
being promoted to a replacement RH receiver or a solved contraction.
Existing |h_N|<=1 and logarithmic Mertens savings do not give a
polylogarithmic bound for their product. The existing critical-tail
obstruction also rules out treating N*h_N^2 -> 0 as an available fact:
the apparent zero-limit result in BaezDuarteMobiusPrefixApproximation
explicitly assumes vanishing full error, and
BaezDuarteMobiusCriticalTailObstruction disproves that decay.

Read source evidence additionally includes CCMPrimeDeficitResidualPairing,
CCMPrimeDeficitResidualReflection, CCMPrimeDeficitBoundaryReflection,
CCMPrimeDeficitBoundaryOscillator, CCMPrimeDeficitBoundaryNoetherBalance,
LogarithmicSawtoothTail and relevant spans of the arithmetic flux and
critical-tail modules. In particular, the bilocal-current derivative is
only a between-entry identity; its omitted impulse terms cannot be
replaced by conserved positive energy.

Both deep searches /tmp/tg-c927-coupled-pairing-search.json and
/tmp/tg-c927-mobius-charge-search.json completed nonpartial with complete
source inventories and incomplete background compiler refresh. All
candidate/argument/idea/ingredient sections were inspected. The first
suggested an inapplicable moving-boundary limit; the second mixed a
harmonic Möbius bound with prime-harmonic Mertens theorems, which do not
bound the Mertens function. All owned jobs terminal. No Lean source edit,
new Lean theorem, numerical computation, or claimed formal audit.

Assessment: no hard gap closed. Q's critical signed bound remains the
active mathematical conjecture. The next proof attempt must estimate the
complete mixed jump/continuous work, preserving the Lambda and mu terms
above and both reflected halves; no representation-only formalisation is
warranted until it supplies such an estimate. Native energy, completed
joint Hardy cubic compatibility, strict contraction and RH remain open.

## 2026-10-04: C9.28 signed kernels and causal energy attempt

Previous contribution: C9.26–27 excluded unjustified estimates but did not
close the actual signed-work gap. No Lean changes or new formal theorem in
C9.28 so far. The target remains the complete Q above, with all tail and
mixed terms.

1. **Prime-deletion correlation conjecture fails on paper.** For a fixed
   nonempty finite set S of distinct primes, P=product(S), define the
   auxiliary finite Laplace packet F_S(x)=sum_(d|P)mu(d)exp(-d*x).
   Its dilation covariance is

       C_S(q)=integral_0^infinity F_S(x)F_S(q*x)dx
             =sum_(m,n|P)mu(m)mu(n)/(m+q*n).

   Finite rational expansion, using sum_(m|P)mu(m)=0, gives

       lim_(q->infinity) q^2*C_S(q)
         =-product_(p in S)(1-p)*product_(p in S)(1-p^(-2)).

   Thus even nonzero cardinality gives eventual negative covariance;
   odd cardinality gives eventual positive covariance. Inserting a new
   prime q gives the exact finite energy recursion
   E_(S union {q})=(1+1/q)E_S-2*C_S(q), so the proposed nonnegative
   covariance step is false even on literal finite Euler packets. The
   positive paper survivor is the exact parity-dependent coefficient,
   not a uniform moving-core estimate. This is NOT Lean-audited and no
   identity or domination relating this auxiliary covariance to TG's Q
   has been established. It does not refute RH or the Q conjecture. No
   unrelated auxiliary no-go leaf has been added or route retired.

2. **Causal nilpotence does not bound mixed energy.** Re-read
   LogarithmicMobiusShortReconstruction and
   CCMPrimeDeficitTruncationDefect: the squared truncated inversion
   defect vanishes before its squared support threshold. This proves
   exact reconstruction, but it only removes a causal tail–tail
   convolution. It gives no norm bound for the retained mixed term.
   CCMPrimeDeficitShortSourceMatrix already proves determinant -1 for
   the actual two-point source matrix. Neither that existing general
   indefiniteness result nor causal nilpotence settles its value on
   the actual moving Möbius vector.

3. **Combined drift integration has not supplied arithmetic control.**
   With E(t)=exp(t)-psi(exp(t)) and D'=E, the chronological work is
   integral D +2D(T)-integral exp(-t)(D+2E_pre)dpsi.
   Replacing dpsi by exp(t)dt-dE and integrating by parts retains every
   jump square but recovers the existing storage/energy balance. It
   produces no upper estimate. Positivity of storage gives the lower
   work bound already in the corpus, not the needed upper bound.
   Any further argument here needs information about actual prime
   entries beyond this Stieltjes identity.

Searches /tmp/tg-c928-signed-kernel-search.json,
/tmp/tg-c928-euler-correlation-search.json, and
/tmp/tg-c928-causal-energy-search.json completed with partial retrieval
and complete source inventories; compiler refresh remained incomplete.
Candidate lemmas, source arguments, proof ideas and ingredient sets were
inspected. The latter two report unfinished semantic_retrieval. Suggested
inversion/energy identities do not provide an actual Q estimate. A fourth
chronological-drift search is in progress. No cross-route source transfer
or claim of exhaustive absence is made.

C9.28 close: the chronological-drift search completed nonpartial, with full
source inventory and incomplete compiler refresh. All four result sections
were inspected; its sampled-work and prime-entry identities supply no upper
bound for the actual signed work. All four searches terminated. No Lean source
changed and no new Lean audit is claimed. Q and all RH gates remain open.
The next concrete candidate is recorded separately as TG-C9.29 in
../3-formalized/tg-native-damped-current-carrier.md: test the actual operator continuation
proposal using physical head Mellin probes, rather than transfer an unrelated
auxiliary covariance. This does not abandon or discharge Q.
