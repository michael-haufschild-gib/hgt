# Sharp recovery clocks for corrupted valuation observations

- **ID:** thim-corrupted-valuation-clock-recovery
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); uncounted formal sharpening
- **Source:** Existing finite observation state, successor phase refinement, and
  exact prime-power totient observation theorem.
- **Statement:** Determine the exact finite-window distance of native valuation
  traces and the sharp observation latency with adversarial errors and erasures.

## Scope and counting

**Current decision: FORMALIZED, UNCOUNTED. Qualified programme count stays 1/100.**
Four leaves and 24 public declarations establish the exact consecutive-window
recovery law for literal horizon states. All named source/olean checks passed;
final imported-axiom audit, generated index, and lint are the remaining integration
gates. Earlier checkpoints below are historical.

The native closed formula was not found in the retrieved corpus. Nevertheless,
its local mechanism is a short extension of the existing totient collision and
observability results, coupled to classical ultrametric resolution, CRT, and the
standard errors-and-erasures criterion. Under this programme's strict significance
standard, retain this as useful verified infrastructure and do not award a new
contribution. This is a conservative significance judgment; it does not assert
that a cited paper already states the identical native formula.

## Prior work checked before the candidate

Actual corpus research queries included:

- `horizonObservationState successor valuation phase multiplicative observation`
- `valuation gcd trace Hamming distance error correction prime power observation`
- `gcd shifted trace disagreement count prime power valuation collision multiplicity`
- `corrupted valuation phase observation gcd trace minimum distance error recovery`
- lexical `Hamming hammingDist --any --module TransHorizonIncidenceMechanics --per-module 0`

The focused observation query recovered prior work missed by the broad query:
`prime_pow_trace_injective_iff_totient_le` and
`horizonObservationPhase_eq_iff_totient_trace` in
`TotientObservabilityThresholdAndValuationFiberCollision.lean`. Source through
the global theorem was read. Reuse its exact threshold, collision pair,
sub-ceiling GCD reduction, divisibility-return construction, and prime-power
phase criterion. These results are not new here.

The disagreement query returned 20 candidate statements and 20 source
arguments, all triaged. It also recovered existing shifted-divisibility CRT
counting in `EulerDeletionTruncatedDivisorPairCorrelation.lean` and the BVI
translation-stabilizer programme. Generic prime-power GCD and correlation
identities are prior work. Its proposed ingredient set only combines a
minimum-exponent GCD identity with divisibility of a shift; that does not prove
   the finite-window distance formula. The corruption query's 20 candidate and
   20 source-argument statements were also triaged. Its retrieved noiseless
   proof is reused; its proposed harmonic-counterterm/valuative-relation
   ingredients do not concern corrupted observation symbols and are rejected.
The narrow THIM Hamming lexical query returned zero; this is not absence or
priority evidence. Source/compiler freshness is mixed despite complete
retrieval runs. No global priority claim.

External baseline: [Toth–Haukkanen, The discrete Fourier transform of r-even
functions](https://arxiv.org/html/1009.5281v1) treats GCD-fibre functions and
their convolution/Fourier algebra; that machinery is classical. The official
[Codeforces 1665D editorial](https://codeforces.com/blog/entry/101663) already
uses shifted GCD queries to recover successive binary digits. Adaptive GCD
lifting is therefore not pursued as a new contribution. Neither cited source
is claimed to exclude other prior work on the exact corrupted-clock problem.

## Exact paper theorem

Let `L_N = lcm(1,...,N)` and let `sigma_N(k)` be the existing
`horizonObservationState N k`. It is the complete state for all real sieve
weights. Its mathematical description is `gcd(k,L_N)`; the implementation
bridge must be checked rather than assuming a public theorem exists.

Observe `sigma_N(k+t)` for `0 <= t < W`. An adversary may erase at most `s`
positions and replace at most `e` of the remaining observations by arbitrary
natural numbers. Recovery means that any two phases compatible with the same
received trace are equal modulo `L_N`.

For a prime power `q=p^a`, `a>=1`, set

```
d_q(W) = 2*floor(W/q) + 1_{W mod q >= phi(q)},
tau_(e,s)(q) = (e+floor(s/2))*q +
              (if s is even then phi(q) else q),
T_N(e,s) = max_{q<=N, q a prime power} tau_(e,s)(q).
```

The empty maximum is zero. Sharp theorem, for every `N,W,e,s`:

```
Every compatible received trace determines the phase uniquely
    iff W >= T_N(e,s).
```

For `L>1`, let `Q(L)={p^(v_p(L)): p prime, p|L}`. A stronger distance formula
underlying the theorem is

```
min_{k not congruent l mod L}
  #{t<W : gcd(k+t,L) != gcd(l+t,L)} = min_{q in Q(L)} d_q(W).
```

The closest-pair construction must attain the distance for every window, not
only at the first noiseless threshold. The global construction must preserve
all other prime-power components.

## Dependency-closed symbolic proof

1. **Prime-power lower bound.** For distinct phases modulo `q`, each block of
   length `q` contains at least two disagreements: the distinct return times
   where one of `k+t,l+t` is divisible by `q`. A final block of length at least
   `phi(q)` contains a disagreement by the existing exact totient theorem.
   Periodicity gives the lower bound `d_q(W)`.

2. **Prime-power attaining pair.** Use the existing pair
   `k=1`, `l=1+p^(a-1)`. The traces disagree exactly when
   `t mod q` is `phi(q)-1` or `q-1`. At all other times neither argument is
   divisible by `q`; the existing sub-ceiling reduction lowers both GCDs to
   modulus `p^(a-1)`, where they agree. At either exceptional residue exactly
   one argument is divisible by `q`. Counting complete periods and the
   remaining prefix gives exactly `d_q(W)`.

3. **Coprime completion.** Distinct phases modulo `L` differ modulo some
   `q in Q(L)`, and every disagreement after projection to `q` is a full-state
   disagreement. Conversely write `L=q*r`, with `gcd(q,r)=1`. CRT lifts the
   local attaining pair while giving both phases residue zero modulo `r`.
   At every time the `r`-GCD factors are equal and positive. The identity
   `gcd(x,q*r)=gcd(x,q)*gcd(x,r)` and cancellation show that global and local
   disagreement sets are exactly equal. This proves the global minimum.

4. **Classical fault criterion.** Two words can be compatible with one received
   trace with `e` errors and `s` erasures exactly when their distance is at
   most `2e+s`. Necessity follows by covering their disagreement set by the
   erasures and the two error sets. For sufficiency erase up to `s`
   disagreement positions and divide the at most `2e` remaining positions
   into two sets of size at most `e`; choose the received symbol from the
   opposite word on each respective set. This is an auxiliary coding lemma.

5. **Exact latency arithmetic.** Write `W=m*q+r`, `0<=r<q`, and
   `s=2u` or `s=2u+1`. Then `d_q(W)>2e+s` is equivalent respectively to
   `W>=(e+u)*q+phi(q)` or `W>=(e+u+1)*q`. No approximation enters.

6. **Native horizon.** By unique factorization, the maximal prime powers
   dividing `L_N` are exactly the maximal powers of each prime not exceeding
   `N`: the exponent in an lcm is the maximum of the input exponents.
   `tau_(e,s)(p^a)` increases with `a`, since both `p^a` and `phi(p^a)` do.
   Thus maximizing over `Q(L_N)` equals maximizing over all admitted prime
   powers. The observation state is `gcd(k,L_N)`: the state divides this GCD;
   conversely each `gcd(k,d)` for `1<=d<=N` is an admitted divisor of `k`,
   and distributing GCD over the finite lcm proves the opposite divisibility.
   If `N<=1`, the phase space has one element and the empty maximum is zero.

## Paper audit outcome

The six steps are closed. For `q=p^a`, the two exceptional residues are
distinct because `0<p^(a-1)<q`; `phi(q)>=1`, so the subtractions by one are
ordinary natural representatives. In a residual prefix of length `r<q`, the
residue `q-1` is never included, and `phi(q)-1` is included exactly when
`phi(q)<=r`. The local attaining pair is independent of `W`. CRT completion
uses the **maximal** prime-power factor of `L`, ensuring that its complement
is coprime; using an arbitrary nonmaximal factor would leave a gap.

For the mixed-fault midpoint, if the disagreement set has size `d<=2e+s`,
erase `min(s,d)` of its positions. The remaining size `r=d-min(s,d)` is at
most `2e`. Partition it into sizes `min(e,r)` and `r-min(e,r)`, both at most
`e`, and use the two original symbols on the respective parts. Thus the
criterion includes arbitrary error/erasure budgets and empty windows.

The native modulus bridge also follows directly from the finite-lcm
prime-power law: `p^a | L_N` iff `p^a<=N` for prime `p`, `a>=1`. A prime
power dividing an lcm of positive integers divides one of its factors, hence
is at most that factor. This law is existing arithmetic, not a new count.

The result's native content is the exact arithmetic distance and minimax
latency, including the parity dependence on erasures. The generic coding
criterion is not new. Formal verification and final significance/priority
assessment remain open; the programme count is unchanged.

## Audit obligations and work plan

1. Finish corpus overlap and external baseline review; separate exact native
   claim from generic coding consequences. **Initial audit complete; check
   any further overlaps exposed during formalization.**
2. Audit the two exceptional residues, full-period lower bound, CRT equality
   of disagreement sets, small-horizon cases, and mixed-fault midpoint.
   **Paper audit complete.**
3. After paper closure, probe actual Lean APIs in `/tmp`, then formalize only
   the exact audited statements in new leaves with disjoint ownership.
4. Named source/olean checks; all public axioms in `/tmp`; imports, index,
   and authoritative lint. Final significance decision before any count.

## Log

- 2026-10-19 — Created after focused corpus searches recovered the existing
  noiseless theorem. Full errors-and-erasures clock law is a candidate; no
  proof certificate, new Lean leaf, or contribution count yet.
- 2026-10-19 — Closed the symbolic paper proof and its boundary-case audit.
  Promoted to fully proven on paper. No new Lean leaf or qualified count yet.


## Corpus and local Lean checkpoint — 2026-10-19

Explicit user request: use the corpus research tool and do not miss prior work.
Two further deep searches used the mechanisms “Chinese remainder coprime
completion shifted gcd trace minimum disagreement distance” and “fault tolerant
valuation observations errors erasures recovery threshold totient”. All 20
candidate statements and 20 source-argument statements from each were triaged;
all prose/source-passage heads and proposed ingredient sets were inspected.
The latter's linear-subspace erasure proposal does not model erased observation
positions and is inapplicable. CRT/root-count identities are classical ingredients,
not an existing finite-window distance theorem.

Completed all remaining lexical pages (offsets 20 through 160, per-module cap zero)
of the earlier `Hamming hammingDist trace gcd --any` THIM search: all 171 matches
are now triaged. Source-text cross-checks cover THIM/BVI and cross-module
Hamming/erasure terminology. Existing exact noiseless totient observability,
its collision pair, active-sawtooth calibrated recovery, and prime-power revival
remain prior work. No retrieved result supplies the proposed mixed-fault clock.
This is bounded retrieval evidence, not a claim of exhaustive external priority.
The deep search inventory had 74,295 files (62,448 Lean); compiler metadata was
mostly pending/stale and semantic coverage was unmeasured. Relevant source and
Lean certificates therefore remain authoritative over retrieval scores.

The local prime-power distance proof passed `lake --old env lean` in scratch,
including standard-axiom audits of all nine public declarations. Promoted to
`ValuationTraceDistanceAndPrimePowerPeriod.lean`; named leaf verification is next.
Global coprime completion, literal-state bridge, and mixed-fault equivalence remain
to formalize. Contribution count remains 1/100; this candidate is uncounted.


## Formalization and external comparison checkpoint — 2026-10-19

Three named leaves have passed direct source/olean checks with empty diagnostics:
`ValuationTraceDistanceAndPrimePowerPeriod.lean` (nine public declarations),
`ValuationTraceCoprimeCompletionAndObservationState.lean` (six), and
`ValuationTraceErrorsErasuresAndRecoveryClock.lean` (four). All 19 public
statements were axiom-audited in scratch; only `propext`, `Classical.choice`,
and `Quot.sound` occur. The finite-LCM bridge reuses
`Finset.factorization_lcm`; totient divisibility reuses
`Nat.totient_dvd_of_dvd`. These arithmetic bridges and the generic coding
criterion are infrastructure, not separate contributions.

The remaining native leaf states the exact all-parameter recovery equivalence
and produces a shared corrupted observation below the threshold. Its local
check is in progress; import wiring and final lint/index remain pending.

External comparison was extended to the publisher abstracts and displayed
parameters of [Yang–Liu, periodic partial Hamming correlation constructions](https://www.aimsciences.org/article/doi/10.3934/amc.2026021?viewType=HTML),
and the abstract of [Tani–Kunihiro, noisy binary-GCD operation sequences](https://link.springer.com/chapter/10.1007/978-981-96-1218-5_9).
The former constructs frequency-hopping families by interleaving; its full text
was access-restricted and was not reviewed. The latter studies operation traces
from a binary-GCD algorithm used in RSA key generation. Neither retrieved
statement supplies the fixed-modulus shifted-GCD window theorem. This comparison
is limited prior-work evidence, not a proof of worldwide priority.


## Final significance audit — 2026-10-19

The late, more relevant external comparison is [Corregidor–Martínez-Pérez,
*Finite metric and k-metric bases on ultrametric spaces*](https://arxiv.org/abs/2003.10239),
Theorems 2.29, 2.30, 2.33 and Corollary 2.35. These classify finite resolving
bases by nearest-neighbour partner classes and explain the two-landmark separation
ceiling. Independently, [Oliynyk–Ponomarchuk, *Metric dimension of ultrametric
spaces*](https://www.math.bas.bg/serdica/abonament/2020/2020-195-206.pdf),
Proposition 1 and Corollary 1, give the regular leaf-count difference.

Our specialization: on residues modulo p^a, the truncated p-adic ultrametric has
partner classes modulo p^(a-1), each containing p points. A GCD query is an
injective recoding of distance to its negative offset. Thus the prime-power
noiseless count phi(p^a), and the two exceptional sibling landmarks, sit inside
that known structure. This specialization is our inference from those theorems.
The papers do not state the exact repeated consecutive-window mixed-fault formula.
The formula's remaining periodic counting, coprime completion, and coding steps
are too close to these foundations to count independently under the requested
standard. The published basis results also rule out treating an arbitrary
nonadaptive query-design reformulation as an independent contribution without
substantially new arithmetic interaction.

No theorem was disproved or removed. Positive retained result: the exact native
recovery threshold, together with explicit existence of ambiguity below it, is
formalized in `SharpCorruptedValuationClockRecovery.lean`. Count increment: **0**.

Further corpus search for arbitrary query schedules inspected all 20 candidate
statements, 20 source-argument statements, prose/source heads and proposed
ingredients. Newly created clock leaves appeared in those results and were
excluded as self-hits. Existing BVI arithmetic-lag scheduling and composite clock
wavelet recovery remain prior work.
