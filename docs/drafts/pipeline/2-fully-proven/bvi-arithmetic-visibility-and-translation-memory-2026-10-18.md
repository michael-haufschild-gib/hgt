# Arithmetic visibility and memory of true integer translation

- **ID:** bvi-arithmetic-visibility-memory
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper proof; Lean pending)
- **Source:** Optimal one-step prediction, exact CRT lag counts, Ramanujan/divisor
  Fourier infrastructure, and the field's prime-valuation distinction.
- **Statement:** Determine when later integer shifts reveal information erased by
  the best one-step divisor-sieve predictor, and classify the observations needed
  to recover the original arithmetic signal.

## Significance gate

Contribution010 proves that one-step prediction erases every nonsquarefree
Selberg mode. It does not prove that true later shifts erase those modes.
The missing structural question is whether that apparent loss is permanent,
or governed by a valuation-dependent arithmetic visibility schedule.

Do not count an arbitrary-lag substitution into a known diagonal formula or a
generic iteration of the existing multiplier as a contribution. Require a
nontrivial arithmetic recovery/visibility classification with an actual integer
translation realization. Audit any semigroup or memory claim against the true
shift before committing. No externally averaged family or asymptotic assertion.

## Initial audit and plan

- Previous goal turn: PROGRESS. Contribution010 source and installed-artifact
  hashes revalidated against its durable audit; cleanup verified. Count10 / 250.
- Objective, root/formal instructions, full363-line field README, formal guides,
  pipeline template and relevant memories read. Architecture/testing docs absent.
  Current field inventory30 leaves; concurrent work preserved. README read-only.
- Documented deep searches launched with90-second budgets:
  `Ramanujan lag prime power visibility` and
  `sieve compressed translation memory projection`.
- Existing `TwoLagMomentCone` has public exact lags0,1,2, but its general
  kernel-to-diagonal machinery is private. `DivisorSieveAffineSpectrum` supplies
  affine DFT data classification. Check applicability and equivalent results.

1. [x] Inspect every returned search section and relevant current sources.
2. [x] Close a dependency-complete paper result and novelty/significance audit.
3. [x] Probe installed APIs; formalize the exact unconditional result.
4. [ ] Original-source checks, every public axiom closure, wiring, complete index
   audit, lint, artifact installation, ledger/memory, cleanup; only then count011.

`update_plan` and `multi_tool_use.parallel` are unavailable. This card is the
durable plan; independent reads use Promise.allSettled. Temporary prefix
`/tmp/bvi11-*`. One owned Lean process at a time, terminal exit before next launch.
No web, hgtl7, RH focus, numerical experiments, README edits, full/umbrella builds,
heartbeat changes, commits, pushes or subagents.

## No-go closure

If compressed succession fails to model true multi-step translation, extract
and prove the strongest positive survivor: exact invisible/visible modes,
recovery criterion, minimal observation schedule, or arithmetic memory invariant.
Record paper and Lean status before closing the obstruction.

## Corpus audit

Three documented deep searches completed: `Ramanujan lag prime power visibility`,
`sieve compressed translation memory projection`, and `Ramanujan totient quotient
gcd`. All candidate declarations, source arguments, proof ideas and ingredient
sets inspected; passage/prose inventories inspected for relevance, with relevant
current sources read. Visibility/quotient searches reported no partial result,
but semantic coverage was unmeasured and coverage snapshots older than current
generation. Memory search was partial: local semantic runtime deadline expired,
with deadline/filter-and-judge unfinished. No claim of exhaustive semantic search.

Focused lexical `"squarefree" "gcd" "quotient"` returned one declaration,
`squarefree_divisor_betaPrefix_eq_clockResidual`; its current source transports
an already squarefree modulus through a clock and does not classify visibility
of arbitrary modes. All 87 focused text hits in the field, BiScaleUncertainty,
RHTower and Mathlib number theory inspected. Existing prime-power Ramanujan
two-layer formulas, primitive Fourier conservation, affine comparable-product
data, and analytic phase-valuation tomography are prior infrastructure, not this
contribution. The normalized Ramanujan identity and finite Möbius inversion are
classical ingredients; no novelty claimed for them.

## Closed paper statement and proof

Let `I={1,...,N}`, `P=N!`, `S_c(k)=sum_(d in I,d|k)c(d)` and
`Y_c(q)=sum_(d in I,q|d)c(d)/d`. Put

`R(q,h)=sum_(d|q) mu(q/d) * d * 1_(d|h)`,
`lambda(q,h)=R(q,h)/phi(q)`, and `D(q)=q/prod_(p|q,p prime)p`.
At q=0 use the displayed finite-divisor/total-division definitions: R=lambda=D=0.
Define `K_h c` by the existing finite multiples inverse of `lambda(q,h)Y_c(q)`.

1. **Literal shift and optimal compression.** For arbitrary real coefficient
   functions b,c and every natural N,h,

   `P^-1 sum_(k=1..P) S_b(k)S_c(k+h)
       = sum_(q in I) R(q,h)Y_b(q)Y_c(q)
       = P^-1 sum_(k=1..P) S_b(k)S_(K_h c)(k)`.

   CRT gives each divisor-pair density `1_(gcd(a,d)|h)*gcd(a,d)/(a*d)`.
   Möbius inversion gives `sum_(q|g)R(q,h)=g*1_(g|h)`. Substitute and interchange
   finite sums; both divisor sums become the exact multiples coordinates.
   Finite inverse and the existing same-node totient pairing give the last
   equality. Expanding squares and cancelling the mixed residual pairing gives
   `Err_h(c,b)=Err_h(c,K_h c)+Q(b-K_h c)`.
   Positive totient weights and coordinate injectivity classify every minimizer
   by equality of active raw coefficients. No external averaging parameter.

2. **Arithmetic visibility.** For q>0 write g=gcd(q,h), t=q/g. Divisor
   involution d=g/e and the elementary law
   `mu(t*e)=mu(t)mu(e)1_(gcd(t,e)=1)` yield
   `R(q,h)=mu(t) sum_(e|g,(e,t)=1)mu(e)*(g/e)`.
   The corpus theorem `TotientMulMoebius.totient_mul_eq` identifies the latter
   sum with `phi(q)/phi(t)`. Thus `lambda(q,h)=mu(t)/phi(t)`.
   It is nonzero iff t is squarefree. For h>0 the p-valuation of t is
   `v_p(q)-min(v_p(q),v_p(h))`; that is at most one iff
   `v_p(q)-1 <= v_p(h)`, exactly `D(q)|h`. At h=0, t=1 and D(q)|0;
   q=0 has zero multiplier. Therefore universally
   `lambda(q,h) != 0 iff q != 0 and D(q)|h`.
   In particular mode p^(a+1) has first positive visibility at p^a.

3. **Exact finite observation schedule.** For any finite H and arbitrary b,c,
   `K_h b` and `K_h c` have equal active coefficients for every h in H iff
   `Y_b(q)=Y_c(q)` for every active q for which some h in H satisfies D(q)|h.
   This follows coordinatewise from the nonzero criterion and injectivity.
   Consequently the schedule recovers every active coefficient of every signal
   iff each active q has such an h. If not, the finite inverse of the unit
   profile at that q is an explicit nonzero invisible signal, proving necessity.
   The same classification holds for literal shifted pairings against every
   divisor probe, by the actual-shift identity and single-coordinate probes.

4. **Sharp horizons and memory obstruction.** Set T_N=max_(q in I)D(q),
   with empty maximum zero. Positive consecutive lags 1..T recover all signals
   iff T_N<=T: a positive multiple of D(q) occurs in that window iff D(q)<=T.
   A single lag h recovers all signals iff every D(q) divides h (equivalently,
   their finite lcm divides h). N=0 is vacuous throughout. For any active
   nonsquarefree q, its unit-coordinate signal is erased at lag1 but visible
   exactly at multiples of D(q), including D(q) itself. A zero state cannot
   recover under repeated one-step prediction, while true translation can.
   This is an exact arithmetic memory obstruction and a positive recovery law.

All helpers' positivity/divisibility premises follow from active index
membership or are discharged by the explicit zero cases. Finite schedules,
signals and lags are unrestricted. No asymptotic or numerical input.
Recovery reconstructs source coefficients from compressed observations; the
shifted signal can still have nonzero optimal prediction error. No noise or
uniform conditioning estimate is part of the claim.

## Significance decision

Count the complete result as one contribution only after formal audit. Its new
content is the valuation-dependent erasure/reappearance schedule, exact
observation equivalence with explicit invisible witnesses, and sharp recovery
horizon for the actual integer-translation compression. Generic diagonalization,
Ramanujan quotient evaluation and finite inverse are supporting infrastructure.
Do not count the separate identities or horizon corollaries independently.
No full semigroup classification is asserted. Paper proof closed; Lean pending.

## Lean work in progress

User cleared the 250-contribution goal, then explicitly requested finishing the
work already started. Finish this contribution and its audits/cleanup, then stop.
Do not open another research topic or recreate the goal.

Four draft leaves, all under the field directory:
`RamanujanLagCoefficientAndTotientQuotient`,
`ValuationVisibilityClockAndRamanujanSupport`,
`TrueTranslationPredictionAndExactCompression`, and
`ArithmeticLagSchedulesAndSharpRecoveryHorizon`.
Installed API probe passed with terminal exit0. First original-source check
found elaboration/cast details in the Ramanujan foundation; repaired, sequential
recheck running. No theorem counted yet. Isolated environment `/tmp/bvi11-formal`
uses cloned `/tmp/bvi11-olean-cache`; no shared full build or heartbeat override.

Concurrent `IteratedSuccessorPredictionAndReservePhaseLossSplit` appeared during
this work. Its iteration section was read: powers of the one-step predictor
contract above parity, and its remaining section compares reserve and phase
loss. It does not identify powers with true shifts or classify their recovery
times. Preserve that work and keep the present contribution centered on actual
translation, valuation visibility and observation schedules.

The combined development check now passes with empty diagnostics. All four
original named sources then passed separate `lake --old env lean --root=... -o
... <original-source.lean>` checks with empty diagnostics, one owned Lean process
at a time. Every public declaration, including definitions, passed its `/tmp`
`#print axioms` audit:38 reports, exactly `propext`, `Classical.choice`, `Quot.sound`.
Additional installed-API probes passed in the same terminal exit0 audit. The
four verified artifacts were installed atomically; umbrella imports added.
Index/lint audit and cleanup remain before counting completion.
