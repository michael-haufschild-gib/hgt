
# Route TG C9.25 closed paid channels; actual signed Q open

RH goal ACTIVE, no proof/falsification. No subagents, full/umbrella builds, numerical experiments, new axioms/holes, heartbeat overrides, commits/pushes.

## New leaf
formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitNeutralWork.lean, 367 lines.
N=floor(exp(T/2)), hN=sum_(1..N)mu(n)/n.
aN(n)=mu(n) n<=N; aN(n)=-(n/N)*hN on N<n<=2N; zero thereafter.
Full harmonic moment0. Literal mu head unchanged, exact old head-extension action still actual deficit D(T).
c=1+gamma; F0(t)=actual dilationSource(t)-c exp(t).
R(t)=ccmPrimeDeficitDivisorPoleRemainder from C9.24A.
L(T)=2 sum_(1..2N) aN(n)F0(T-log n).
Q(T)=sum_(m,n in1..2N) aN(m)aN(n)R(T-log m-log n).
Absolute diagonal Bdiag=sum aN(n)^2*|R(T-logn-logn)|.

4 new public theorems:
- line64 ccmPrimeDeficitNeutralCoefficient_harmonic N: sum aN(n)/n=0.
- line230 ccmLogChebyshevDeficitPrimitive_eq_neutral_work hT: D=L-Q exactly.
- line306 ccmPrimeDeficitNeutralLinearWork_critical_bound: exists K>0 forall T>=0 |L|<=K exp(T/2)(T+1)^2.
- line345 ccmPrimeDeficitNeutralDiagonalBudget_critical_bound: exists K>0 forall T>=0 Bdiag<=K exp(T/2)(T+1)^4.

5 public defs:
line29 ccmPrimeDeficitNeutralCoefficient
196 ccmPrimeDeficitDilationPoleRemainder
199 ccmPrimeDeficitNeutralLinearWork
204 ccmPrimeDeficitNeutralQuadraticWork
338 ccmPrimeDeficitNeutralDiagonalBudget.

Proof: actual head extension; finite-support causal sum expansion including negative shifted times; C9.24A full pole/moment cancellation. Global F0 linear envelope from uniform centered source. |hN|<=1+logN and diffuse |a|<=2(1+logN)+1 give l1 <=6 exp(T/2)(T+1), l2²<=18 exp(T/2)(T+1)^2. Global R envelope pays diagonal, not offdiagonals.
Private generic finite_dilation proves causal source finite-support expansion, useful if needed but don't expose just to wrap.

## Actual hard target, do not re-prove paid channels
Unconditional exists K>0 and finite k such that |Q(T)|<=K exp(T/2)(T+1)^k, all T>=0. Original head, diffuse tail, every unequal-label and negative-time contribution retained.
No such bound proved. Native soninPrimePolarGridEnergy summability, full joint Hardy cubic compatibility, strict contraction still open.
Do NOT spend next turn changing tails, optimizing constants/powers, bounding another diagonal or producing RH equivalence wrappers. Attack complete signed arithmetic correlations.

## Failed ideas / useful learning
Single-point tail at N+1 achieves harmonic cancellation but concentrated coefficient (N+1)hN creates unpaid diagonal square mass. Replaced before tree formalization by diffuse tail above.
Diffusion does NOT pay the entire tail block: its correlations can still carry exp(T)hN². Retain head-tail and tail-tail signs.
Two-tail construction forcing quadratic work0 requires a coefficient constraint involving unknown head quadratic value; no independent bound results. Not a falsification of RH or of actual Q bound.
Midpoint reflection gives a symmetric product: integral is twice half-integral, NOT cancellation. Actual first-half sawtooth profile = exp(t) sum_(n<=exp t)mu(n)/n -1 -(1/2)M(floor exp t). Do not separate M/harmonic terms.
Source suggestions linking diagonal budget to chronological work, or midpoint symmetry to signed cancellation, rejected as insufficient. No conditional premise admitted.

## Audits
Final foreground lake --old env lean GaloisForLFunctions/RHTower/CCMPrimeDeficitNeutralWork.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCMPrimeDeficitNeutralWork.olean: exit0, empty output.
Separate /tmp/tg-c925-neutral-work-axioms.lean audit all4: exit0, only propext Classical.choice Quot.sound.
RHTower import after CCMPrimeDeficitCompletePole. No umbrella build.
Index exit0, nine API rows verified.
Authoritative lint exit1: 16 unrelated unreachable modules, no owned finding. Logs /tmp/tg-c925-neutral-work-{final,axioms,index,lint}.log.
All owned Lean/search/lint processes terminal. Seven superseded scratch files removed. Final logs, axioms source, two search JSONs retained. No source changed after final audit.

## Docs
P3 docs/drafts/pipeline/3-formalized/tg-diffuse-neutral-mobius-work.md full dependency-closed proof and audits.
P1 docs/drafts/pipeline/1-in-progress/tg-complete-divisor-pole-cancellation.md rewritten as ACTUAL Q target; no stale single-tail plan.
Main log docs/drafts/pipeline/1-in-progress/tg-principal-polar-operator-cancellation.md C9.25.
Frontier TG new row after complete-pole adaptive cancellation.
Prior mem:rh/tg-complete-divisor-pole-adaptive-cancellation-2026-10-04.

## Corpus search and reads
/tmp/tg-c925-neutral-work-search.json --mode deep --module CCMPrimeDeficit; nonpartial complete inventory, background compiler refresh incomplete. Candidates/sourcearguments/ingredients inspected: source pole law, short quadratic work, coprime balance, force/diagonal estimates; no actual Q bound.
/tmp/tg-c925-midpoint-work-search.json --mode deep --module Logarithmic; same status. Candidates/sourcearguments/ingredients inspected: reciprocal sawtooth exact convolution, half reflection, actual full-prefix arithmetic. No cancellation estimate.
LogarithmicMobiusSawtoothPrefix.lean read FULL this turn. Relevant theorem logarithmicShortMobiusInverse_centeredSawtooth_first_half, exact profile above.
Other source sources already read prior turn: CoefficientAction, TailSymmetry, FiniteEntryProfile, ShortReflection, CoprimeRows/Balance. C9.24CompletePole final public theorem segment revalidated this turn with last axioms log.

## Lean lessons
Finite cutoff split via explicit union Icc1N union Icc(N+1)(2N), disjoint_left and sum_union; tail cardinal exactly N.
Avoid nested one-line 'have := by omega; positivity': semicolon may attach to inner solved goal.
Add explicit type to chained abs_sub/add_le_add bound; underscores don't infer without expected type.
In THIS import context add_le_add_right ht 1 inferred 1+max <=1+T instead of max+1<=T+1; use linarith only[ht].
Scratch test APIs already verified sum_Icc_succ_top, sum_subset, harmonic_le_one_add_log, abs_moebiusCoeff_le_one, exp_neg/log, Nat floor APIs.
