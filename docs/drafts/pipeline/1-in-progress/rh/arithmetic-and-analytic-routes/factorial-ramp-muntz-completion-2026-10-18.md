# Factorial-ramp arithmetic completion

Status: IN PROGRESS. Route: RW; framework: BiScaleUncertainty.
Ultimate goal remains unconditional RH in Lean; this card does not redefine it.

## Current evidence

`FactorialWeilGramDecoupling.lean` leaves the literal ramp diagonal unsigned.
`CCMBVMuntzSummation.lean` proves that the arithmetic sum of a bounded,
compact, bounded-variation, zero-mean seed has Mellin transform zero at every
zeta zero in the right half-plane. No matching seed for the actual factorial
ramp is presently identified by the inspected source.

## Conjecture and hostile audit

Let N=n+1, epsilon=sourceFactorialCollar N, and r=clampedRamp epsilon.
Set b_N(t)=1_(t>0)[r(t/(4N))-4r(t/(2N))+4r(t/N)].
Conjecture: its full arithmetic sum A_N(t)=sum_(j>=1) b_N(jt)
is an explicit zero-mean Muntz completion of the actual ramp:

* exp(x/2) A_N(exp x)/sqrt(N)=sourceFactorialRamp N x for x>=0;
* A_N is uniformly bounded independently of N;
* its Mellin transform vanishes at every right-half-plane zeta zero;
* the omitted negative-logarithmic tail has an explicit O(1/N) square mass.

The seed is arithmetic and independent of zeros. No RH or Weil sign is assumed.
The positive/negative tail split must be justified; identifying a null completion
does not make either truncated piece null or positive. The previous balanced
source coercivity cannot supply the pure-ramp sign because the tent cancels.
Verdict: SURVIVES PRELIMINARY ATTACK as a source identification and tail producer,
not yet a solution of the diagonal-sign problem.

## Plan and proof obligations

1. Prove seed support, bounded variation, and exact zero integral before Lean.
2. Identify the entire positive-logarithmic half with the actual compact ramp,
   retaining cutoff endpoints and the positive collar.
3. Prove the uniform arithmetic-sum bound, quantitative missing-tail bound,
   and source-specific Muntz annihilation theorem.
4. Audit direct leaf modules, axioms, imports, index, and formal lint.

## Dependency-closed paper proof

Write p_a(t)=1_(t>0) r(t/a), a>0. It is measurable, bounded between zero
and one, and supported in (0,a(1+epsilon)]. On the whole real line,
p_a(t)=r(t/a)-1_(t<=0). Each term on the right is antitone with range
[0,1], hence has variation at most one. For
b=p_(4N)-4p_(2N)+4p_N, the shared step has coefficient -1, so the
triangle inequality for finite partition variations gives Var(b)<=10.
There is no numerical experiment in this estimate.

Scaling Lebesgue measure gives integral p_a=a integral p_1. Therefore
integral b=(4N-8N+4N) integral p_1=0. Its support is (0,L],
L=4N(1+epsilon). The corpus Muntz theorem now applies with every seed
premise discharged. It gives Mellin(A)(rho)=0 at every zeta zero with
Re(rho)>0. Its Riemann-sum estimate also gives |A(t)|<=Var(b)<=10.

For x>=0, t=exp(x)>=1. For j>K, with K in {N,2N,4N}, the collar
budget epsilon K<=1 implies jt>=K+1>=K(1+epsilon), so p_K(jt)=0.
Thus each infinite sum truncates exactly at K, including all atomic
endpoints. Distributing the three finite sums gives
exp(x/2) A(exp x)/sqrt(N)=rampBiNull epsilon N x, precisely the actual
sourceFactorialRamp N. For x<=0 the latter is identically zero.

Define F(x)=exp(x/2) A(exp x)/sqrt(N), and T(x)=1_(x<0) F(x).
The previous equality and the zero value at x=0 prove F=R+T pointwise.
Measurability follows from locally finite arithmetic sums. On x<0,
|T(x)|<=10 exp(x/2)/sqrt(N), so T squared is integrable and
integral T(x)^2 dx <=100/N, since integral_(-infinity,0) exp(x) dx=1.
This establishes every claimed source identity and tail estimate without
an arithmetic or spectral sign premise. The full Weil sign remains open:
small L2 tail mass does not control the singular archimedean energy.

Paper status: proved as above. Lean status: pending. In particular no claim
of a proved compact-source Weil sign or RH is made.

### Exact compact-source readout

For Re(s)=sigma>0, the logarithmic readout of F is
integral exp((s-1/2)x)F(x) dx = Mellin(A)(s)/sqrt(N), by t=exp(x).
It is an admitted integral: F vanishes above log L and its weighted absolute
value is at most 10 exp(sigma x)/sqrt(N) below log L.
The compact ramp readout is admitted by continuity and compact support.
The tail readout is consequently admitted as their difference. At any
right-half-plane zeta zero rho, the full readout vanishes, so the actual
compact-ramp readout equals minus the omitted-tail readout. Moreover,
its absolute value is at most
10/sqrt(N) integral_(-infinity,0) exp(Re(rho)x) dx
=10/(sqrt(N) Re(rho)). This also supplies a quantitative source-specific
zero-readout producer, without assuming RH or dropping the omitted tail.

## Implementation checkpoint

- `FactorialMuntzSeed.lean`: direct canonical leaf audit passed, empty log
  `/tmp/hgt-muntz-seed-final.log`; `.olean` and `.ilean` produced.
- `FactorialMuntzCompletion.lean`: scratch and canonical output audits passed;
  `/tmp/hgt-muntz-completion-check.log` and `/tmp/hgt-muntz-completion-final.log`
  are empty. `.olean` and `.ilean` produced. Exec session 28772 is terminal.
- `FactorialMuntzTail.lean` was copied into the tree. Its original scratch
  check found one `IntegrableOn.integrable_indicator` elaboration mismatch;
  the call is now explicit. Later checks failed at import loading because a
  concurrent worker is rebuilding shared dependencies. Sessions 74474, 70094,
  and 38181 are terminal; no owned Lean process is running at this checkpoint.
  The last missing shared object was `WeilPositivitySummablePerturbationRigidity`;
  the other worker owns its live build. Recheck availability before retrying.
- `/tmp/hgt_FactorialMuntzReadout.lean` is a complete proof attempt, including
  reflected-source readout decay, but has not yet been checked. The same
  `IntegrableOn` elaboration issue was fixed before its first check.
- The readout attempt has now also been copied to `FactorialMuntzReadout.lean`.
  All four module imports are wired into `BiScaleUncertainty.lean`; Tail and
  Readout are still unverified, so umbrella wiring is not a proof claim.
  A later Tail retry (session 20786, terminal) again stopped at import loading,
  now `WeilPositivityFiniteLevelExistence`. Do not repeatedly retry while the
  external dependency rebuild continues. The latest inventory found several
  other missing dependency objects. No proof diagnostic was obtained.
- `scripts/formal_tools.py index` passed in session 21333; log
  `/tmp/hgt-muntz-index.log`. Lint session 22098 exited 1 with ten unreachable
  BiScale modules, four belonging to this contribution before the imports above
  were added and six belonging to concurrent contributions. No forbidden
  declaration was reported. Rerun lint after final changes; do not claim its
  global gate passed. Axiom audit of all 28 public theorems is prepared at
  `/tmp/hgt_muntz_axioms.lean`, with source hashes and pending statuses in
  `/tmp/hgt-muntz-audit-manifest.json`; it has not run.
- Still required: finish Tail and Readout direct checks, audit axioms from
  `/tmp`, refresh the index after final changes, rerun
  formal lint, record remaining diagonal-sign obstruction, and clean scratch.

Concurrent changes to other ramp, cycle, BVI, README, and route-ledger files
are not owned by this contribution. Preserve them.

## Route rotation checkpoint

User explicitly requested rotation across all 27 live routes and 18 candidates.
All 45 open obligations in the read-only frontier map were reviewed on 2026-10-18.
RW is now audit-only. While its shared dependencies were unavailable, work
rotated to TH and proved the actual enriched clock-current sign on the inner
large-action region. Direct leaf and axiom audits passed; see
`../../../3-formalized/theta-inner-large-action-current-2026-10-18.md`.
The next research cycle must reassess a different route family or candidate;
do not automatically extend the ramp chain or tune the TH threshold. BVI has
concurrent workers; avoid their write scopes. All unfinished RW direct and
axiom checks above remain required once shared dependencies are available.

Latest RW dependency inventory found eight unavailable shared objects plus
the unbuilt Tail leaf; the external rebuild remained active. No owned Lean
process remains active after the TH axiom audit. Final index passed and final
lint reported five unrelated concurrent umbrella-coverage errors; logs are
`/tmp/hgt-rotation-final-index.log` and `/tmp/hgt-rotation-final-lint.log`.

## Constraints

Corpus only; no web or novelty claim; no numerical experiments. README files and
RH frontier map remain read-only. No full/umbrella build, added axioms, proof
debt, heartbeat increase, commit or push. Existing concurrent ramp-diagonal and
cycle work is outside this card's write scope.

## MSC rotation checkpoint — 2026-10-18

The next substantive cycle moved to MSC and completed an unconditional unweighted
squarefree critical Hilbert source (card in `3-formalized`). RW stayed audit-only.
A fresh full import inventory still found five missing shared dependency objects:
`ThetaCuspHawkingBMJointSourcePrincipalContinuation`, `WeilArchReLevyPoleForm`,
`WeilFullConeWindowPinning`, `WeilWorkPBAPGramPackets`, and
`XiGaussianHeatZeroFreeHalfPlane` (all in `GaloisForLFunctions.RHTower`).
External build PID 37778 remained live. No duplicate build or futile leaf retry
was started. Tail, Readout, and their 28-declaration axiom audit remain pending;
Seed and Completion retain their earlier verified status. Latest inventory:
`/tmp/hgt-muntz-missing-latest.txt`. No owned Lean process remains running.

### RB rotation checkpoint (2026-10-18)

RW received no new extension during the RB cycle. The Tail/Readout audit remains pending: a fresh transitive-import inventory still finds five missing shared objects, in addition to the not-yet-built Tail object. No replacement build of another worker's dependency chain was started. Missing shared objects:

- `GaloisForLFunctions.RHTower.SelbergNativeConstantMode`
- `GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedCombinedMeanSquare`
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPositiveRows`
- `GaloisForLFunctions.RHTower.WeilPaperPacketRepair`
- `GaloisForLFunctions.RHTower.XiGaussianHeatHankelLargeTimeDetection`

Inventory: `/tmp/hgt-muntz-missing-rb-checkpoint.txt`. Recheck shared object availability before retrying the owed canonical audit; do not extend RW while rotating the other routes.

### SZ-cycle audit checkpoint — 2026-10-18

Fresh import inventory still prevents the pending RW audit. Tail's closure lacks four shared
artifacts: `SelbergThetaHorizontalTransform`, `Sieve.DifferentiatedBarbanVehovLcmExpansion`,
`Sieve.PerronKernelCellSum`, and `XiGaussianHeatSharpWitnessComparison`. Tail and Readout's own
artifacts also remain pending. Inventory: `/tmp/hgt-sz-pending-imports.txt`; import graph:
`/tmp/hgt-sz-final-imports.txt`. No duplicate dependency build or RW Lean retry was launched.
The substantive cycle advanced SZ instead. Retain RW as audit cleanup, not the next research topic.
