# 018 — Whole native BV forcing through the singular theta quantile

Baseline: **17/100**. Previous turn classified as verified progress from all
ten current source/artifact pairs, unique umbrella imports, exact main theorem
declarations and the current ledger. Goal attachment reread; the full target
remains 100 significant independently justified contributions.

Status: **formalized and audited; contribution 018, total 18/100**.

Mission: unconditional structural RH progress from current Lean evidence.
Continue the hgtl7 conjecture/attack/paper-proof/formalization workflow. No web,
external novelty checks, old research reports, numerical experiments,
subagents, full or umbrella builds, heartbeat increases, commits or pushes.
One owned foreground Lean process at a time. Preserve concurrent unrelated
work. Distinguish original sources, original cohomology and completions.

Session init: Serena memories listed with filtered output; relevant 017
memory read. Architecture/testing docs absent. Current frontier map route
headings and open cores scanned. No `update_plan` tool is available; this
card is the durable plan.

Plan:
1. Search current corpus across original topological spectral synthesis,
   arithmetic duality and cross-fibre inertia; inspect exact declarations.
2. Conjecture and attack a distinct hard obstacle; routine inversion,
   holomorphic-calculus or native-transport consequences of 017 do not count.
3. Complete dependency-closed paper proof before new Lean. Then direct leaf
   audits, axioms, umbrella wiring, lint/index, exact cleanup and count audit.

Conjecture log:
- Original-Frechet finite-mode density: the available Hilbert density and
  nuclear seminorm-family statements do not pay original convergence. No
  density claim accepted. Inverse closure from 017 does not repair this gap.
- A new compact theta inverse: rejected as duplicate. The current
  `HedenmalmThetaSourceCompressedInverseDeterminant` already has the Hilbert
  inverse and exact spectrum. Its existence does not establish BV regularity
  of arbitrary forced solutions through the singular quantile.
  The current `HedenmalmThetaComplexResolventRow` already identifies the
  full inverse's scalar moment row, and `HedenmalmThetaRealResolventTrace`
  constructs its pinned AC primitive. Neither states whole-line BV of the
  source-relative forced profile. The new partition argument addresses that
  precise regularity gap; the integrating factor itself is not counted new.
- Selected conjecture: **every continuous whole-line BV forcing has a unique
  literal native solution at every nonzero imaginary shift, with a common
  two-ended trace, whole-line BV, an absolutely continuous closed-quantile
  representative, and admission to the complete signed CHMD graph.** This
  removes the finite-Xi-packet restriction from native inhomogeneous solving.

Dependency-closed paper proof (all seven leaves now audited):
Write rho for the positive normalized theta density and C(z)=integral
rho(x) exp(i z x)=XiC(z)/mass. For continuous BV g let
J(z,g)=integral rho(x) exp(i z x) g(x) and
R(z,g)(x)=integral_{h>0} [rho(x+h)/rho(x)] exp(i z h) g(x+h).
All integrals converge absolutely: g is bounded, and every tilted source
ratio is integrable (`PaperThetaSourceRatio`). When z*C(z) is nonzero set
tau=-J(z,g)/(z*C(z)), h=g+z*tau, and f=tau+i*R(z,h).

1. The weighted forcing h has zero total character moment. Changing
   variables and using theta reflection identifies the right-tail formula
   with -R(-z,h(-.))(-x) on the left. This is exact cancellation before
   dividing by the superexponentially small density.
2. Each R(z,h) has BV on every right ray. For a finite increasing partition
   x_j>=a, expand a product increment into the source-ratio difference and
   the forcing difference. Source ratios are positive decreasing in x.
   Their increments telescope; forcing increments sum to TV(h). Integrate
   the resulting bound (supnorm(h)+TV(h))*ratio(t,a)*exp(-Im(z)*t).
   Both rays therefore have finite variation. This is the new regularity
   mechanism; individual pointwise bounds do not prove it.
3. The same bound without increments controls |R| by supnorm(h) times the
   positive tilted tail/density ratio. The already-proved relative-tail
   theorem makes that ratio tend to zero. Hence both traces of f are tau.
4. Differentiating the absolutely convergent tail gives
   R'=-(rho'/rho+i*z)R-h. Consequently
   i*(f'+(rho'/rho)*(f-tau))-z*f=g pointwise.
5. For uniqueness subtract two solutions. Multiplication by
   rho(x)*exp(i*z*x) turns the zero-tail homogeneous equation into a
   constant. Its right limit is zero. Thus every homogeneous solution with
   tail c equals -c*flatQuotient(z). The existing whole-line boundedness
   selector forces c=0 when z!=0 and XiC(z)!=0.
6. For z=i*r, C(z) is the integral of the strictly positive density
   rho(x)*exp(-r*x), so C(z)!=0 without RH. Every nonzero imaginary shift
   is therefore admitted. The output is again continuous BV, so it can be
   supplied as a forcing to the same construction.
7. The theta quantile preserves variation. Matching traces and interior
   differentiability give the closed-interval derivative primitive and AC
   by the existing RN FTC mechanism. CHMD's unconditional BV admission then
   puts every solution in the full mass/prime/Gamma jump graph and retains
   the exact signed Weil expression.

Scope attack: no spectral-series convergence, arbitrary Hilbert-packet
realization, self-adjointness, or positivity is inferred. The forcing class
is the literal continuous BV space, not its image under a spectral map.
The conclusion is an actual inhomogeneous solution and domain preservation,
not a new RH equivalence. Existing finite-packet theorems are recovered but
do not supply this infinite-dimensional native domain theorem.

Searches used whole-corpus deep retrieval and targeted Meyer lexical/deep
retrieval. Deep reports were non-partial with no errors; compiler metadata
was predominantly source-only/stale, so applicability is checked in source
and must be audited by Lean. No old research markdown or web was used.

Formal result:
`nativeThetaImaginaryEquation_existsUnique_full_source (r : ℝˣ)
(g : ThetaContinuousBV)` constructs a unique `ThetaNativeDomain` solution of
the literal pointwise equation `(A-i*r)f=g`, together with compact absolute
continuity and the complete signed arithmetic graph representative of every
real-linear component. The equation also has a cleared native parametrix at
every complex parameter, without a spectral premise. The auxiliary regular
parameter construction is not the unconditional main statement: nonvanishing
on the imaginary axis is proved from the positive actual theta integral.

Direct audits passed, sequentially, using `lake --old env lean -o ... <leaf>`:
- `HTGeometry/BoundedVariationKernelIntegral.lean`
- `RHTower/PaperThetaForcedTail.lean`
- `RHTower/PaperThetaForcedConnection.lean`
- `RHTower/PaperThetaNativeUniqueness.lean`
- `RHTower/PaperThetaNativeResolvent.lean`
- `RHTower/PaperThetaNativeQuantileDomain.lean`
- `RHTower/PaperThetaNativeArithmeticResolvent.lean`

All 58 public theorem declarations passed a separate `/tmp` `#print axioms`
audit. Every dependency list is exactly `propext`, `Classical.choice`,
`Quot.sound`; no added axiom or admitted proof. All seven source/artifact
pairs are fresh and each leaf has exactly one theorem-area umbrella import.
No full or umbrella build, numerical experiment or heartbeat increase ran.

Global `scripts/formal_tools.py lint` exited 1 on three unrelated concurrent
umbrella omissions, preserved without importing unaudited work:
`CHMDLevySymbolLowerBound`, `CHMDWindowFourierTail`,
`WeilCutEvenMeanZeroDeficit`. Its other output was existing large-file warnings.

Assessment: this closes a native domain obstruction. The weighted tail now
acts on arbitrary continuous BV forcing and its output survives both the
singular coordinate and the complete arithmetic form domain. This is an
actual inhomogeneous solution theorem, not just a variation estimate or an
RH receiver. The integrating factor and Hilbert inverse were already known
in the corpus; they are not counted as new. Original-Frechet spectral density,
arbitrary Hilbert-packet source realization and directed prime--Gamma work
orientation remain open. No external priority claim is made. Routine word
iteration or weaker forcing-domain extensions cannot count as another
contribution without a separate structural obstacle.

Housekeeping completed: `scripts/formal_tools.py index` rewrote the three
formal inventories and refreshed the Lean search database (7 changed,
0 removed). All eight exact owned `/tmp/hgt_rh018_*` scratch files were
removed after the audits. This card moves to `3-formalized`; the ledger
counts the complete result once as contribution 018. The 100-result goal
remains active. No commit or push was made.
