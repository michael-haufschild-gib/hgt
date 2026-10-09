# The potential domain is exactly subexponential coefficient growth

Status: [FORMALIZED; GLOBAL LINT HAS FOUR UNRELATED UMBRELLA ERRORS]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Target and plan

Identify whole-line paired-kernel potential convergence for arbitrary signed
weights with elementary coefficient growth. Reframe the exact cofinal-probe
convergence guard as subexponential growth and obtain the corresponding
finite-excess positivity receiver.

1. Audit actual full-kernel upper/lower envelopes and summation APIs.
2. Convert kernel envelopes at log n into exponential damping upper and lower
   comparisons, ignoring finitely many initial n where needed.
3. Prove whole-line potential convergence iff every exponential damping is
   summable, iff subexponential pointwise growth.
4. Connect growth to cofinal actual-probe lower bounds and the potential
   inequalities. Retain finite excess only in these Weil-probe applications.
5. Compile/export, audit all public theorems, wire/index/lint, update the failed
   convergence-free route's positive survivor, promote, save memory, clean scratch.

## Dependency-closed paper argument

Write P_y(n)=K(y+log n)+K(y-log n). Existing autocorrelation envelopes give
K(z)<=C exp(-pi exp|z|) (choose c=pi/2 in autocorr_upper) and, eventually for
positive z, K(z)>=D exp(-4pi exp z) (choose b=4pi in autocorr_lower).
Both envelopes are already proved for the literal kernel.

For n>=1, exp|y+log n| and exp|y-log n| are at least n exp(-|y|).
Consequently P_y(n)<=2C exp(-epsilon_y*n), epsilon_y=pi exp(-|y|)>0.
Thus summability of |v(n)|exp(-epsilon*n) for every epsilon>0 implies
summability of v(n)P_y(n) for every real y, by norm comparison.

Conversely, fix epsilon>0 and choose y=-log(epsilon/(4pi)). Then
4pi exp(-y)=epsilon. For all sufficiently large n, log n-y is in the lower
envelope's tail, giving D exp(-epsilon*n)<=K(log n-y)<=P_y(n).
Norm summability of the potential at y implies summability of the damped
absolute coefficients. Finite heads cause no restriction. Hence the domain
equivalence holds for every signed sequence v, without finite excess.

If every damping is summable, S_epsilon=sum |v(n)|exp(-epsilon*n) is finite
and nonnegative. Retaining one term and multiplying by exp(epsilon*n) gives
|v(n)|<=S_epsilon exp(epsilon*n). Conversely, a bound at epsilon/2 leaves the
summable geometric envelope C exp(-epsilon*n/2) after damping at epsilon.
This proves equivalence with forall epsilon>0 exists C>=0 forall n,
|v(n)|<=C exp(epsilon*n).

Apply the arbitrary-weight result to weilDeviation(lam). With finite excess,
the already-proved cofinal-probe lower-bound characterization identifies those
lower bounds exactly with subexponential growth. Asymptotic positivity is then
equivalent to subexponential normalized-deviation growth plus all integer-log
potential inequalities. Positivity supplies growth; growth supplies the entire
potential domain. No new unproved analytic premise is introduced.

## Corpus audit and limits

Cached lexical search: 655 declarations, 241 modules, 366 eligible entries.
Read the actual ExposingRayTail.autocorr_upper/autocorr_lower statements and
proofs. Existing square-root subexponential summability concerns a different
weight and does not supply this n-scale domain classification. The cofinal
domain and guarded positivity theorems are already verified leaves.

No RH or general mixed-sign rigidity conclusion. Finite excess remains in
the probe and positivity applications, but not in the arbitrary-weight domain
classification. No external novelty claim, numerical experiments, added axioms,
heartbeat increases, full builds, or umbrella builds.

## Verification checkpoint

`WeilLogShiftSubexponentialDomain.lean` compiled/exported at default heartbeats
without diagnostics. All seven public theorems are proved: exponential upper
and lower comparisons, potential/damping equivalence, damping/growth
equivalence, exact potential/growth classification, growth/cofinal-probe
equivalence with finite excess, and the growth-based positivity receiver.
The scratch API check passed. The leaf is wired in `RHTower.lean`.
All seven public theorem axiom audits passed with only `propext`,
`Classical.choice`, and `Quot.sound`. `scripts/formal_tools.py index` passed;
all seven API rows were checked. Scoped whitespace checks passed.

The final leaf audit used `lake --old env lean` with the source path and local
`-o` output, at default heartbeats. The scratch axiom audit imported that final
exported leaf. No full or umbrella build was run.

Global lint exited 1 solely for these unrelated modules unreachable from their
theorem-area umbrellas:

- `GaloisForLFunctions.RHTower.PaperCircleCalibrationPrediction`
- `GaloisForLFunctions.RHTower.PaperCirclePosteriorCalibration`
- `GaloisForLFunctions.RHTower.RiemannKernelTailDecayRate`
- `GaloisForLFunctions.HTGeometry.ApertureStableKTheory`

No reported lint error concerns this leaf. Unrelated sources/imports were not
modified. The failed convergence-free route card now records this exact
growth-based positive survivor and its dependency-closed paper/Lean status.

## Exact advance

For arbitrary signed weights, the largest domain on which all real-shift
potentials are summable is precisely the subexponential growth class. This
classification needs no coefficient sign or finite-excess premise. It replaces
an analytic family of convergence requirements by the elementary bounds
`forall epsilon>0, exists C>=0, forall n, |v(n)|<=C exp(epsilon*n)`.

For normalized Weil deviations with finite excess, this class is exactly the
one detected by lower bounds on any cofinal family of actual probes. Uniform
asymptotic positivity is equivalent to this growth condition plus all
integer-log potential inequalities. The unrestricted totalized-sum no-go remains
valid outside the recovered domain.

## Follow-up results

`WeilLogShiftLocalDecayThreshold.lean` formalized the local rate
`2*pi*exp(-|y|)`, hence `2*pi/m` at log m, and both strict sides of its growth
classification. `WeilLogShiftCriticalEndpoint.lean` subsequently proved
divergence at equality for pure exponential weights, closing their exact iff.
See the corresponding local-threshold and critical-endpoint proof cards.

`RiemannKernelTailDecayRate` was audited in the local-threshold increment;
its bounds concern Phi rather than the paired autocorrelation.
