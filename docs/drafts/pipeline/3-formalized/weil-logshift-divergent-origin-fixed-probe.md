# Divergent origin mass and a universal fixed negative probe

Status: [FORMALIZED; GLOBAL LINT BLOCKED BY ONE UNRELATED UNWIRED MODULE]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Target and plan

Remove origin-moment summability from fixed-probe separation of arbitrary strict
minorants. For divergent origin moment, conjecture a universal fixed integer-log
probe tends to minus infinity. Combine with the proved finite-moment separator
to obtain fixed-probe separation without any coefficient-growth premise.

1. Audit the corpus's exact full-kernel upper bound and truncated-kernel support
   and plateau lemmas. No unproved log-concavity or tail-ratio premise.
2. Prove a uniform tail comparison: for c>=4, all large y and every L,
   `4 K_L(y) <= K_L(y-c)`.
3. Prove divergence of the nonnegative truncated origin sums when their limiting
   origin series is not summable, using finite partial sums and termwise limits.
4. Deduce the fixed probe tends to minus infinity; combine finite/divergent
   branches and derive unrestricted strict-minorant fixed separation.
5. Compile final leaves at default heartbeats, audit all new/changed public
   theorems, wire/index, lint, promote verified results, clean owned scratch.

## Paper argument for the tail comparison

Put B=4*pi^2-6*pi>0. The existing whole-line sandwich for Phi gives
`Phi(t)>=B exp(-pi exp(2|t|))`: the other factors in its leading term are bounded
below by 1 and B. Existing autocorrelation comparison gives, with X=exp(y),

`K(y) <= (101/100)^2 exp(-pi(X-1)) ((4*pi^2 X-6*pi)/B)^2 K(0)`

for y>=log2. Its right side is bounded by `C X^2 exp(-pi X)` with fixed C>0.

Fix c>=4, y>=c. If y>=2L then K_L(y)=0 and the comparison is immediate.
Otherwise integrate K_L(y-c) over t in [a-1,a+1], a=(y-c)/2. Both |t| and
|t-(y-c)| are at most a+1<=L-1, so both cutoff factors equal 1. The integrand
is at least `B^2 exp(-2pi exp(y-c+2))`; the interval has length 2.
Since c>=4 and exp(2)>4, this gives

`K_L(y-c) >= 2 B^2 exp(-(pi/2) exp y)`.

The ratio of the full-kernel upper bound to this lower bound is at most a
constant times `X^2 exp(-(pi/2)X)`, which tends to zero. Therefore eventually
`4 K_L(y)<=K_L(y-c)`, uniformly over L. This uses the already-proved leading
term sandwich and shift estimate, not a new log-concavity assumption.

## Paper argument for divergent origin mass

For a minorant let v=-weilDeviation(lam)>=0. If sum v(n)K(logn) diverges, the
truncated sums D_L=sum v(n)K_L(logn) tend to +infinity. To see this without
assuming monotonic cutoffs, choose a finite partial sum larger than any given
bound, use termwise convergence on that finite set, and retain nonnegativity
of every other truncated term.

Choose m0=floor(exp4)+1, so c=logm0>=4 by the existing integer-log probe bound.
For logn beyond the tail-comparison threshold, the real paired probe kernel is
`4K_L(logn)-2K_L(logn+c)-2K_L(logn-c) <= -4K_L(logn)`.
The finitely many head terms have a common upper bound using K_L<=K. The
unconditional probe identity then bounds this probe above by a bounded head,
the vanishing zero-side term, and minus four times the divergent truncated
tail mass. Hence it tends to -infinity. A late cutoff also includes m0 in the
expanding panels.

Every strict minorant therefore has a persistent fixed negative probe: use
the previously verified finite-origin theorem in the summable branch, and
this universal probe in the divergent branch. No coefficient nonnegativity,
sampled convergence, or uniform-panel positivity premise remains.

## Evidence and boundaries

Inspected `riemannKernelReal_sandwich`, `riemannAutocorr_two_mul_le`, and
`riemannShiftRatio` in `WeilFullConeMinorantRigidity.lean`. Exact local query
for riemannKernelReal/log/concave returned zero; broader Lean source search
located theta-source log-concavity results, but the proof above does not need
to import or bridge them. The cutoff plateau, integral comparison, and limit
APIs were checked against this toolchain.

The complete chain is Lean verified and all seven axiom audits passed. Global
lint reports only the unrelated umbrella-reachability error listed below.
No external novelty, RH, or general mixed-sign rigidity claim. No numerical
experiments, new axioms, heartbeat increases, or full builds.

## Sharper corpus ingredient found during audit

`WeilWorkExposingRayTailAsymptotic.lean` already proves
`ExposingRayTail.autocorr_upper`: for 0<c<pi, K(y)<=C exp(-2c exp|y|).
Use c=pi/2 to remove the polynomial prefactor from the earlier paper bound.
Its existing `phi_lower` gives `Phi(t)>=2pi^2 exp(-pi exp(2|t|))`; expose this
lemma publicly and reuse its proof. The central-interval lower bound therefore
has constant `D=2(2pi^2)^2`, and the ratio comparison reduces directly to
`exp(-(pi/2)exp y)->0`. The same argument permits any prescribed gain A, not
just four, uniformly in the cutoff L. Exact cutoff plateau and measure-theory
APIs were checked in a scratch Lean file; its compile passed.

## Verification checkpoint

`WeilWorkExposingRayTailAsymptotic.lean` recompiled with `phi_lower` public;
proof body unchanged. New `WeilLogShiftTailComparison.lean` compiled and exported
at default heartbeats. Both the central-interval lower bound and arbitrary-gain,
cutoff-uniform inward-shift comparison are now Lean verified.

`WeilLogShiftDivergentMinorant.lean` also compiled and exported without warnings
at default heartbeats. Four public theorems establish unconditional truncated
origin summability, divergence of nonnegative truncated origin mass, the
minus-infinity probe limit for every fixed integer m with log(m)>=4, and the
unrestricted strict-minorant fixed separator. The final theorem assumes only
lam(n)<=vonMangoldt(n) for n>=2 and one strict deficit. Its fixed witness has
a positive margin and belongs to every sufficiently late expanding panel.

All new modules are wired in `RHTower.lean`. Seven public-theorem axiom audits
(including the exposed existing lower envelope) report only `propext`,
`Classical.choice`, and `Quot.sound`. The audit also checks the finite-sum and
order-limit APIs against this toolchain. Index refresh passed; all seven API
rows are present. Scoped whitespace checks passed.

Final `scripts/formal_tools.py lint` exited 1 with this unrelated module
unreachable from its theorem-area umbrella:

- `GaloisForLFunctions.RHTower.PaperCirclePosteriorMask`

No lint errors concern this result. Unrelated sources/imports were not
modified. No full or umbrella build was run. All three final leaf sources were
compiled with `lake --old env lean <leaf> -o <local olean>` at default heartbeats.

## Exact advance and remaining frontier

The finite-origin assumption in the previous fixed-minorant result is removed.
In the divergent case the witness can be chosen independently of the minorant:
`m0=floor(exp(4))+1`; indeed every fixed integer with log(m)>=4 works and its
probe tends to minus infinity. In the finite case the witness may depend on
the deficit distribution. The cutoff threshold and negative margin are not
claimed uniform over all minorants.

A possible next step is to extend the divergent-mass argument to signed
deviations with summable positive excess, whose contribution has a uniform
kernel bound. This is a new conjecture/application requiring a separate paper
and corpus audit; no general mixed-sign rigidity result is claimed here.
