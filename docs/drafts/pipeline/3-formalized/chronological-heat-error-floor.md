# Bounded chronological heat repair: universal error floor

**Status:** both Lean leaves pass their individual final builds. All 15 public
declarations pass the axiom audit with only propext, Classical.choice, and
Quot.sound; five private helpers are covered transitively. No computation,
numerical zero, RH assumption, full build, or umbrella build enters the proof.
The original bounded-array convergence target remains open.

## Exact result

Put h(t)=1/t−1/(e^t−1),
r_(N,a)(t)=e^(−t)+Σ_(1≤k≤N)a_k h(kt), and E_(N,a)=||r_(N,a)||₂.

There exists one constant G>0 such that, for every C≥0, every N, and every
real coefficient vector with |a_k|≤C,

E_(N,a) ≥ G / [4 sqrt(log(1+8(1+CN)/G))].

More precisely, the inequality holds with G=|Γ(ρ)| for **each** critical-line
zeta zero ρ. A closed Hardy theorem supplies such a zero, making the existential
statement unconditional. Every finite residual is proved to belong to the actual
L²(0,∞) space, with the norm equal to the square root of its squared integral.

**Positive cost theorem.** For η>0, E_(N,a)≤η implies

G [exp((G/(4η))²)−1] ≤ 8(1+CN).

For fixed C>0 this is an exponential lower bound on the arithmetic cutoff in
inverse squared accuracy. In particular, a requested error 2^(−m) forces a
cutoff at least of order exp(c·4^m). Fast nonlinear response recovery therefore
requires an enormous arithmetic cutoff if it is to be realized with bounded
linear coefficients. The inequality supplies no such realization.

## Dependency-closed paper proof

For t>0, 0≤h(t)≤min(1,1/t), and e^(−t)≤min(1,1/t).
Hence |r_(N,a)(t)|≤A and |r_(N,a)(t)|≤A/t, where A=1+CN.

The convergent Mellin transform of h on 0<Re(s)<1 is −Γ(s)ζ(s).
Finite linearity and dilation therefore give
M[r_(N,a)](ρ)=Γ(ρ) at every zeta zero in this strip, independently of a.
At Re(ρ)=1/2 the modulus of the Mellin weight is t^(−1/2).

Split its integral at K^(−2) and K², K>1. The two tail bounds each contribute
at most 2A/K. Cauchy–Schwarz bounds the middle by
E_(N,a) sqrt(∫_(K^(−2))^(K²) dt/t)=2E_(N,a)sqrt(log K).
Thus G≤4A/K+2E_(N,a)sqrt(log K).

Set K=1+8A/G. Since A,G>0, K>1 and 4A/K≤G/2. Rearrangement gives the
floor. If E_(N,a)≤η, positivity permits squaring and exponentiating, giving
the cost theorem. Gamma has no zero at ρ. Critical-zero existence is supplied
by `exists_riemannZeta_line_zero_dyadic`, whose axiom audit contains only
propext, Classical.choice, and Quot.sound.

## What this decides

For a fixed coefficient bound, the explicit floor has order 1/sqrt(log N).
It excludes persistent power-rate decay in N. Lean additionally proves that
no bounded array can have E_N sqrt(log(1+8(1+CN)/G))→0.

This does **not** exclude E_N→0, assert raw Möbius nonconvergence, or establish
RH. The excellent finite fits remain valid numerical evidence; they cannot
justify extrapolating their apparent fast rate. The remaining hard task is
an actual coefficient construction with a uniform budget and full L² decay.

Zeta-zero lower bounds in Nyman–Beurling approximation are classical; see
[Burnol](https://arxiv.org/abs/math/0103058). The exponential kernel's
coefficient-controlled RH interface is also classical; see
[Darses–Hillion](https://cml.centre-mersenne.org/item/10.5802/cml.71.pdf).
This result audits the explicit bounded heat family. No novelty claim is made.

## Lean map and audit

Namespace `RHTower`, directory `formal/GaloisForLFunctions/RHTower/`:

| Leaf | Main statements |
|---|---|
| ChronologicalHeatMellin | chronologicalHeatError_bounds; chronologicalHeatError_mellin_at_zero |
| ChronologicalHeatErrorFloor | chronologicalHeatError_exists_universal_floor; chronologicalHeatError_not_log_weighted_zero; chronologicalHeatError_exponential_budget |

Both imports are wired into `GaloisForLFunctions/RHTower.lean`.
The base leaf passed `lake build GaloisForLFunctions.RHTower.ChronologicalHeatMellin`.
The floor leaf passed `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ChronologicalHeatErrorFloor`.
The initial floor build was stopped after it spawned parallel dependency
compilers; all owned processes were cleaned up before the serial audit.
An early axiom audit exited on the then-missing leaf output and was rerun only
after the successful build. Authoritative formal lint passes with existing
file-size warnings.

Audit artifacts: `/tmp/chronological_heat_floor_manifest.json`,
`/tmp/chronological_heat_floor_axioms.txt`,
`/tmp/chronological_heat_floor_axiom_summary.json`,
`/tmp/chronological_heat_floor_build.txt`,
`/tmp/chronological_heat_floor_lint.txt`.

[Compact research notes](../1-in-progress/chronological-bounded-repair-attack.md).
