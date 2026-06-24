# Gamma C-Point RVM-Scale Control

- **ID:** gamma-cpoint-rvm-scale-control
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** Professor computation and gamma-zeta native-route refutation, 2026-06-23
- **Statement:** The full Gamma differential field `C(s)<Gamma>` contains functions with unbounded-height poles of Riemann-von-Mangoldt leading density, so pole-height and leading pole-density cannot separate zeta from the Gamma field.

## Goal

Kill a false native route in `gamma-zeta-differential-independence.md` and add a control object for future zeta-divisor invariants. If an invariant only detects unbounded height or `T log T` leading density, it may be seeing the archimedean Gamma phase rather than zeta's prime arithmetic.

## Gates

- [ ] 0 -> 1 in-progress: turn the Stirling/Lambert-W branch argument into a complete paper proof and run source search for inverse-Gamma/c-point asymptotics
- [ ] 1 -> 2 fully-proven: prove existence of `Gamma(s)=1` solutions `s_k` with `Im(s_k) ~ 2*pi*k/log k` and derive the counting consequence
- [ ] 2 -> 3 formalized: unlikely; would require complex asymptotics infrastructure absent from Lean
- [ ] 3 -> 4 publication-ready: only if the source gate finds a genuinely new project-level control statement

## Approach

[CONJECTURE / proof sketch] On the principal logarithm branch in the first quadrant, Stirling gives

`log Gamma(s) = (s-1/2)Log s - s + (1/2)log(2*pi) + O(1/s)`.

For large positive integers `k`, solve the leading equation

`s(Log s - 1) = 2*pi*i*k`.

With `w = Log s - 1`, this becomes `w e^w = 2*pi*i*k/e`, giving

`s_k^0 = 2*pi*i*k / W(2*pi*i*k/e)`.

The approximants satisfy `Im(s_k^0) ~ 2*pi*k/log k -> infinity`. Since the phase derivative is `Log s + O(1/s)`, a Rouché/Newton-Kantorovich argument should give true solutions of `log Gamma(s) = 2*pi*i*k`, hence `Gamma(s)=1`, near these approximants for all sufficiently large `k`.

Therefore `f(s)=1/(Gamma(s)-1) ∈ C(s)<Gamma>` has unbounded-height poles. Moreover the branch count satisfies

`N_f(T) ~ (T/(2*pi)) log T`

up to lower-order `log log T` corrections, the same leading scale as Riemann-von-Mangoldt.

## Computation

Archived in:

- `computations/2026-06-23-gamma-cpoints-unbounded-height.py`
- `computations/2026-06-23-gamma-cpoints-unbounded-height.txt`

Sample roots:

- `k=50`: `29.068503603921728829 + 80.836387880226486924 i`, `|Gamma(s)-1| ~ 3.3e-79`
- `k=100`: `45.336359590189951313 + 142.624809956592716 i`, `|Gamma(s)-1| ~ 7.5e-79`
- `k=500`: `137.79387391572387708 + 553.53753295347030626 i`, `|Gamma(s)-1| ~ 1.5e-78`

## Consequence

The following proposed separators over `K=C(s)<Gamma>` are refuted as stated:

1. every `K`-element has poles in a bounded horizontal strip;
2. no `K`-element has log-enhanced `T log T` pole density.

Any surviving native proof of `Gamma ⟂ zeta` over `K` must distinguish the origin, phase, or arithmetic law of poles, not height or leading density alone. Gamma c-points provide an archimedean `T log T` control lattice; zeta zeros add the functional-equation/prime fluctuation law.

## Theatre Test

Novelty risk is high. Inverse-Gamma and Stirling-inversion branch asymptotics are likely known. The candidate should not be promoted as a globally novel theorem unless source search finds that the project-level control statement is new and significant.

## Log

- 2026-06-23 - created after refuting the pole-confinement lemma in `gamma-zeta-differential-independence.md`. Status is CANDIDATE / source-risk high.

## RunPod Verification

- 2026-06-23 - copied the computation to the shared RunPod at `root@157.157.221.30:/root/hgt-shared/computations/2026-06-23-gamma-cpoints-unbounded-height.py` and reran it with `/usr/bin/python3.13` after installing `mpmath` for that interpreter. Output saved at `/root/hgt-shared/computations/2026-06-23-gamma-cpoints-unbounded-height-runpod.txt`. The RunPod output matches the local output.

## Source Check

- 2026-06-23 - web search for exact phrases `Gamma(s)=1 Lambert W`, `log Gamma(s) 2 pi i k Lambert W`, `a-points of the Gamma function T log T`, and `Gamma function a-points Nevanlinna` did not surface an exact matching statement in the first-pass results.
- Nearby literature is substantial and keeps novelty high-risk: Jeffrey-Watt, *The Inverse of the Complex Gamma Function* (arXiv:2311.16583 / SYNASC 2023) studies complex inverse-Gamma branch structure, and Folitse-Jeffrey-Corless, *Properties and Computation of the Functional Inverse of Gamma* (SYNASC 2017), uses Stirling/Lambert-W inverse-Gamma approximations. See `https://arxiv.org/abs/2311.16583` and `https://ieeexplore.ieee.org/document/8531266/`.
- Current theatre status: no promotion. The exact project-level control may still be useful, but the global mathematics is likely adjacent to known inverse-Gamma asymptotics.

## Replacement Target After The Kill

The Gamma c-point branch kills leading-density arguments, but it also clarifies the only plausible remaining separator.

For zeta zeros,

`N_zeta(T) = theta(T)/pi + 1 + S(T)`,

where `theta` is the archimedean Gamma phase and `S(T)` is the residual prime/arithmetic fluctuation. For the Gamma c-point branch, the count should be governed by inverse-Stirling asymptotics, with residual terms built from smooth `log log T / log T` corrections rather than prime-explicit oscillation.

[CONJECTURE / repair target] A native separator for `Gamma ⟂ zeta` over `C(s)<Gamma>` must live in the residual law after all archimedean inverse-Gamma controls are allowed: the zeta divisor carries the prime-explicit fluctuation `S(T)`, while finite Gamma-field c-point constructions supply archimedean inverse-Stirling residuals. Height and leading `T log T` density are too coarse.

Theatre risk: this may reduce to explicit-formula folklore. It is recorded only as the next attack target after the pole-height and leading-density invariants were killed.
