# Height reflection requires conductor normalization

- **ID:** euler-fe-height-reflection-normalization.
- **Stage:** 3-formalized.
- **Type:** THEOREM.
- **Source:** Euler–FE transport theory, §2.10; whole-quadrant Vitali receivers.
- **Statement:** Construct the actual normalized reflected-height law. Every connected
  open domain in the upper half-plane meeting `Re s>1` and supporting locally
  bounded escaping ζ-translates must lie in `Re s>½`.

## Exact objects

Write `χ(s)=Γℝ(1−s)/Γℝ(s)`, `R(s)=1−conj(s)` and, for `t>0`,

    N_t(s)=exp((s−½)log(t/(2π)))/χ(½+it),
    F_t(s)=N_t(s)ζ(s+it),
    J_t(s)=conj(ζ(R(s)+it)).

The exact functional equation gives `F_t−J_t=(N_t χ(s+it)−1)J_t`.
For `D≥0`, the Gamma ratio theorem bounds its first factor by `C_D/t` when
`0<Re s<1`, `|s−½|≤D`, and `t` exceeds an explicit threshold depending on `D`.
The existing convexity bound with parameter `η=½` gives
`|J_t(s)|≤C t^(3/4)` uniformly on the same set. Hence

    sup |F_t−J_t| ≤ C_D' t^(−1/4) → 0.

This is an unconditional law on the actual ζ-function, with no return,
boundedness or zero-location premise. It retains the archimedean conductor drift.

## Whole-quadrant obstruction

Let `τ_j→∞`. Suppose `ζ(s+iτ_j)` were locally bounded on
`U={Re s>0, Im s>0}`. After deleting a finite initial segment, every translate
is holomorphic on `U`. For `½<Re s<1`, its reflected value is bounded at
`R(s)∈U`, whereas `χ(s+iτ_j)→0`. The exact functional equation therefore
forces `ζ(s+iτ_j)→0` on this open substrip. Vitali convergence and analytic
uniqueness propagate the zero limit through `U`. On `Re s=2`, the uniform
Euler inverse bound prevents convergence to zero. Contradiction.

Thus the whole-quadrant local-boundedness premise in
`ArithmeticAuxiliaryDynamics/ReturnsAreReturnsOfThePrimes.lean` cannot hold
for an escaping sequence, independently of any return premise.

More generally, a connected open upper-half-plane domain meeting `Re s>1` and
also `Re s≤½` contains a disc centred on the critical line. Its reflected pairs
force a zero limit on the right half of that disc. Vitali propagates zero through
the domain. At its Euler-half-plane point, the uniform positive lower bound
contradicts that limit. Thus every such boundedness domain lies strictly right
of the line.
The corpus's `IsPhaseReturn.re_gt_half_of_translatesBoundedOn` establishes this
boundary for phase returns; the present argument removes phase alignment entirely.

## No-go closure

- **Failed route:** ordinary ζ-recurrence propagated through a boundedness
  domain crossing the critical line and meeting the Euler half-plane.
- **Positive survivor:** the explicitly normalized reflected-height law above,
  uniformly on every bounded part of the open critical strip.
- **Limit:** this transports the reflected profile at the same height. It does
  not produce a new zero height, same-depth replication, `LinAt C`, or AAL.
- **Status:** paper proof and Lean formalization complete for both laws.

## Lean declarations

Namespace `GaloisForLFunctions.EulerFETransportTheory`.

- `TheNormalizedHeightReflection.lean`: `zeta_height_reflection`,
  `heightReflectionDefect_eq`, `exists_heightReflectionDefect_bound`,
  `tendstoUniformlyOn_heightReflectionDefect`.
- `TheWholeQuadrantCannotSupportReturns.lean`:
  `re_gt_half_of_translatesBoundedOn`,
  `not_translatesLocallyBounded_of_tendsto_atTop`.

Both modules pass direct `lake --old env lean` checks. Terminal transitive audits
use only `propext`, `Classical.choice`, and `Quot.sound`.
The retired cross-line recurrence route and its positive survivor are recorded
in `../5-failed/euler-fe-cross-line-normality.md`.
