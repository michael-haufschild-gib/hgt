# Permanent positive odd-prime entry sign

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Rejected claim:** an individual prime-power contribution that raises the odd exponential-pole Weil energy after entry continues to do so as aperture grows.
- **Scope:** this local sign-propagation shortcut only. The RH pole criterion and constrained-ground route remain open.

## Exact obstruction

At half-log shift `h=log(n)/2`, the actual odd prime-operator energy is

`8 exp(-h)[sinh(a-h)-(a-h)cosh(h)]`.

The full Weil contribution is its negative times `Lambda(n)`. For every genuine prime power, that contribution is positive at `a=log(n)` and negative at `b=3log(n)/2>a`. The theorem `ccmOddPole_primePower_contribution_changes_sign` uses the actual transport operator and positive Mangoldt weight. A permanent sign cannot be inferred from entry behavior.

## Strongest positive survivor

There is a unique half-log cutoff `H(a)∈(a/3,a/2)` at each aperture, solving `sinh(a-H)=(a-H)cosh(H)`. The actual Weil prime terms are losses below this cutoff, gains above it before entry, and zero at cutoff and entry. All visible prime powers therefore admit an exact partition into nonnegative old losses `O` and recent gains `R`.

The complete source identity is `Q(p_+-p_-)=G_odd+R-O`, retaining the exact Gamma–pole balance and negative odd pole square. The new comparison target is `O≤G_odd+R`. Separate positivity of the two budgets does not prove it.

A full-source replacement is also formal above radius two: within an unchanged integer cutoff, nonnegative actual odd energies at both endpoints force strict positivity throughout the interior. The proof uses the exact Gamma/prime chamber equations and `E_ch''-E_ch<0`; it does not propagate the sign of any individual prime term. The changed-cutoff boundary is included by exact cancellation of the entering atom. Odd nonnegativity on any tail starting at radius at least two is exactly its starting inequality and all later genuine prime-power entry inequalities; negative tail witnesses localize to that set. The full-source minimum principle crosses arbitrary gaps between prime powers, eliminating zero-Mangoldt checkpoints. Exact entry corrections have positive odd slope `4Lambda(n)(1-exp(-b))²` and negative even slope `-4Lambda(n)(1+exp(-b))²`; the old odd atom can still reverse its sign later. These actual checkpoint signs remain open. [Differential law](../3-formalized/weil-pole-prime-chamber-comparison.md); [boundary handoff](../3-formalized/weil-pole-prime-entry-comparison.md); [stronger prime-power survivor and parity slopes](../3-formalized/weil-pole-prime-power-gaps.md).

The complete post-entry correction is now also evaluated: it is the signed initial tangent minus the common positive loss `8Lambda(n)exp(-b)(sinh(t)-t)` in both parities. Summing yields exact full-source entry/loss balances. Omitting the loss strictly overestimates both energies after the first prime enters. The actual late-gap shapes are also proved: odd strict concavity, even strict convexity, and one unique actual even minimum per closed gap. These facts strengthen the source comparison but prove no actual checkpoint or minimum sign. [Common loss, exact balance and gap-minimum survivor](../3-formalized/weil-pole-entry-age-balance.md).

## Paper and Lean closure

The strict monotonicity of `sinh(u)/u`, the strict endpoint inequalities, and the intermediate value theorem give the unique cutoff and its complete signs. Reflection and self-adjointness connect that kernel to the actual transport operator. Exact finite-sum partitioning and the admitted full pole matrix give the source identity. Every dependency in this positive survivor is closed.

The cutoff and budget statements are formal in `CCMRestrictedWeilOddPrimeCutoff`, `CCMRestrictedWeilOddPrimeTransport`, and `CCMRestrictedWeilOddPrimeBudget`. Key theorems: `ccmOddPolePrimeKernel_eq_zero_iff`, `ccmOddPolePrimeWeight_sign`, `ccmWeilOddPole_eq_prime_budgets`, `ccmWeilOddPole_nonneg_iff_prime_budget`. Named leaf builds and all 26 public axiom audits passed. [Full proof and verification](../3-formalized/weil-odd-prime-cutoff.md).
