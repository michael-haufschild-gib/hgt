# CCM-FU: uniform weighted completion through small terminal heads

- Stage: 5-failed.
- Scope: a restricted terminal-completion claim, not the main fixed-weight path candidate.
- Exact [proof and positive survivor](../3-formalized/ccm-fu-weighted-terminal-head-barrier.md).

## False statement

There exist a fixed alpha>0, a fixed positive integer grid c, a head
constant C, a remaining-quotient bound J and a threshold N₀ such that
at every M=cN, N≥N₀, some terminal core with `|H|≤C sqrt(M)` and M/p≤J
admits a complete nonincreasing `V+alpha H²` prime order.

`not_exists_uniform_weighted_small_terminal_completion` refutes exactly
this statement. Cofinal fixed-grid square-root escape of the actual
complete signed source contradicts the necessary endpoint amplitude.

The actual small-head, arbitrarily small-envelope cores also exist
arbitrarily far out where they cannot complete at the chosen positive
weight: `exists_mobiusDivisorSmallTerminalCore_without_weighted_completion`.
Thus small current energy and small complete one-step envelope do not
supply this form of complete continuation.

## Strongest positive survivor

Weighted scalar descent forces the sharp invariant

`|new head|≤max(|old head|,((1+alpha)/(2alpha))|absorbed leaf|)`.

A unit leaf attains the coefficient with exact energy equality. This
law is proved for full finite paths and transported to every literal
terminal prime order. Every completable bounded-quotient terminal core
must have a head escaping every fixed square-root bound along the
cofinal source escape cutoffs. All statements have dependency-closed
paper proofs and passing scratch/leaf Lean checks in the linked card.

## Surviving main question

The [fixed-weight complete-path candidate](../1-in-progress/ccm-fu-weighted-head-dissipation.md)
from the empty processed core remains unchanged and open. A successful
path can avoid the excluded small-head terminal cores. No RH proof or
falsification is claimed.
