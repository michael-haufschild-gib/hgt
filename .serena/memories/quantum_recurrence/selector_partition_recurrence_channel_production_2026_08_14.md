# Selector partition and recurrence-or-channel-production frontier (2026-08-14)

## False frontier retired

Scalar centralizer recurrence energy cannot close Brown onset. One sample has exact energy ||z||², and fresh self-target channels saturate the observer–spectral inequality without orthogonality or spectral assumptions. Diagonal subtraction leaves a signed kernel and loses perfect fresh-target shortcuts.

Failed-route card:
- docs/drafts/pipeline/5-failed/scalar-centralizer-recurrence-energy-as-brown-onset-provider.md

## Formal survivor 1: selector partition

Module:
- formal/GaloisForLFunctions/HTGeometry/StaticShortcutSelectorPartitionLaw.lean

Core exact results:
- selectorMargins_sq_load_le_recurrenceEnergy
- selectorRecurrenceEnergy_eq_pairSum
- selectorRecurrenceEnergy_flow_injective
- selectorIdentity_selfTarget_saturation
- adaptive_selected_shortcuts_force_channel_recurrence

Interpretation: recurrence energy measures reuse inside the same selected observer channel; fresh channels carry unavoidable diagonal production cost.

## Formal survivor 2: recurrence-or-channel-production law

Module:
- formal/GaloisForLFunctions/HTGeometry/StaticShortcutRecurrenceChannelProductionLaw.lean

Let W be total shortcut mass, Mσ occupied-channel count, Rσ same-channel recurrence energy, eta alignment margin, B target-memory norm ceiling. Proven universally:

eta² W² <= B Mσ Rσ.

Capacity form and strict contrapositive:
- Mσ <= K -> eta² W² <= B K Rσ
- B K Rσ < eta² W² -> Mσ > K

Separation safeguard:
- ObserverChannelsSeparated q δ with δ>=0 implies q injective.
- separated strict contrapositive returns both injectivity and Mσ>K, preventing duplicate-label inflation.

Static two-memory capstone writes Rσ as exact same-target stationary kernel after completed-sector removal.

## Paper cards

- docs/drafts/pipeline/2-fully-proven/selector-partition-observer-channel-recurrence-law.md
- docs/drafts/pipeline/3-formalized/selector-partition-observer-channel-recurrence-law.md
- docs/drafts/pipeline/2-fully-proven/observer-channel-recurrence-production-dichotomy-law.md
- docs/drafts/pipeline/3-formalized/observer-channel-recurrence-production-dichotomy-law.md

Master paper hostile/corpus audits updated. Paper remains below Nature threshold.

## Verification

Both modules pass direct `lake env lean <file>`.
Module-only builds pass:
- lake build GaloisForLFunctions.HTGeometry.StaticShortcutSelectorPartitionLaw
- lake build GaloisForLFunctions.HTGeometry.StaticShortcutRecurrenceChannelProductionLaw

Axiom audits report only propext, Classical.choice, Quot.sound. No sorry/admit/project axiom/opaque/unsafe. Both wired in HTGeometry umbrella. Scratch files cleaned and no stale Lean processes.

Global non-build lint failed only because unrelated concurrent module GaloisForLFunctions.RHTower.SuzukiScrewNaturalDomainEquality was unreachable from RHTower umbrella.

## Exact open Brown core

For canonical resolution-separated channels and one ordinary one-draw time-independent local-Hamiltonian ensemble, prove on one quenched event, uniformly over every shallow selector with channel capacity K(s):

B K(s) Rσ < eta² W²

through the onset window. This is selector-resolved cross-incidence anti-concentration, not scalar source dephasing. Full Brown law still needs plateau measure, first low-complexity recurrence scale, and permanent non-Haar locality on the same event. Novelty of classical inequality composition is unverified.