# Constrained-Prolate Bessel/clock universality law

## Status

Fully proven on paper; Lean 4 formalization in progress.

## Theorem-first source

- `summable_evenProlateConstraintCoord_sq`: squared magnitudes of the true signed-Prolate
  constraint coordinates are summable at every aperture.
- `evenProlate_bessel_eventually`: their total squared mass is eventually at most `2λ`.
- `ClockEnvelope.ccm_depth_exactEigenpair_and_allRawDefects`: an arbitrary clock-enveloped CCM
  family with those two properties and finitely many coordinate limits has an eventual nonzero
  exact secular eigenpair and vanishing normalized raw defects at every earlier coordinate.

The statements use the same coordinate sequence after the literal specialization
`ℓ λ j = ‖evenProlateConstraintCoord λ j‖`. Corpus research found no theorem performing this
true-operator discharge.

## Universal law

For any clock envelope and fixed depth, the true signed-Prolate constraint magnitudes require only
their first `k+2` Hermite coordinate limits. The full infinite-dimensional summability and Bessel
hypotheses are automatic, and the clock law yields an eventual genuine depth eigenpair plus
collapse of every normalized raw contrast through depth `k`.

## Paper proof

Specialize the clock-universal theorem to the norm of the actual constraint coordinate. Apply
true-operator summability pointwise in aperture and the eventual Bessel bound. The remaining
finite coordinate-limit hypothesis is exactly the law's input. No numerical computation is used.

## Lean formalization

Module: `GaloisForLFunctions.RHTower.ConstrainedProlateBesselClockUniversalityLaw`.

## Novelty audit

Pending literature audit after exact Lean formalization. Corpus audit is negative.
