# Local ring at a prime divisor is a DVR — proved (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(stage 2).

## New module (9th in this card's lineage)

`GaloisForLFunctions/HTGeometry/LocalizationAtPrimeDivisorDVR.lean`

| statement | declaration |
|---|---|
| Krull dimension of the local ring is one | `ringKrullDim_localizationAtPrime` |
| it is not a field | `not_isField_localizationAtPrime` |
| every nonzero prime of it is maximal | `dimensionLEOne_localizationAtPrime` |
| **localisation at a height-one prime is a DVR** | `isDiscreteValuationRing_localizationAtPrime` |

Hypotheses: `B` Noetherian integrally closed domain, `P` prime with `P.height = 1`.
**mathlib only has this for Dedekind domains** (`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`),
where height one is automatic.  The version over a base of arbitrary dimension — what a variety of
dimension `r` needs — is new here.  All axiom-clean; umbrella green (14919 jobs); lint clean.

## Route

`ringKrullDim (Localization.AtPrime P) = P.height` via
`IsLocalization.AtPrime.ringKrullDim_eq_height`; not-a-field because a field would force
`maximalIdeal = ⊥` hence dimension `0 ≠ 1`; `Ring.DimensionLEOne` because a nonzero prime `Q < m`
would give `height Q < 1` (again via `Ideal.height_le_iff`, avoiding ℕ∞ arithmetic) hence `Q = ⊥`;
then `IsDedekindRing = Noetherian + DimensionLEOne + IsIntegrallyClosed`, and
`IsDiscreteValuationRing.TFAE` entry 2 → 0.

## Lean traps

- `isIntegrallyClosed_of_isLocalization` needs the **target ring as an explicit first argument**:
  `isIntegrallyClosed_of_isLocalization _ P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P)`.
- `IsNoetherianRing (Localization S)` is an instance but lives in
  `Mathlib/RingTheory/Localization/Submodule.lean` — **import it or the instance is invisible**
  and you get `IsNoetherian (Localization.AtPrime P) (Localization.AtPrime P)` failures.
- `List.TFAE.out i j` leaves the two propositions as metavariables, so
  `(htfae.out 2 0).mp inferInstance` fails with "type class instance expected ?m".  **Pin the type
  with a `have hiff : A ↔ B := htfae.out 2 0` first**, then `hiff.mp inferInstance`.
  `inferInstanceAs` does not help.
- `omit ... in` must come **before** the docstring, not between docstring and `theorem`.

## Card status

Lineage is now 9 modules.  Everything from the eigenvolume identity (7) through the local law
(8)/(9), the abstract system and all its hypotheses, and now the DVRs at prime divisors, is
formal.  Remaining: assemble the capstone (blocked on the self-map `Algebra B B` instance clash —
see `research/prime_divisor_height_both_directions_2026_08_06`), and the scheme-level passage
(rational top form = coframe top wedge; `AlgebraicGeometry.ord` pullback; `AlgebraicCycle` stub).
