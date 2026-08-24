# Bounded generated enhanced Verdier quotient

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Bounded categorical form of enhanced ind-sheaf infrastructure.

## Target

Construct the bounded Verdier quotient by the thick triangulated envelope of bounded derived
enhanced-projection pullbacks, without assuming unproved fullness.

## Dependency-closed paper proof

Bounded enhanced-projection pullback is triangulated. Its essential image is nonempty because it
contains the pullback of zero. Take the thick triangulated envelope of this image. Localizing the
bounded target derived category at morphisms whose cones lie in that envelope produces a
triangulated Verdier quotient. Every bounded object pulled back from the base lies in the envelope,
so its image in the quotient is zero. The localization universal property gives descent and the
canonical factorization for every functor which inverts this Verdier class.

## Exact standard-identification gap

Replacing the generated envelope by the bare essential image still requires fullness of bounded
derived projection pullback. This remains downstream of cohomological contractibility of `EReal`.

## Lean status

`StokesBoundedGeneratedEnhancedVerdier` formalizes bounded projection image, generated negligible
subcategory, Verdier localization, triangulatedness, annihilation of bounded base-pulled objects,
descent, and factorization. Direct Lean check and targeted module build passed. All declarations
use only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-24 — paper proof closed; Lean formalization started
- 2026-08-24 — bounded generated quotient formalized and axiom-audited
