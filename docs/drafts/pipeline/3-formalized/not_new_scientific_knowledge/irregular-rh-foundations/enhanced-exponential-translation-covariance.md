# Enhanced exponential translation covariance

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Foundational functoriality for enhanced exponential objects.

## Target

Prove that inverse image by compactified enhanced translation through `c` sends the exponential
object of a continuous phase `φ` to the exponential object of `φ - c`, at ordinary-sheaf,
compact-support, ind-sheaf, derived, bounded-derived, and generated enhanced-quotient levels.

## Dependency-closed paper proof

Translation through `c` pulls the closed epigraph of `φ` back to the closed epigraph of `φ - c`.
Direct image along a homeomorphism is an equivalence, so inverse image agrees with direct image
along the inverse. The induced homeomorphism of epigraph subspaces preserves the constant integral
sheaf, and direct-image composition identifies the ambient closed-support sheaves. Exact proper
pullback then transports this comparison through compact support and indization; exact-derived
functoriality and the translation descent squares transport it through both derived categories and
both generated Verdier quotients.

## Lean target

Generic homeomorphism transport in `StokesSheafHomeomorph.lean`, followed by all seven
exponential-object translation comparisons in `StokesEnhancedExponentialTranslation.lean`.

## Log

- 2026-08-24 — corpus search found support-preimage covariance and quotient translation actions,
  but no sheaf-level or enhanced-object translation comparison
- 2026-08-24 — formalized generic sheaf transport and exponential translation covariance; direct
  Lean checks and targeted module builds pass; all new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`
