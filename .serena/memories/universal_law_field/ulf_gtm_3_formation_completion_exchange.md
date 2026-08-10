# ULF-GTM-3 — compact formation/completion exchange

Paper: `docs/drafts/pipeline/2-fully-proven/universal-law-field/genesis-termination-mechanics/compact-formation-depth-completion-exchange-and-observer-erasure-law.md`.
Lean: `formal/GaloisForLFunctions/HTGeometry/ConstitutiveFormationCompletionExchange.lean`.
Stage3: `docs/drafts/pipeline/3-formalized/universal-law-field/genesis-termination-mechanics/compact-formation-depth-completion-exchange-and-observer-erasure-law-formalized.md`.

Mechanism: finite continuous formation families on compact Hausdorff law spaces commute with closure at each bounded word depth. Completion-born laws lie in an exact limit-exchange boundary and force effective realizations of arbitrarily large formation depth in every neighborhood. Mutually bounded generator dictionaries preserve boundary and depth up to linear distortion. Continuous equivariant observers can erase but cannot create boundary; injective observers preserve it.

Lean certification: direct elaboration passed; formal lint passed; `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` passed (11,430 jobs). Axiom audit on capstones reports only `propext`, `Classical.choice`, `Quot.sound`. Umbrella import wired.

Sharp boundaries: infinitely many continuous constant generators on `OnePoint ℕ` can break completion exchange at depth one; compactness, continuity, and finite signature are load-bearing. Earlier compact-counterwitness-escape candidate was retired as regression because RBD/Kőnig machinery already covered it; failed card records this.

Do not present this as RH proof or route theorem. It is a route-independent genesis mechanism and one law of the emerging universal field.