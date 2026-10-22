# Von Mangoldt–Gamma Beta-reflection positivity-gap universality law

## Status

Fully proven on paper; Lean 4 source written. Exact check deferred because imported
`VonMangoldtGammaCofinalStrictBianchiLaw.olean` is absent; dependency build is reserved for final
audit by user rule.

## Theorem-first source

- `vonMangoldtGammaCofinalBianchiGram_posDef_of_injective`: every positive displacement and every
  injective raw-order packet give a strictly positive cofinal Gamma--Bianchi Gram.
- `det_vonMangoldtGammaCofinalBianchiGram_pos_of_injective`: its determinant is strictly positive.
- `infiniteVonMangoldtGammaFactorialBetaReflection_eventually_not_posSemidef`: the canonical
  factorial/Beta-reflected trace Gram is eventually not positive semidefinite on packet `[0,2]`.

Both branches use same cofinal von Mangoldt--Gamma source, same displacement, and same even-order
packet. Corpus research found no theorem recording their opposite matrix-order phases.

## Universal law

Eventually as positive displacement tends to infinity, raw cofinal Gamma--Bianchi Gram at orders
`[0,2]` is positive definite with positive determinant, while canonical factorial/Beta reflection
on those exact orders is not positive semidefinite.

## Paper proof

Order map `[0,2] : Fin 2 → Nat` is injective. Eventually `x>0`, so cofinal strict Bianchi theorem
gives raw positive definiteness and positive determinant. Intersect this eventual set with existing
eventual Beta-reflection obstruction. No numerical computation is used.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.VonMangoldtGammaBetaReflectionPositivityGapUniversalityLaw`.

Full exact command is deferred to final dependency audit.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
