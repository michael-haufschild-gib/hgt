# Route E terminal-leg multilinear resonance (2026-08-07)

New formal theorem family: `formal/GaloisForLFunctions/RHTower/RouteETerminalLegMultilinearResonance.lean`, imported by `formal/GaloisForLFunctions/RHTower.lean`.

At physical resonance `tY = π / log Y`, any entrywise absolutely summable complex cross-prime kernel whose nonzero entries have at least one terminal coordinate in `0 ≤ log Y - log p ≤ η log Y` has oscillatory quadratic sum norm at most `2 π η` times kernel ℓ¹ mass. For arbitrary finite arity, one source-selected terminal leg gives `π η · 2^|I|` times coefficient ℓ¹ mass; if every leg is terminal, the bound is `(π η)^|I|` times coefficient ℓ¹ mass. Signs, Hermitian symmetry, positivity, and aperture-independence are not assumed.

Scientific consequence: “cross-scale” alone is not an escape. Every fixed-arity, entrywise-ℓ¹ signed terminal-shell monomial mechanism is excluded unless coefficient mass diverges/renormalizes. Genuine survivors are: a no-terminal-leg component with a proved signed physical cutoff connector; arity growing with aperture; or relation-valued/pre-norm cancellation not reducible to such an ℓ¹ monomial sum. Diffuse Fisher codiagonal and grade-recurrent entropy-spread cube remain candidates but do not yet supply the required signed physical connector.

Paper card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-e-terminal-leg-multilinear-resonance.md`. Active Route E and frontier-map cards were updated. Exact open core remains `GIBBS-SINGULAR-OR-GROWING-ARITY-PHYSICAL-TRANSVERSE-SOURCE`; `OPEN-SOURCE-001`, Route E, and RH remain open.

Verification: `lake env lean GaloisForLFunctions/RHTower/RouteETerminalLegMultilinearResonance.lean` passed. Missing olean was built with only `lake build GaloisForLFunctions.RHTower.RouteETerminalLegMultilinearResonance` (9722/9722). `#print axioms` for all three complete tsum theorems reports only `propext`, `Classical.choice`, `Quot.sound`. No full build was run.