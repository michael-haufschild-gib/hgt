# Artin holomorphy formalization frontier (2026-08-14)

Active user goal: fully formalize literature frontier, build all missing infrastructure, then resume conjecture/proof-pivot research toward unconditional Lean proof/disproof. Never full build; source checks via `lake env lean <file>`, targeted final olean only, wire modules into RHTower umbrella without building it.

Formalized modules, all source-checked, targeted-built, and #print-axiom audited with only propext/Classical.choice/Quot.sound:
- `RHTower/ArtinStarkSimpleZero.lean`: exact integer-order simple-zero classifier.
- `ArtinVirtualCharacter.lean`: FDRep character generator closure, genuine/virtual chars, restriction, conjugacy invariance, identity values. Added universe-safe `smallModelRepresentation` / `smallModelFDRep`; theorem every finite-dimensional representation in arbitrary carrier universe has same-character FDRep model.
- `ArtinVirtualCharacterPairing.lean`: normalized pairing; general representation pairing = finrank intertwining; genuine pairings Nat, virtual pairings Int.
- `ArtinCharacterInduction.lean`: actual coinvariant induced representation, induced character is concrete generator via smallification, genuine/virtual induced chars.
- `ArtinFrobeniusReciprocity.lean`: new universe-polymorphic raw IntertwiningMap adjunction `indResIntertwiningEquiv`; pairing Frobenius reciprocity.
- `ArtinMonomialCharacter.lean`: linear chars H→*ℂˣ, scalar representation exact character, induced monomial genuine/virtual chars, specialized pairing reciprocity.
- `ArtinCharacterMultiplicity.lean`: canonical Nat/Int multiplicities, biadditivity/negation, genuine nonnegativity, monomial multiplicity and genuine nonnegativity.
All imports wired at lines ~93-99 of `RHTower.lean`; umbrella deliberately unbuilt. Formalized cards in `docs/drafts/pipeline/3-formalized/artin-*.md`.

Important discovered obstruction and pivot:
- mathlib `FDRep ℂ G` carrier is Type 0; `Representation.ind` carrier lives in group universe, so arbitrary-universe induction cannot bundle directly.
- Solved without restricting G: conjugate any finite-dimensional representation to canonical coordinates `Fin(finrank) → ℂ`, preserving character.
- mathlib categorical `Rep.indResHomEquiv` also imposes common large universe. Solved by direct universe-polymorphic intertwining equivalence copied at raw representation level.
- Higher principle: use induction–restriction adjunction to transport character multiplicities; do not prematurely depend on induced-character coset formula.

Current open finite-group frontier:
- complete irreducible-character family/decomposition from Maschke;
- monomial span and full Brauer induction theorem;
- induced degree/index and explicit character formula;
- Heilbronn order character/effectivity and Stark/Foote–Murty bridge.
No Artin L-function/Frobenius determinant infrastructure yet. Novelty loop remains paused until literature frontier closed.

Prior research card `artin-holomorphy-global-polar-effectivity.md`: Ginsberg PSL2(q) static effectivity obstruction; synthetic divisor-factorization obstruction; positive survivor requires genuine Frobenius determinant Euler source→continued divisor law.

Repo lint was run after early modules: no Artin-owned errors; failure only unrelated concurrently created unwired modules. Latest owned files wired. No stale Artin Lean processes.