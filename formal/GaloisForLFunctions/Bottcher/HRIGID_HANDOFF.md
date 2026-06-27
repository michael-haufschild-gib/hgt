# Handoff: current `hRigid` branch of `q62_independence`

This handoff supersedes the old "make a new `Rigidity.lean` file" note.  The hRigid lane has already
created substantial axiom-clean Lean infrastructure.  Do not redo it, and do not replace the remaining
work by axioms, `sorry`, or terminal hypotheses.

## Current verified surface

The main active files are:

- `DendriteContinuesAcross.lean`
  - `not_continuesAcross_of_emptyInterior_modulus`
  - `hnb_of_emptyInterior_modulus`
- `RelativeFibreGeneric.lean`
  - `fibrePoly_eq_denseFibreCoeff`
  - `exists_sparse_fibre_separable_crossing`
  - `exists_commonBasin_input_of_sparse_fibre_crossing`
- `RelativeRigidityNaturalBoundary.lean`
  - natural-boundary hRigid bridges from `ContinuesAcross` obstruction;
  - empty-interior specialization deriving the obstruction from the Böttcher modulus;
  - local/off-other `γ` endpoints;
  - common-region and common-basin endpoints;
  - level-root tower endpoints;
  - crossing-driven endpoints that create the separable target fibre internally;
  - square-root-family endpoints that create the `2^n` power law internally via `hpow_of_sqrt_family`.

The newest strongest square-root endpoints are:

- `noRelation_phiMero_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing`
- `hrig_phiMero_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing`
- `q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing`
- `q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_repellingG`

Verification from the current session:

- `lake build GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary`
- `git diff --check`
- placeholder scan for `sorry`/`admit`/`axiom`/`opaque`/`unsafe` over touched hRigid files
- `scripts/formal_tools.py index`
- `scripts/formal_tools.py lint --check-generated`
- `#print axioms` for the newest square-root endpoints: only `[propext, Classical.choice, Quot.sound]`

## What the created pieces already remove

- The natural-boundary predicate is no longer a raw input in the empty-interior case.
- The selected separable fibre is no longer a raw input in the crossing route; it is produced by
  `exists_commonBasin_input_of_sparse_fibre_crossing`.
- The full `2^n` power-law tower is no longer a raw input in the newest route; it is produced by
  `hpow_of_sqrt_family` from a coherent square-root family.
- The abstract `Transcendental (RatFunc ℂ) (phiMero c₂ hU₂)` can be replaced by the existing
  repelling/simple-root interface in the `_repellingG` endpoints, but that interface itself is still a
  real input unless separately discharged.

## Remaining work for a hypothesis-free both-connected theorem

The final theorem is not done.  A theorem that still carries these as terminal hypotheses must not be
presented as the q62 close.

1. **General Eremenko-van Strien natural-boundary obstruction.**
   Current code proves the obstruction from `interior (filledJulia c) = ∅`.  The full connected
   nonexceptional theorem needs an axiom-clean Lean proof that analytic continuation of the basin
   Böttcher branch through a Julia point forces a smooth Julia piece, then E-vS rigidity forces
   `c ∈ Exceptional`, contradiction.

2. **Capacity/common-basin crossing geometry.**
   The hRigid endpoint now consumes sparse crossing data plus pointwise common-basin target geometry.
   The missing created theorem should supply this geometry from distinct connected parameters:
   enough points in `filledJulia c₁ ∩ (filledJulia c₂)ᶜ`, accumulating inside an analytic coefficient
   region, with local preconnected basin sectors from the carrier `U` to the selected point.

3. **Actual branch construction on connected basins.**
   The newest endpoint accepts coherent square-root towers and derives the level-root power law.
   A final connected theorem must either construct these towers axiom-clean, or replace this input by
   an already-formalized global single-valued Böttcher branch on `(filledJulia c)ᶜ`.

4. **Repelling/simple-root transcendence input.**
   The `_repellingG` wrappers remove the abstract `hG`, but the callback producing the repelling
   simple-root data remains to be discharged if the final theorem uses that route.

## Coordination boundary

- Avoid the hDisc files unless the user explicitly redirects: `HDiscLoopDeck.lean`, deck/cover
  construction files, and the disconnected Kummer lane are separate work.
- `Bottcher.lean` already imports the new hRigid files.  Do not churn the import list except when a new
  module is genuinely added.
- Keep every new theorem axiom-clean.  Run `#print axioms` from `/tmp`, not by editing the tree.

## Target shape

The target remains an unconditional both-connected `NoRelation` theorem for the genuine Böttcher
coordinates, suitable as the `hRigid` branch of `q62_independence`.  The proof must have no extra axioms,
no `sorry`/`admit`, and no terminal hypothesis that is just the missing theorem in another form.
