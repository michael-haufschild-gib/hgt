# FZZ parity fixed-monomial determinism no-go

- **ID:** HC26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** FZZ-P
- **Date:** 2026-08-28
- **Statement:** No fixed monomial power of the literal source eigenline is both unit-circle phase-complete and injective in positive physical scale.

## Goal

Determine whether HC25's fixed-quintic phase completion can itself provide deterministic source
dynamics. Phase completeness without unique scale may still hide a branch-selection burden.

## Result

For `y(beta)` the positive-imaginary balanced literal source eigenline:

1. degrees `0,1,2,3,4` are unit-circle incomplete;
2. for every `n>=5`, the upper-left unit phases at angles
   `3*pi/4-pi/n` and `3*pi/4+pi/n` are distinct but have equal `n`th powers;
3. HC23 realizes those phases at two positive physical scales, which are necessarily distinct;
4. every phase-complete fixed monomial therefore has an explicit two-scale collision;
5. no fixed monomial is simultaneously phase-complete and scale-injective.

This is sharp against HC25: degree five is the least complete fixed monomial, but every complete
degree is intrinsically multiscale.

## Proof certificate

For `n>=5`, `pi/n <= pi/5 < pi/4`, so both collision angles lie strictly in `(pi/2,pi)`.
Their exponentials are distinct because cosine is strictly decreasing on `[0,pi]`. Their angular
difference is `2*pi/n`; De Moivre plus exponential periodicity gives equality of their `n`th
powers. HC23 maps each root to a positive source scale. Equal scales would give equal source roots,
contradicting distinctness. Degrees below five are excluded by HC25's explicit missed phases,
together with the trivial degree-zero obstruction.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityFixedMonomialDeterminismNoGo.lean`.

Main declarations:

- `fzzCigarParityFixedMonomialCollisionRoots_ne`
- `fzzCigarParityFixedMonomialCollisionRoots_pow_eq`
- `exists_distinct_pos_fzzCigarParityFixedMonomialEigenphase_eq`
- `FZZCigarParityFixedMonomialPhaseScaleInjective`
- `exists_distinct_pos_fzzCigarParityFixedMonomialEigenphase_eq_of_complete`
- `not_fzzCigarParityFixedMonomialPhaseComplete_and_scaleInjective`

Verification: direct `lake env lean` passed; target-only `lake build
GaloisForLFunctions.RHTower.FZZCigarParityFixedMonomialDeterminismNoGo` passed (9763 jobs); six
audited endpoints report only `[propext, Classical.choice, Quot.sound]`.

## Literature and corpus novelty audit

Mandatory corpus searches covered source-scale injectivity, fixed-quintic fibre multiplicity,
deterministic landing, FZZ phase winding, and branch ambiguity. No prior corpus theorem classifies
all fixed monomial degrees or proves this completeness-versus-injectivity dichotomy.

Primary-source searches checked Ikhlef--Jacobsen--Saleur, *An integrable spin chain for the
SL(2,R)/U(1) black hole sigma model* (arXiv:1109.1119); Jatkar, *The Spectrum of
SL(2,R)/U(1) Black Hole Conformal Field Theory* (arXiv:hep-th/9203063); Israel--Pakman--Troost,
*Extended SL(2,R)/U(1) characters* (arXiv:hep-th/0402085); and the FZZ/sine-Liouville sources
audited for HC25. They treat reflection amplitudes, spectra, winding sectors, and correlators, but
the searches found no coefficient-faithful theorem giving this all-degree phase-completeness versus
scale-injectivity no-go. Novelty claim is bounded to corpus plus these searches as of 2026-08-28.

## Gates

- [x] 0 -> 1: source-pure sharp no-go and constructive collision
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: unconditional Lean theorem, target build, axiom audit
- [ ] 3 -> 4: standalone publication draft

## No-go closure

- **Exact killing theorem/mechanism:** every phase-complete fixed monomial has two distinct positive source scales with the same reported phase.
- **Strongest positive survivor:** HC25's fixed quintic remains minimally phase-complete; HC26 supplies explicit collision roots and scales at every complete degree.
- **New insight:** phase capacity and dynamical determinism are incompatible within the entire fixed-monomial family. Additional source data is mathematically necessary.
- **Status:** survivor and obstruction are dependency-closed and formalized in this module.

## Remaining burden

Construct a literal FZZ/GFZZ observable paired with the monomial phase that separates collision
scales and is derived before divisor specialization. Candidates must use amplitude, derivative,
orientation, interaction coefficient, or another source-native coordinate; phase alone is terminal.

## Log

- 2026-08-28 — conjectured from HC25 winding excess
- 2026-08-28 — all-degree dichotomy proved constructively
- 2026-08-28 — formalized, wired, target-built, and axiom-audited
