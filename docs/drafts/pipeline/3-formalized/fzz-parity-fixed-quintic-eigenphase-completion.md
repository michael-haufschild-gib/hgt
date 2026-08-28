# FZZ parity fixed quintic eigenphase completion

- **ID:** HC25
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** FZZ-P
- **Date:** 2026-08-28
- **Statement:** Fifth power of one fixed literal FZZ Krein eigenline covers every unit phase, and five is the least positive monomial degree with this property.

## Goal

Remove HC24's residual target-dependent choice among four quadratic channels. Determine minimal
interaction degree at which one predetermined source monomial has full unit-circle phase capacity.

## Result

Write `y(beta)` for the positive-imaginary balanced literal source eigenline. HC25 proves:

1. every unit complex `z` equals `y(beta)^5` for some `beta>0`;
2. degree one misses `1`;
3. degree two misses `1` because its image has strictly negative imaginary part;
4. degree three misses `-1`;
5. degree four misses `1`;
6. consequently five is the least positive degree whose one fixed monomial orbit is phase-complete;
7. exact fixed-quintic incidence of a centered dyadic Mellin character is equivalent to
   `Re rho=1/2`;
8. fixed-quintic incidence for every open-strip zeta zero is equivalent to RH.

This strengthens HC24 from joint coverage by four selectable quadratic channels to full coverage by
one fixed nonlinear source law. Phase capacity and channel choice are now closed. Remaining FZZ-P
burden is actual dynamical incidence of parity-delay Mellin zeros in this orbit.

## Proof certificate

For unit `z`, write it as `exp(arg(z) I)`. If `arg(z) != pi`, choose

`theta = (arg(z) + 4*pi)/5`;

if `arg(z)=pi`, choose `theta=3*pi/5`. In both cases `pi/2 < theta < pi` and
`exp(theta I)^5=z`. HC23 realizes `exp(theta I)` as `y(beta)` at a positive physical scale.

Minimality uses exact quadrant signs. Degree one cannot hit `1`; degree two lies in the strict lower
half-plane; a factorization of `y^3+1` excludes `-1` from degree three; and factoring `y^4-1`
reduces degree four to a real square, contradicting the strict lower-half-plane square law.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityFixedQuinticEigenphaseCompletion.lean`.

Main declarations:

- `fzzCigarParityUpperLeftFifthRoot_pow_five`
- `exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_of_norm_one`
- `fzzCigarParityFixedMonomialPhaseComplete_five_minimal`
- `fzzCigarParityDyadicMellinCharacter_eq_fixedQuintic_forces_critical`
- `exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_dyadicMellinCharacter_iff`
- `fzzCigarParityFixedQuinticEigenphaseDivisorComplete_iff_rh`

Verification: direct `lake env lean` passed; target-only `lake build
GaloisForLFunctions.RHTower.FZZCigarParityFixedQuinticEigenphaseCompletion` passed (9762 jobs);
six audited endpoints report only `[propext, Classical.choice, Quot.sound]`.

## Literature and corpus novelty audit

Mandatory corpus searches covered FZZ/GFZZ quadratic interactions, OPE/landing laws, unit-circle
powers, winding, complex roots, and scale uniqueness. No prior corpus theorem gives a single fixed
FZZ source monomial with complete phase image or proves its minimal degree.

Primary-source searches checked Hikida--Schomerus, *The FZZ-Duality Conjecture -- A Proof*
(arXiv:0805.3931); Creutzig--Hikida--Ronne, *The FZZ duality with boundary*
(arXiv:1012.4731); Fukuda--Hosomichi, *Three-point Functions in Sine-Liouville Theory*
(arXiv:hep-th/0105217); Creutzig--Hikida, *Higher rank FZZ-dualities*
(arXiv:2010.14681); and the prior cigar reflection sources audited in HC23/HC24. These sources treat
correlators, winding violation, duality, and higher-rank extensions, but the searches found no exact
minimal fixed-power phase-surjectivity theorem for the coefficient-faithful parity/Krein source and
no corresponding RH endpoint. Novelty claim is bounded to corpus plus these searches as of
2026-08-28.

Important scope: `y(beta)^5` is a mathematically fixed monomial interaction phase. HC25 does not yet
derive it as a physical quintic vertex or OPE coefficient of the FZZ conformal field theory. That
identification belongs to the remaining dynamical burden.

## Gates

- [x] 0 -> 1: source-pure statement and exact angle attack
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: unconditional Lean theorem, target build, axiom audit
- [ ] 3 -> 4: standalone publication draft

## Remaining burden

Derive from literal FZZ/GFZZ interaction data—before divisor specialization—that actual zeros of
the source-defined parity-delay Mellin transform obey the fixed-quintic incidence law. Since the
quantified incidence statement is equivalent to RH, it cannot be assumed as a stability axiom or
manufactured by selecting scale from the target character.

## Log

- 2026-08-28 — conjectured from HC23 exact quadrant and HC24 channel-choice residue
- 2026-08-28 — fifth-root construction and degree-1-through-4 obstructions proved on paper
- 2026-08-28 — formalized, wired, target-built, and axiom-audited
