# FZZ parity independent radial-phase incidence classification

- **ID:** HC28
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SHARP NO-GO
- **Route:** FZZ-P
- **Date:** 2026-08-28
- **Statement:** Independent literal Fermi-radial and fixed-quintic phase scales classify all dyadic Mellin characters into exactly one transverse sector; selectable sectors are universally nonselective.

## Goal

Audit whether HC27's radial clock, once allowed to vary independently of HC25's phase scale, can
provide a new RH-selective landing law.

## Result

Let `r(beta)=-Re y(beta)` and `q(gamma)=y(gamma)^5`, for positive source scales. HC27 gives
`0<r(beta)<1` and exact radial surjectivity; HC25 gives `||q(gamma)||=1` and phase surjectivity.
Define

- contracting encoding `C(beta,gamma)=r(beta)q(gamma)`;
- unit encoding `U(gamma)=q(gamma)`;
- expanding encoding `E(beta,gamma)=r(beta)^(-1)q(gamma)`.

Lean proves:

1. every nonzero `z` with `||z||<1` has a contracting representation;
2. every `z` with `1<||z||` has an expanding representation;
3. `chi(rho)` has contracting incidence iff `Re rho<1/2`;
4. it has unit incidence iff `Re rho=1/2`;
5. it has expanding incidence iff `Re rho>1/2`;
6. every dyadic Mellin character lies in exactly one of these three sector classes;
7. every open-strip zeta divisor is therefore sector-representable unconditionally;
8. arbitrary-sector incidence cannot characterize the critical line.

The classification is exact because
`||chi(rho)||=exp(log(2)(Re rho-1/2))`. Radial scale records transverse sign, but allowing source
to select contracting/unit/expanding sector makes incidence universal.

## Proof certificate

The literal balanced eigenline is unimodular with positive imaginary part, so its negative-real
coordinate lies strictly in `(0,1)`. HC27 supplies every such coordinate. For nonzero `z`, normalize
its phase as `z/||z||`; HC25 realizes that unit phase. Choosing radial value `||z||` constructs the
contracting case, while choosing `||z||^(-1)` and taking reciprocal constructs the expanding case.
Taking norms reduces the converses to `exp(x)<1 iff x<0` and `1<exp(x) iff 0<x`. Real trichotomy
then gives existence and uniqueness of the sector class.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityIndependentRadialPhaseIncidenceClassification.lean`.

Main declarations:

- `exists_pos_fzzCigarParityIndependentContractingQuinticEncoding_eq`
- `exists_pos_fzzCigarParityIndependentExpandingQuinticEncoding_eq`
- `fzzCigarParityIndependentContractingQuinticIncident_iff`
- `fzzCigarParityIndependentExpandingQuinticIncident_iff`
- `fzzCigarParityIndependentRadialPhaseIncidenceTrichotomy`
- `existsUnique_fzzCigarParityIndependentRadialPhaseSectorIncident`
- `fzzCigarParityIndependentRadialPhaseDivisorSectorComplete`
- `not_fzzCigarParityIndependentRadialPhaseAnySectorIncident_iff_criticalLine`

Verification: direct `lake env lean` passed; target-only `lake build
GaloisForLFunctions.RHTower.FZZCigarParityIndependentRadialPhaseIncidenceClassification` passed
(9765 jobs); seven audited endpoints report only `[propext, Classical.choice, Quot.sound]`.

## Literature and corpus novelty audit

Mandatory corpus searches covered two-scale FZZ amplitude/phase incidence, independent radial-phase
nonselection, and dyadic Mellin norm sectors. Existing corpus work gives generic carrier
radial-phase factorization and reflected reciprocal norm, but no theorem connects HC27's literal
Fermi clock and HC25's fixed quintic to a complete, unique three-sector incidence classification.

Primary-source searches checked Ikhlef--Jacobsen--Saleur, *An integrable spin chain for the
SL(2,R)/U(1) black hole sigma model* (arXiv:1109.1119); Hikida--Schomerus, *The FZZ-Duality
Conjecture -- A Proof* (arXiv:0805.3931); Becker--Becker, *Interactions in the SL(2,R)/U(1) Black
Hole Background* (arXiv:hep-th/9310046); and Jatkar, *The Spectrum of SL(2,R)/U(1) Black Hole
Conformal Field Theory* (arXiv:hep-th/9203063). They treat duality, spectra, amplitudes, reflection,
and density of states; searches found no coefficient-faithful Fermi/quintic incidence trichotomy or
universal-sector nonselection theorem. Novelty claim is bounded to corpus plus these searches as of
2026-08-28.

## Gates

- [x] 0 -> 1: corpus-derived exact three-sector conjecture
- [x] 1 -> 2: dependency-closed constructive proof
- [x] 2 -> 3: unconditional Lean theorem, target build, axiom audit
- [ ] 3 -> 4: standalone publication draft

## No-go closure

- **Exact killing theorem/mechanism:** selectable contracting/unit/expanding sectors represent every
  dyadic Mellin character, so arbitrary-sector incidence is identically true and cannot detect the
  critical line.
- **Strongest positive survivor:** sector class is unique and exactly equals the sign of
  `Re rho-1/2`; the unit sector alone remains a precise critical-line detector.
- **New insight:** radial amplitude is informative only when dynamics constrains its sector or
  couples radial and phase scales before seeing the target.
- **Status:** obstruction, classification, and survivor are dependency-closed and formalized.

## Remaining burden

Derive from interacting FZZ/GFZZ dynamics a source-first law that forces the unit sector, or a
same-scale radial-phase coupling whose image excludes both off-wall sectors. Independent amplitude
and phase matching with selectable reciprocal sector is retired.

## Log

- 2026-08-28 — conjectured from HC27 and corpus Mellin carrier factorization
- 2026-08-28 — exact three-sector incidence and universal nonselection proved
- 2026-08-28 — formalized, wired, target-built, and axiom-audited
