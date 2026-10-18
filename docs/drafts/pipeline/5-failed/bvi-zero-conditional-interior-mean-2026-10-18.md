# Endpoint deletion does not imply zero conditional interior mean

- **ID:** BVI-ZERO-CONDITIONAL-MEAN-2026-10-18
- **Stage:** 5-failed
- **Type:** FALSIFIED, with formalized positive survivor
- **Source:** Problem 4 conditional-orthogonality mechanism
- **Statement rejected:** Deleting moduli incident to n or n+1 forces the remaining centered sawtooth to have zero mean conditioned on d dividing n+1.

## Exact obstruction

For J_e(n)=-psi_e(n) with both adjacent jump residues deleted, put
g=gcd(d,e). The mean over the reduced predecessor progression is

    gamma(d,e) = 0 if g=1, and (e-g)/(2e^2) otherwise.

Consequently gamma(a,2a)=1/(8a)>0 for every a>=2. The squarefree pair
d=3,e=6 already gives a nonzero correction. Endpoint coprimality of n and
n+1 does not imply coprimality of a jump modulus and an interior modulus.
This falsifies only the zero-mean sub-conjecture, not the full contraction.

## Strongest positive survivor

Exact correction and complete zero classification, followed by uniform
finite-horizon bounds after subtracting that correction:

    |sum_{k<L} (J_e(d-1+dk)-gamma(d,e))| <= e/g,
    |sum_{k<L} w_{d,T}(k)(J_e(d-1+dk)-gamma(d,e))| <= e/(dg).

Here w is the nonnegative compensated reciprocal jump weight. The theorem
also bounds the actual finite-cutoff `bezoutInteriorSawtoothSum` with
arbitrary signed coefficient weights and explicit dependence on every
modulus. The complete proof and scope limits are recorded in
`../3-formalized/bvi-interior-jump-orbit-centering-and-compensated-bounds-2026-10-18.md`.

## New insight

Resonance occurs precisely at proper shared factors of composite interior
moduli. Prime interior moduli have zero conditional mean. The mean correction
has a reciprocal-modulus gain; the unsummed finite-orbit error remains the
obstruction to the requested global inequality. Preserve signed arithmetic
coupling when attacking that error.

## Status

Dependency-closed paper proof and original-source Lean certificate:
`InteriorJumpOrbitCenteringAndCompensatedBounds.lean`.
The exact obstruction is `interiorJumpOrbitMean_double_pos`; exact
classification is `interiorJumpOrbitMean_eq_zero_iff`; finite-cutoff positive
survivor is `abs_bezoutInteriorSawtoothSum_centered_jump_compensated_le`.
All fourteen public declarations passed axiom audits with only standard
Lean axioms. No numerical experiments or unproved analytic premises.

Corpus audit identified existing fractional-atom orbit infrastructure;
no global novelty claim. Broader programme remains active on
`../1-in-progress/bvi-interior-martingale-coercive-contraction-2026-10-18.md`.
