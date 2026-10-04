# PM: interpolation through the literal imaginary damping boundary

- **ID:** pm-imaginary-damping-interpolation
- **Stage:** 5-failed
- **Type:** FALSIFIED, with exact positive classification
- **Conjecture falsified:** the literal complex power-damped Möbius Fermi source is canonically L2 along a neighborhood of zero on the imaginary damping axis.

## Exact obstruction

Canonical admission at an imaginary parameter z would transport every positive critical zero rho with Im(rho-z)>0 to another zero rho-z. The proof uses the actual finite source, absolute dilation interchange, analytic continuation of the cleared Mellin identity, and the canonical Hilbert boundary decay. It makes no simplicity assumption.

An unconditional positive Hardy zero has an isolated punctured neighborhood. Every sufficiently small nonzero imaginary shift places the transported point strictly inside that neighborhood, a contradiction. Therefore the required imaginary boundary is not admitted, even separately at any sufficiently small nonzero shift.

## Strongest positive survivor

There exists delta>0 such that for all real y with |y|<delta,

`A_(iy) belongs to canonical L2 if and only if y=0`.

Both signs of y are covered. At zero the literal source equals supported dyadic Haar. The additional positive structural law is the general critical-zero transport statement, with exact identification of the new complex source with the existing real source at real parameters.

Paper proof and audit: [isolated imaginary admission](../3-formalized/pm-complex-damping-boundary.md). All fifteen public exports passed the targeted old-mode leaf build, mandatory final actual-file Lean check and separate axiom queries, using only propext, Classical.choice and Quot.sound. The umbrella import appears once and generated indexes are refreshed. Formal lint has twelve unrelated unreachable leaves, none from this work. The exact positive classification is fully formalized.

## Surviving hard target

This falsifies only the proposed boundary of this interpolation family. Positive real damping remains the RH route. The complete signed natural-denominator energy, or the exact weighted joint critical-line moment with every mixed term retained, still needs an upper bound for arbitrarily small positive real damping. Neither failure of this interpolation boundary nor the existing derivative obstruction is an RH falsification.
