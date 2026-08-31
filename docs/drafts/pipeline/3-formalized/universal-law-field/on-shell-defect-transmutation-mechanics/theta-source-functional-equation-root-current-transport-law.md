# Theta-source functional-equation root-current transport law

- **ID:** `ULF-ODTM-5`
- **Stage:** 3 — formalized in Lean 4
- **Scientific status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [LEAN-FORMALIZED] [NOT RH]`
- **Paper proof:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/on-shell-defect-transmutation-mechanics/theta-source-functional-equation-root-current-transport-law-paper.md`
- **Lean modules:**
  `HTGeometry.ConstitutiveEvenPositiveWeightedReflection`;
  `RHTower.HedenmalmThetaSourceFunctionalEquationRootCurrentTransport`

## Formalized capstones

Lean proves the weighted source reflection is a linear isometric involution, its quantile lift
satisfies `R B R = -B`, and its restriction maps every complete generalized `mu`-root block
unitarily onto the `-mu` block.  Nilpotent powers transform by `(-1)^j`; the terminal conormal
current transforms by `(-1)^(d_mu-1)`.  Kernel, range, pointwise norm, and full operator norm are
preserved.  At an actual Xi support point the character exponent is analytic multiplicity minus
one.

## Verification

Scratch and project-path elaboration pass.  Targeted named leaf build passes
(`10970/10970`); umbrellas are wired but were not built.  Audited capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`.  Scoped scan contains no `sorry`, `admit`, `axiom`,
`opaque`, or `unsafe`; formal lint and `git diff --check` pass.

## Remaining gate

Reflection is now an information-neutral action on actual source histories, not determinant-level
symmetry.  It does not constrain which source fibres occur.  RH still requires an arithmetic
formation/properness law controlling occurrence.
