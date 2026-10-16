# OWU: structural sign obstruction

Status: IN PROGRESS. No new theorem claimed.

## Objective and scope

Remove a hard structural obstruction in OWU beyond the existing exact odd-source
purification, energy completion and blind variational attainment. A bound, another
RH equivalence, or a conditional receiver does not satisfy this task.

Mathematical evidence: current Lean sources and corpus search only. No web,
external novelty audit, numerical experiments, or old research Markdown.

## Plan

1. Search the current Lean corpus for mechanisms addressing the remaining sign,
   arithmetic rigidity and slit-cut obstructions; inspect actual declarations.
2. State competing exact conjectures and attack their dependency and sign laws.
3. Complete a dependency-closed paper proof of a substantive survivor before
   formalising it. Continue the conjecture loop after failed attacks.
4. Audit new modules with foreground `lake --old env lean`, inspect axioms from
   scratch, wire umbrellas without building them, run lint, and clean owned files.

## Established baseline

The current `OddSector` modules purify finite smooth odd mixtures at the same
aperture, realize bounded-energy profile limits in the complete form domain, and
attain the arithmetic-blind unit-source minimum. They do not determine its sign.
Its exact objective is the Gamma energy minus twice the squared half-pole moment.
The odd spectral slit measure has nonnegative test weights on both the critical
line and real cut, so positivity of further odd tests alone cannot remove the cut.

## Conjecture log

1. Shift the twisted arc operator to produce an odd, arithmetic-null source.
   Status: OPEN CORE, not a proved construction. Multiplying the spectral
   square by the squared frequency changes the arc operator from M² to
   M²(M−1/4). The existing minimum principle only handles M². A positive
   resolvent transport cannot be assumed: its integration-by-parts boundary
   terms are not killed by the existing arc conditions. No route retired.
2. Exact recovery of complete odd sources in each arithmetic fibre, with no
   aperture enlargement. Status: paper proof being checked below. The current
   energy-completion theorem has only the native-to-completed inclusion; it
   does not show that completed blind minima are limits of native blind tests.

## Paper proof: exact arithmetic recovery

Fix a positive aperture a and an odd form-domain source u. Smooth strict-interior
sources are dense in the exact Gamma form norm (`SuzukiRayleighInfimum`). Apply
the bounded odd projection to a sequence converging to u. Reflection preserves
the aperture and the smooth core. Their energies and autocorrelations converge
to those of u, by continuity of the quadratic form and physical embedding.

Only finitely many positive integer lags can occur: J consists of n≥2 with
log n<2a. Smooth source correlations vanish at and beyond 2a. By density and
continuity, the same is true for complete sources. In particular the equality
case log n=2a is excluded, and never becomes an uncorrectable boundary trace.

For each j in J choose a smooth even bump b supported in a sufficiently small
interval about zero. Its radius is smaller than a−log(j)/2 and the corpus
node-isolation radius for j. The odd translated difference of b realizes a
strictly negative j-coordinate and no other coordinate. The symmetric
translated sum of x*b(x) is odd and realizes a strictly positive j-coordinate
and no other coordinate. Both stay strictly inside the original aperture.
The two nonzero squared norms normalize these to signed unit coordinates.

For each smooth approximant, repair the target-minus-approximant trace vector
using nonnegative multiples of these finitely many fixed coordinate sources.
The coefficients tend to zero, hence every correction profile value and its
literal Weil energy tend to zero. Exact odd window purification turns the
corrected positive mixture into one smooth odd source without changing any
lag, energy, or aperture. Thus the entire arithmetic fibre is recovered exactly
at every stage, while the profile and energy converge to those of u.

For a normalized blind target, the recovered masses tend to one; normalize
the nonzero tail of the sequence. Blindness survives normalization, and the
normalized energies converge to the original energy. Applied to the existing
complete blind minimizer this removes the relaxation gap between the smooth
test problem and the attained complete-domain problem. It does not determine
the sign of that common minimum.

Dependencies to audit in Lean: fixed-aperture signed coordinate construction,
boundary trace vanishing, odd smooth-core sequence, exact positive repair,
purification, and normalization. None assumes positivity or RH.
