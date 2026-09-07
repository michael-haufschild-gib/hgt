# EDQ completed horizontal contact and multiplicity parity

Stage: 3-formalized. Dependency-closed paper proof and new-declaration Lean audit complete.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
Objective: determine which interior sign proposals the actual completed arithmetic half can satisfy. RH remains open.

## Dependency-closed paper argument

Use the actual completed arithmetic half A_p from EulerDeletionHolomorphicChronology.
At a critical-line center rho and a real displacement d with 0<d<1/2, its exact
functional equation and conjugation symmetry give

`Re(A_p(rho+d))+Re(A_p(rho-d)) = Re(xi(rho+d)^2)`.

This identity retains both horizontal sides. At an actual critical zero of full
analytic multiplicity m, the corpus's analytic-order factorization gives
`xi(z)=(z-rho)^m*g(z)` near rho, with g analytic and c=g(rho) nonzero.
Xi reflection sends rho+d to rho-d and conjugates its value. After canceling
the nonzero real displacement power in the two factorization identities and
taking d to zero, this forces `conjugate(c)=(-1)^m*c`. Consequently

`Re(c^2)=(-1)^m*norm(c)^2`.

Continuity of g justifies the full contact limit

`[Re(A_p(rho+d))+Re(A_p(rho-d))]/d^(2*m) -> (-1)^m*norm(c)^2`.

The finite pair is identical for every nontrivial modulus, since its right
side contains only xi. The contact magnitude can therefore be chosen once
for the zero, independently of the modulus. Obtain the local sign neighborhood
from modulus two and shrink it below 1/2; the exact finite-pair identity then
transfers the same bound to every other nontrivial modulus. This proves a
uniform-in-modulus statement, without interchanging an infinite family of limits.

The magnitude is strictly positive. Thus an odd-order critical zero has a
strictly negative reflected horizontal pair, with an eventual bound at most
`-norm(c)^2*d^(2*m)/2`; at an even-order critical zero the pair is at least
`norm(c)^2*d^(2*m)/2`. No simplicity assumption is used in this classification.

The corpus's unconditional cofinal simple-critical census supplies m=1 above
every height. Applying the odd contact bound to any nontrivial channel produces
a strictly negative value of Re(A_p) at one of the two nearby off-line source
points. These are source points near actual critical zeros, not asserted
off-line zeta zeros. Therefore blanket nonnegativity of Re(A_p) throughout the
strip, even only at all sufficiently high source points, cannot be an RH producer.

## Positive survivor and remaining route

The survivor is the exact multiplicity-sensitive horizontal contact, including
its nonzero leading magnitude and quantitative local sign uniform across all
nontrivial moduli. Boundary positivity
and holomorphy remain valid; any usable interior comparison must permit the
negative neighborhoods forced by odd critical multiplicity. The EDQ route is
not retired. Universal annihilation of the earlier oriented current remains open.

Corpus basis: EulerDeletionHolomorphicChronology, GaussianZetaCounting,
GaussianZetaBridge, FiniteToEntireRealApproximation, ArithmeticJointJetExclusion,
Zeta23SimpleCriticalDensity, ArithmeticFiniteZeroDisplacement, and the existing
XiWard aperture-contact limit as a finite-to-limit proof pattern. Other-source
parity and curvature theorems are not substituted for the literal completed half.
## Formal certificate

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionHorizontalContact.lean`
(244 lines; eight public theorems, one public definition, nine private helpers).
Namespace: `RHTower.DeletionHorizontalContact`.

- `horizontalPair_eq_xi_sq` and `horizontalPair_channel_independent`: the exact finite horizontal pair is the real part of genuine xi squared, independent of every nontrivial modulus.
- `exists_horizontal_contact`: at every actual critical zero, one strictly positive magnitude gives the full order `2*m` and parity `(-1)^m` for all nontrivial moduli.
- `odd_contact_negative` and `even_contact_positive`: one magnitude and one positive neighborhood give the quantitative contact sign simultaneously for every nontrivial modulus.
- `exists_high_simple_center`: the unconditional simple-critical census supplies actual multiplicity-one critical zeros above every height.
- `exists_high_negative_source`: every nontrivial modulus has strictly negative completed real parts at off-line source points above every height. The negative side can depend on the modulus; no common negative point for all moduli is claimed.
- `not_eventually_nonnegative_completedSplit`: even eventual blanket strip nonnegativity of the literal completed half is impossible.

Final scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_contact.lean`, exit 0,
no diagnostics. Final leaf audit:
`LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionHorizontalContact`,
exit 0; only the new leaf rebuilt (6.8 seconds). Dependencies cached/replayed.
Umbrella import added without a full or umbrella build.

New-only axiom audit: `lake env lean /tmp/edq_contact_axioms.lean`, exit 0.
All nine public declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`; their dependency closure covers the private helpers.
No added axioms, admissions, numerical premises, or external computation certificates.

The [retired blanket positivity shortcut](../5-failed/edq-completed-global-accretivity.md)
retains this exact contact classification as its formalized positive survivor.
RH remains unproved and unfalsified. Universal current annihilation and a valid
source comparison selecting zero locations remain open.

## Repository checks and cleanup

Repository lint ran once. It reports seven unrelated unwired modules:
`MobiusDivisorTwoChannelPrimeBlocks`, `ThetaCuspEvenFourEffectiveErrors`,
`ThetaCuspEvenFourEffectiveReserve`, `ThetaCuspEvenFourEffectiveSchur`,
`ThetaCuspEvenFourExplicitTail`, `FirstAtomEvenTailReserve`, and
`HankelFourPerturbation`. It reports no error for this new module. Those other
work areas were left untouched; a global lint pass is not claimed.

The search index was refreshed once. Scoped whitespace, local links, exact
umbrella wiring, equality with the checked scratch source, and forbidden
declaration checks passed. No owned Lean or Lake process remained.
All three owned scratch Lean sources were removed; audit logs remain under
`/tmp/edq_contact` with `.api.log`, `.check.log`, `.build.log`, `.axioms.log`,
`.lint.log`, and `.index.log` suffixes.
