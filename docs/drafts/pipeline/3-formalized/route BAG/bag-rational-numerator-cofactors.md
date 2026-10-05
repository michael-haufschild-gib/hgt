# BAG complete rational cone with unrestricted numerator cofactors

- **Stage:** 3-formalized

- Route: signed physical BAG cubic.
- Stage: both production leaves and all40 public axiom audits pass.
- Corpus basis: ChiRamanujanPositiveRationalTrace, ChiRamanujanWeightedRationalTrace,
  ChiRamanujanCofactorPole and ChiRamanujanCriticalGridSource.
- No physical cubic saving or RH proof.

## Rational decomposition [PROVED HERE]

Let S be a finite prime set, R=product S. A positive rational has denominator
prime support in S exactly when every prime valuation outside S is nonnegative.
This follows from coprimality of its reduced numerator and denominator: a
prime dividing the denominator has zero numerator valuation and strictly
negative rational valuation; all remaining valuations are nonnegative.

Separate any such valuation vector into its retained and outside filters.
The outside filter has finite support and nonnegative values, so its product
of prime powers is a positive integer n. The existing rational product map
is injective and agrees with natural prime factorization; therefore n has
exactly the outside valuations and is coprime to R. Conversely, adding the
natural valuation vector of any positive n coprime to R to an arbitrary
retained integer vector produces such a rational. Retained coordinates recover
the vector, and outside coordinates recover n. These maps are inverse.

The resulting explicit equivalence sends (v,n) to n*product_(p in S)p^(v_p).
It retains EVERY numerator cofactor, not merely S-supported numerators.
Its complex character is exactly

    q^(-s) = n^(-s)*product_(p in S)(p^(-s))^(v_p).

The corpus's complex prime-product power theorem justifies this identity for
arbitrary complex s; no imaginary-frequency premise or branch assumption is
added. Apply the equivalence in both coordinates, with a literal rearrangement
of the pair-valued finite valuation vector.

## Complete rational source [PROVED HERE]

Write A=product(1-1/p), a_p=log(p)/p. Define the rational distinguished
coefficient directly, without using the inverse equivalence:

    D_p(q)=A*a_p*product_(l in S)c_(1/l)(v_l(q)+1_(l=p)).

For each positive rational pair (x,y) whose denominator primes lie in S,
retain the full signed cubic D_p(x)*D_q(y)*D_r(x*y)*x^(-s)*y^(-t), summed
over labels p!=r AND q!=r. Coincident first and second labels remain.
The valuation and character identities give pointwise equality with the
previous complete weighted finite-prime cone times BOTH coprime numerator
powers. Restricting the established coprime Dirichlet series to its exact
nonzero support preserves its HasSum. Absolute product summation and the
proved pair bijection therefore give the complete rational-pair HasSum in
Re(s),Re(t)>1, equal to criticalCompletedConeEuler S s t. Arbitrary numerator
primes remain, and no critical unordered sum is asserted.

## Literal grid attachment [PROVED HERE; LEAN VERIFIED]

For every positive integer a, put q=a/R^2. Each retained valuation is
v_p(a)-2. Accordingly, the local normalized base is
I_(p^2 divides a)-I_(p divides a)/p, and the local normalized tag is
I_(p divides a)/p-1/p^2. These are the already identified literal grid
weights. Multiplication and the exact label normalization give
log(p)*T_p(a)*product_(l!=p)B_l(a) for EACH distinguished label. Summing
labels and reducing divisibility modulo R^2 gives the already proved actual
grouped atom mass at a mod R^2. This includes positive lifts of the zero
residue class and all nonprimitive nodes.

If a reduced denominator supported in S does not divide R^2, some retained
prime has denominator exponent greater than two. Reducedness makes its
numerator valuation zero, so its rational valuation is less than -2.
Every label shift is at most one, hence the corresponding local coefficient
vanishes. Thus EVERY distinguished coefficient is zero off the actual grid.
Conversely, if den(q) divides R^2, the positive integer
num(q).natAbs*(R^2/den(q)) gives q=a/R^2 exactly. Every nonzero distinguished
coefficient therefore occurs among these positive lifts. Numerator primes
remain unrestricted throughout.

## Remaining hard mathematical problem

The complete grid attachment gives no uniform growing-profile estimate.
The actual pole, full near-cone region, all integer lifts and tails must be
paired with the literal physical test and controlled together at o(N/log^2 N).
Growing moments, moving cofactors, common-height self-return and RH remain open.

## Audit log

ChiRamanujanRationalCofactors (317 lines,24 public declarations) production62049
and ChiRamanujanRationalGridAttachment (328 lines,16 public declarations)
production15658 pass with empty logs using lake --old env lean leaf -o.
Combined axiom13267 passes all40 with only propext, Classical.choice and
Quot.sound. Index56173 passes; every exact module/name API row and one
umbrella import per leaf verified. No full or umbrella build.

Lint78719 exits1 with24 unrelated unreachable-module errors, all inspected;
no new-leaf or proof-debt finding. Global lint is not clean. Development
rewriting/cast failures were repaired with explicit functions and congruences,
without mathematical premises or resource-limit changes.

Search44715 (rational decomposition) and61153 (grid valuation) complete
nonpartial, inventories65764/65766 complete. Background refresh incomplete;
compiler metadata mostly pending/source-only. All candidate lemmas, source
arguments and ingredient sets inspected. Private prime-product proposals
were mediated through public rational-product results; unrelated
ClassFieldTheory and unsafe float suggestions were not used.

Next-source search31155 (physical pole pairing) is nonpartial65773; its
coords_symm/ABHN proposed cancellation is unrelated and rejected. Search5344
(Mellin pairing) is nonpartial65775; the generic mellinInv_mellin_eq is useful
but requires actual convergence and vertical integrability. The proposed
height-profile/one-variable symmetry ingredient does not supply the full
two-variable physical theorem. These searches establish no cancellation.
RH goal remains ACTIVE.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.ChiRamanujanRationalCofactors`, `GaloisForLFunctions.RHTower.ChiRamanujanRationalGridAttachment`, `GaloisForLFunctions.RHTower.ChiRamanujanCofactorPole`, `GaloisForLFunctions.RHTower.ChiRamanujanCriticalGridSource`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean`/`lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the RHTower umbrella; statements re-verified claim by claim against this paper card):
`GaloisForLFunctions.RHTower.ChiRamanujanRationalCofactors`, `GaloisForLFunctions.RHTower.ChiRamanujanRationalGridAttachment`; base `GaloisForLFunctions.RHTower.ChiRamanujanCofactorPole`, `GaloisForLFunctions.RHTower.ChiRamanujanCriticalGridSource`.

| Claim | Declaration |
|-|-|
| denominator support in `S` ⇔ outside valuations nonnegative | `denominatorValuations_iff` |
| explicit equivalence `(v,n) ↦ n Π p^{v_p}` retaining every numerator cofactor; character identity; pair version | `mixedValuations`, `mixedValuations_injective`, `mixedValuations_surjective`, `mixedValuationsEquiv`, `denominatorRationalEquiv`, `mixedRationalEquiv`, `mixedRationalEquiv_valuations`, `mixedRationalEquiv_value`, `mixedRationalEquiv_retained`, `mixedRationalEquiv_character`, `mixedRationalPairEquiv` |
| complete rational source HasSum `= criticalCompletedConeEuler S s t` (`Re > 1`) | `criticalRationalLabelCoefficient`, `criticalRationalCone`, `criticalRationalCone_equiv`, `criticalRationalCone_hasSum` |
| grid attachment `q = a/R²`: valuations `v_p(a)−2`, base/tag, label, actual grouped mass | `criticalGridRational`, `criticalGridRational_valuation`, `criticalGridRational_base`, `criticalGridRational_tag`, `criticalGridRational_label`, `criticalGridRational_source`, `criticalIntegerSource_grid`, `criticalGridRational_actualMass` |
| zero off the grid; every grid rational and every nonzero coefficient is a positive lift | `criticalRationalLabelCoefficient_off_grid`, `criticalGridRational_exists`, `criticalRationalLabelCoefficient_support` |

No physical cubic saving or RH is claimed.

The earlier Lean certificate of this lane is `../bag-rational-numerator-cofactors.md` (stage 3, flat folder).

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
