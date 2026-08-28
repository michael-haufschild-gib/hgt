# JAS prime-support unitary obstruction

- **ID:** JAS-PSUO-1
- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL THEOREM / HARD ROUTE-CLASS FALSIFIER
- **Source:** read-only `rh-current-frontier-map.md`, surviving prime-support-synchronized
  `C(PrimeTorus)` sewing burden

## Hard frontier target

The remaining JAS mechanism must couple prime support to the completed-theta grade chain. The most
direct realization sends a prime-torus coordinate character to the actual RFHM Gamma insertion
operator. That insertion remembers native support by a proper projection and advances reversible
coefficient history.

Test whether this is compatible with source multiplication at all. Every coordinate character of
`C(PrimeTorus)` is a unit. A unital multiplicative operator representation must therefore send it
to a surjective invertible operator. An RFHM packet with proper native support is only a partial
isometry and should fail surjectivity.

## Corpus basis

All conjecture-forming search used `scripts/formal_tools.py research`. Corpus provides:

- `torusCharacter` and its exact additive/multiplicative character law;
- faithful RFHM `RestrictionPacket.packetOperator` on `ell²(E × G)`;
- exact packet composition and partial-isometry identities;
- actual arithmetic `jasGammaInsertionPacket`, whose support is the complement of one prime;
- no classification of surjective JAS packet operators and no obstruction to realizing an actual
  Gamma insertion as a prime-torus coordinate.

## Conjecture loop

### C1 — exact RFHM unit classification

For a JAS restriction packet, its canonical operator is surjective exactly when native support is
all primes. Proper support creates a missing Hilbert coordinate independently of reversible grade.

### C2 — actual insertion is non-surjective

Every `jasGammaInsertionPacket x p P` has proper support and hence is not surjective, for arbitrary
aperture, inserted prime, and prior support.

### C3 — closed source-algebra no-go

There is no unital multiplicative map from `C(PrimeTorus)` to bounded operators on the JAS packet
Hilbert space that sends even one prime coordinate character to its actual Gamma insertion packet
operator. State this as one closed negated existential with no hypotheses.

## Positive survivor sought

Classify exactly what survives: only support-free reversible packets can represent source units.
Native support insertion must instead occur through a Toeplitz compression, correspondence,
crossed-product corner, or bilateral group completion; it cannot be the `C(PrimeTorus)` action
itself.

## Hostile falsification

1. Arbitrary aperture, inserted prime, prior support, and reversible grade.
2. Assume only unitality and multiplicativity—no continuity, linearity, star preservation, or RH.
3. Use actual corpus RFHM packet operator, not an abstract shift surrogate.
4. Prove exact positive unit classification before retiring the mechanism.

## Novelty status

`[PROVED IN LEAN] [CORPUS-NOVEL ROUTE THEOREM] [TARGETED EXTERNAL NO-MATCH]`

Generic ingredients are not claimed novel: units map to units under unital multiplicative maps;
proper support projections yield partial isometries; Toeplitz compression and inverse-semigroup
representations are established subjects. Targeted literature search found those general theories
but no prior theorem for the corpus-native RFHM Gamma insertion, prime-torus character source, and
JAS synchronized-sewing burden. Novel claim is restricted to the exact unit classification and its
closed route-level consequence.

## Formal result

Module:

- `formal/GaloisForLFunctions/RHTower/JointAncestryPrimeSupportUnitaryObstruction.lean`

Theorems:

- `jasPacketOperator_surjective_iff_support_eq_univ`: exact classification of canonical arithmetic
  RFHM packet units—surjectivity holds exactly at full native support;
- `jasGammaInsertionPacket_operator_not_surjective`: every actual Gamma insertion is
  non-surjective for arbitrary aperture, prime, and prior support;
- `not_JASPrimeSupportCoordinateRaisingRepresentation`: closed negated existential ruling out any
  unital multiplicative `C(PrimeTorus)` operator action that sends a coordinate character to an
  actual Gamma insertion.

C1--C3 are proved without weakening. C3 assumes less than planned: no linearity, boundedness of the
representation as a function, continuity, or star preservation is needed.

## RH-route consequence

The direct prime-support-synchronized JAS construction is terminal. Native Gamma insertion cannot
be the source-algebra action: a torus character has an inverse, whereas the actual RFHM insertion
erases a Hilbert coordinate through its proper support projection.

Positive survivor is exact. Support-free reversible packets—the existing BV--Wold history
sector—are the only canonical RFHM packets eligible to represent source units. Prime support must
enter through a nonmultiplicative Toeplitz compression, correspondence/corner, or a bilateral group
completion that restores the missing inverse. Any next JAS conjecture must build and test one of
those structures rather than repeat direct coordinate raising.

## Verification

- Direct `lake env lean` check passed.
- Exact leaf `lake build GaloisForLFunctions.RHTower.JointAncestryPrimeSupportUnitaryObstruction`
  passed; no umbrella or full build was run.
- Module wired into `GaloisForLFunctions.RHTower` umbrella.
- Axiom probes for all three public theorems report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Formal lint reported no error in the new module; repository-wide failure consists only of
  unrelated concurrently unwired modules.
- No RH premise, Xi-zero premise, finite computation, numerical bound optimization, or added axiom.

## Log

- 2026-08-28 — selected after arbitrary phase/history dependent-sum sewing was proved terminal.
  Frontier map remained read-only.
- 2026-08-28 — C1--C3 proved in Lean. Direct coordinate-raising route retired; exact
  support-free/bilateral survivor retained.
