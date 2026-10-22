# HB source FE cocycle versus fixed-pairing rigidity

## Status

Formalized. HC50. Dependency-closed paper proof and Lean proof complete.

## Route

HB, with interfaces to the FZZ-P/RBH/PW-B shared Ward producer.

## Corpus basis

- `ThetaCuspHawkingBMPhaseSensitiveChiralWardAmplitude.lean` identifies the literal polarized BM source amplitude with a nonzero physical multiplier times the Deninger Ward charge.
- `ThetaCuspHawkingBMCanonicalSchwarzTransportExtinctionClassification.lean` proves ordinary semilinear Schwarz transport is unconditional; the older same-channel equality is source extinction, hence RH.
- `ReflectionCocycleCurvature.lean` proves carrier-ratio reflection cocycles are involutive away from zeros.
- `SourceHorizontalGammaSixRelativeReflectionFraming.lean` separates transported reflection from fixed-framing compatibility: transported involution is automatic, while fixed-frame mismatch retains curvature.
- `DeningerDivisorGaugeWardIdentity.lean` supplies the anti-linear divisor FE reindexing and its exact horizontal Ward defect.

Mandatory corpus searches:

- `HB Peierls FE reindexing cocycle source amplitude reflection transport diagonal cocycle Schwarz`
- `Deninger reflect gauge cocycle countertransport commutation defect source marked Ward Peierls`
- `quadratic carrier reflection ratio polarized source amplitude reflect ratio cocycle involution`

## Hard conjecture HC50

Fix the canonical unit Einstein seed and let `a(q)` be its literal BM polarized source amplitude.
Let `R q` be the xi-zero-copy reflection. Define the canonical source FE cocycle by

`κ(q) = 1` when `a(q) = 0`, and otherwise

`κ(q) = a(R q) / conj(a(q))`.

This is the source-faithful anti-linear FE transport within one channel. Composing it with the
already-formal anti-linear channel Schwarz exchange gives the corresponding linear transport into
the opposite channel. The initially considered direct opposite-channel ratio
`conj(a(R q))/conj(a(q))` fails the automatic anti-linear cocycle cancellation and was rejected.

Conjecture:

1. `κ(q) * conj(a(q)) = a(R q)` for every xi-zero copy.
2. `κ(R q) * conj(κ(q)) = 1`; the source-derived anti-linear transport is involutive.
3. Away from the critical line, source compatibility uniquely determines `κ(q)`.
4. Requiring this source-derived transport also to preserve the fixed bilinear Peierls pairing forces critical-line rigidity. Equivalently, its scalar fixed-pairing condition `κ(q)^2 = 1` holds exactly when `re(q.1) = 1/2`.
5. Universal fixed-pairing compatibility is equivalent to RH.

The intended positive survivor is a classification, not a bound: literal FE source transport always exists and is involutive, but preservation of the untransported Peierls pairing is precisely the missing Ward/RH content.

## Proof attack

Off the wall the source is nonzero, so cocycle identities reduce by field cancellation. The helicity mixing factor is reflection-invariant, nonzero, and pure imaginary. The remaining unit-seed carrier is

`s^2 * (s + 2) / 8`.

The condition `κ^2 = 1` gives `κ = 1` or `κ = -1`. Source compatibility, together with the
pure-imaginary reflection-invariant helicity mixing factor, then gives either

- `f(1-s) = f(conj(s))`; factorization plus nonzero Xi height forces `2 re(s)-1 = 0`, or
- `f(1-s) = -f(conj(s))`; its real and imaginary parts contradict `0 < re(s) < 1` off wall.

Thus fixed-pairing compatibility forces the critical line in both branches.

## Novelty audit

Bounded literature search through 2026-08-28 found work on reflected/CPT bilinear products for black-hole quasinormal modes and general covariant/Peierls brackets, but no theorem classifying a literal BM source-derived FE cocycle against a fixed Peierls pairing, nor the proposed equivalence with critical-line support. Relevant primary sources inspected: arXiv:2604.13182, arXiv:2210.15935, arXiv:1402.1282, hep-th/9308150.

## Acceptance gate

- Dependency-closed paper proof or closed Lean obstruction.
- Unconditional public Lean theorems; no new axioms, `sorry`, `admit`, `opaque`, or `unsafe` declarations.
- Direct `lake env lean` check, target-only `lake build`, axiom audit, lint, umbrella wiring.

## Result

Formal module:

`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFECocycleFixedPairingRigidity`

The conjecturing loop rejected the first direct opposite-channel ratio because conjugation prevents
the anti-linear cocycle from telescoping. The corrected corpus-native FE ratio is the unique
source-faithful coefficient off wall. Lean proves:

1. exact literal-source transport on every Xi fibre;
2. compatibility classification: arbitrary scalar transport is possible precisely at source
   extinction, and otherwise equals the canonical cocycle;
3. anti-linear reflection involution unconditionally;
4. the cocycle-square/fixed-bilinear-pairing condition is equivalent to critical-line support;
5. actual fixed `hbXiPeierlsDot` preservation on every basis fibre is equivalent to RH globally.

The positive survivor closes a proof-burden distinction: FE transport and transported-form
compatibility need no RH input. The nontrivial HB producer must identify transported Peierls form
with fixed physical Peierls form; that identification is already an exact RH receiver.

## Formal audit

- Direct `lake env lean` elaboration: passed.
- Target-only build: `11918/11918`, passed.
- Public theorem axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import: wired into `GaloisForLFunctions.RHTower`.
- Formal lint: no HC50 issue; repository-wide lint remains red only on unrelated pre-existing
  unreachable modules.
