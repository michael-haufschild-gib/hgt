# Finite-packet Schwarz-doubled positive quartic realification

- **ID:** `finite-packet-schwarz-doubled-positive-quartic-realification`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Route:** GTA (`ORIENT` finite spectral assembly)
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`

## Goal

Assemble the local `(7,5)` positive quartic lift over an arbitrary finite complex spectral packet
without choosing representatives of conjugate pairs. Obtain a reporter invariant under relabeling
and Schwarz conjugation, unlike the formally excluded entrywise matrix reporter.

## Gates

- [x] 0 → 1 in-progress: packet, exact invariants, falsifiers, and parent corpus fixed
- [x] 1 → 2 fully-proven: dependency-closed finite-sum proof
- [x] 2 → 3 formalized: exact Lean theorem and audit

## Parent corpus

- `[LEAN-PROVED]` One conjugate source pair has a `(7,5)` lift preserving traces one/two with
  quartic charge `100b²(6a²+23b²)`, zero iff `b=0`.
- `[LEAN-PROVED]` Entrywise matrix aggregation is not a real-divisor reporter.
- `[LEAN-PROVED]` Actual theta-stage Hermite trace positivity is equivalent to real divisor and RH
  cofinally, so the missing assembly must be spectral/similarity-invariant.
- `[LEAN-PROVED]` Schur triangulation exposes a finite characteristic-node packet for every stage.

## Frozen conjecture

Let `ι` be finite and `z : ι → ℂ`. For each `i`, apply the positive local lift to the Schwarz pair
`zᵢ, conj(zᵢ)`, with `aᵢ=Re zᵢ`, `bᵢ=Im zᵢ`. Sum the local even, odd, and Schwarz-pair moments.
Let `D_n(z)` be total even moment minus total odd moment minus total Schwarz-doubled source moment,
and let

`Q(z)=Σᵢ 100(Im zᵢ)²(6(Re zᵢ)²+23(Im zᵢ)²)`.

Then:

1. `D₁(z)=D₂(z)=0`.
2. `D₄(z)=Q(z)`.
3. `Q(z)≥0`, and `Q(z)=0` iff every `zᵢ` is real.
4. `Q` is invariant under pointwise Schwarz conjugation.
5. `Q` and every `D_n` are invariant under arbitrary finite reindexing.

Thus one positive quartic supertrace detects realness of a complete finite spectral packet, without
pair selection and without referring to matrix entries.

## Hostile attacks

- Empty packet and singleton nonreal packet.
- Packet not initially closed under conjugation: Schwarz doubling must remain exact.
- Duplicate roots and arbitrary relabelings.
- Pointwise conjugation must flip each imaginary coordinate but preserve charge.
- Do not claim source-side vanishing or actual theta-stage real divisor from construction alone.

## Dependency-closed proof

For each index `i`, the local `(7,5)` theorem gives anomalies `A₁ᵢ=A₂ᵢ=0` and

`A₄ᵢ=100(Im zᵢ)²(6(Re zᵢ)²+23(Im zᵢ)²)`.

Finite-sum distributivity identifies the packet anomaly with `Σᵢ A_nᵢ`. This proves degrees one,
two, and four. Every quartic summand is nonnegative. If their finite sum vanishes, finite-sum
rigidity forces each summand to vanish; local faithfulness then gives `Im zᵢ=0` for every `i`.
The converse follows termwise. Hence the packet charge is strictly positive exactly when some
packet node is nonreal.

Schwarz conjugation fixes each real coordinate and negates each imaginary coordinate. Local even,
odd, and source-pair moments are unchanged because their two signed nodes swap; the charge is
unchanged because it contains only even powers of the imaginary coordinate. Summing proves
all-degree Schwarz invariance. For an equivalence of finite index types, change of variables in the
finite sum proves invariance of every anomaly and the charge. Empty packets, duplicates, and
packets not initially closed under conjugation require no separate case.

## Novelty audit

- Exact corpus searches returned only local source-pair realification, entrywise no-go, and abstract
  all-degree graded locks; no finite-packet positive quartic assembly was found.
- Exact current web searches found no matching arXiv construction. Priority remains unverified.

## Open core

`[OPEN CORE]` Remaining GTA burden becomes one scalar source-side vanishing law for the Schur
packet charge, plus the exact Schur-to-actual-theta-stage transport.

## Log

- 2026-08-27 — frozen from corpus local classification plus entrywise obstruction.
- 2026-08-27 — dependency-closed finite-sum proof completed; scratch Lean closes exact statement.
- 2026-08-27 — formalized in `FinitePacketSchwarzDoubledPositiveQuarticRealification.lean`;
  direct Lean, targeted module build, formal lint, and axiom audit passed. Axiom footprint is only
  `propext`, `Classical.choice`, and `Quot.sound`.
