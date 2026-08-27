# Theta-source Schur quartic charge flag

- **ID:** `theta-source-schur-quartic-charge-flag`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Route:** GTA (`ORIENT` actual finite-stage transport)
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`

## Goal

Transport finite-packet positive quartic charge to every Schur packet of each actual signed theta
source matrix. Prove zero charge is exactly existing Hermite/Green/real-divisor stage property.

## Gates

- [x] 0 → 1 in-progress: stage reporter, equivalences, falsifiers, and corpus dependencies fixed
- [x] 1 → 2 fully-proven: dependency-closed Schur/Hermite proof
- [x] 2 → 3 formalized: exact Lean theorem, targeted build, lint, and axiom audit

## Parent corpus

- `[LEAN-PROVED]` Every finite complex matrix admits unitary Schur triangulation.
- `[LEAN-PROVED]` Actual theta-stage Hermite positivity is equivalent to stage real divisor and
  modewise Green neutrality.
- `[LEAN-PROVED]` Hermite form equals sum of squares evaluated on Schur diagonal nodes.
- `[LEAN-PROVED]` Finite-packet quartic charge is nonnegative and vanishes exactly when all packet
  nodes are real; it is relabel invariant.

## Frozen conjecture

Fix actual theta stage `k` and any Schur data `U,T` for its finite matrix. Define

`Q_k(T)=Σ_i 100(Im T_ii)²(6(Re T_ii)²+23(Im T_ii)²)`.

Then:

1. `Q_k(T)=0` iff theta stage `k` has universal arithmetic Hermite positivity.
2. Equivalently, `Q_k(T)=0` iff stage `k` has real ordinary divisor.
3. Equivalently, `Q_k(T)=0` iff stage `k` has exact modewise Green neutrality.
4. Global vanishing for every stage and every Schur packet is equivalent to existing Hermite,
   Green, and all-stage real-divisor flags, hence implies RH.

The equivalence must be independent of which Schur triangularization is chosen.

## Hostile attacks

- Repeated eigenvalues and nonunique Schur bases.
- Non-normal actual source matrices: use only triangular diagonal and trace identity.
- Both unitary identities are retained exactly as required by corpus Schur theorems.
- Reporter is a consumer: do not assume or claim unconditional global vanishing.

## Dependency-closed proof

Fix Schur data `U,T`. If `Q_k(T)=0`, finite-packet faithfulness gives `Im T_ii=0` for every
diagonal node. Existing Schur trace identity rewrites each real-polynomial Hermite form as

`Σ_i p(T_ii)²`.

Every `T_ii` is real, so this is a sum of nonnegative real squares. Hence stage Hermite positivity
holds. Conversely, existing finite-matrix Hermite--Sylvester converse applied to the same Schur
data forces `Im T_ii=0` from stage Hermite positivity; packet faithfulness gives `Q_k(T)=0`.

Public stage theorems identify Hermite positivity with ordinary real divisor and Green neutrality,
proving all three equivalences. Every finite matrix has at least one Schur packet. Therefore:

- global charge vanishing implies Hermite flag by choosing one packet per stage;
- Hermite flag implies charge vanishing for every packet by the stagewise equivalence.

This proves exact global flag equality, independent of Schur choices. Existing Green/all-stage
real-divisor equivalences and RH consumer finish the transport.

## Novelty audit

- Corpus searches found Schur/Hermite equivalence and unrelated Schur packet charges, but no
  positive quartic scalarization of actual theta stages.
- Exact current arXiv searches found no matching construction. Priority remains unverified.

## Open core

`[OPEN CORE]` Prove global charge vanishing from a prime/Gamma/theta arithmetic selection law.
The current four-field approximation property is insufficient, as the separately formalized
admissible-stage nonselection theorem shows.

## Log

- 2026-08-27 — frozen from finite-packet realification and existing theta Hermite flag.
- 2026-08-27 — dependency-closed Schur/Hermite proof completed; exact scratch Lean passed.
- 2026-08-27 — stagewise/global equivalences and RH consumer formalized in
  `HedenmalmThetaSchurQuarticChargeFlag`; targeted build, formal lint, and axiom audit passed.
