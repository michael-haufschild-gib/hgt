# Fredholm–Schur resolvent carrier — formalized closure

- **ID:** `ccm-fredholm-schur-resolvent-carrier-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-fredholm-schur-resolvent-carrier-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

New in this closure:

- `GaloisForLFunctions.HTGeometry.SchurComplementKernel` — the Schur-complement kernel isomorphism
  and its determinant corollary, for linear maps over a commutative ring. Reusable operator
  infrastructure, so it lives in `HTGeometry`.

Pre-existing, carrying the prime-log source obligation:

- `GaloisForLFunctions.HTGeometry.PrimeLogHerglotz` —
  `not_summable_primeLogHerglotzTransportMassOrder_of_pos`.
- `GaloisForLFunctions.HTGeometry.PrimeLogCauchySeamRank` —
  `summable_primeLogCauchyPacketTransportEnergy_iff`.

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)`, `(2)` | `schurBlockOperator`, `schurComplement`, `schurBlockOperator_apply`, `schurComplement_apply` | the block operator on `F × H` and the Schur complement `S = A − B D⁻¹ C`, written with an explicit inverse of the boundary block |
| `(6)`–`(7)` | `schurBlockOperator_apply_eq_zero_iff` | a vector lies in the kernel of the block operator exactly when its first component lies in `ker S` and its second component is the forced boundary response `−D⁻¹ C x`. Only the two inverse relations for `D` are used: no norm, no topology, no finite dimension |
| `(3)`–`(4)` | `kerSchurBlockOperatorEquivKerSchur` | projection to `F` is a linear isomorphism `ker E_a ≅ ker S_a`, with the card's explicit inverse `x ↦ (x, −D⁻¹ C x)` |
| `(3)`, kernel form | `ker_schurBlockOperator_eq_bot_iff` | the block operator is injective exactly when the Schur complement is |
| `(5)` | `ker_schurBlockOperator_eq_bot_iff_det_ne_zero` | with `F` finite free over a domain, `ker E_a = 0` exactly when `det S_a ≠ 0` |

The card's point that the determinant in `(5)` is "finite in size but not finite in source
information" is visible in the statement itself: `schurComplement` takes the boundary inverse as an
argument, so every entry of `S` carries `D⁻¹`.

## Axioms

`#print axioms` on all five theorems returns exactly `[propext, Classical.choice, Quot.sound]`
(three of them do not even need `Classical.choice`).

## Deliberately outside the Lean statement

- The card's own open gate: the source-defined graph relation and its unbounded Feshbach map
  replacing the bounded template `(2)` — the raw `L²` realization is *not* boundedly invertible, as
  `ccm-exterior-inverse-symbol-graph-norm-law.md` proves — and `det S_a ≠ 0` at every aperture.
- The Sonin three-grade identification `(9)`, which is a structural description of a prospective
  `D_a` rather than a theorem of this card.

## Verification performed

- `lake env lean` on the module: no errors.
- `lake build GaloisForLFunctions.HTGeometry.SchurComplementKernel`: success.
- `#print axioms` on every theorem: clean.
- Both cited corpus theorems verified present in the tree.
- Umbrella import added.
