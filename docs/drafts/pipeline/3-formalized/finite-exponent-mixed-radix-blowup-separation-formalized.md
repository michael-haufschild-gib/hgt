# Finite-exponent mixed-radix blow-up separation — Lean certificate

- **ID:** `finite-exponent-mixed-radix-blowup-separation-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `finite-exponent-mixed-radix-blowup-separation.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/MultiJetBlowUpSeparation.lean`, imported by
`GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. `finiteExponentDigitBase` — the radix `2 + ∑_a ∑_k e a k`, strictly above every coordinate
   (`exponent_coordinate_lt_finiteExponentDigitBase`) and above `1`.
2. `mixedRadixBlowUpRate` — its powers, one per coordinate.
3. `blowUpOrder_mixedRadix_injective` — those weights separate every injectively indexed finite
   exponent family, by uniqueness of fixed-length base-`B` expansion.
4. `exists_blowUpRate_injective` — the card's statement: for every injective
   `e : κ → (Fin n →₀ ℕ)` with `κ` finite there is `d : Fin n → ℕ` making
   `a ↦ ∑ k, e a k · d k` injective.
5. `exists_periodicPolePower_row_packet` — the downstream use: an unconditional full-rank row
   packet for every finite family of distinct monomials, realized by powers of the periodic pole
   model, with the combinatorial rate premise of the multi-jet blow-up theorem discharged.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/MultiJetBlowUpSeparation.lean` — clean.
- `#print axioms` on 3, 4 and 5: `[propext, Classical.choice, Quot.sound]` only.
