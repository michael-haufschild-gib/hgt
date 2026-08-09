# Route E block-defect energy reduction — formalized closure

- **ID:** `route-e-block-defect-energy-reduction-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./route-e-block-defect-energy-reduction.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NO RH INPUT]`

## Lean modules

- `GaloisForLFunctions.RHTower.MobiusBlockDefectCompression`
- `GaloisForLFunctions.RHTower.MobiusBlockDefectEnergy`

Umbrella: `GaloisForLFunctions.RHTower`.

## Formal theorem chain

1. `abs_exp_neg_mul_sub_blockRepresentative_le` — the pointwise cost `|e^{-xn} − e^{-xξ}| ≤ xh e^{-xξ}`
   of moving one exponential atom to its block representative.
2. `norm_sum_atom_sub_blockRepresentative_le` — its summed complex form for coefficients of norm
   at most one.
3. `sum_atom_eq_sum_blockDefect_mul_weight` — the exact fiber regrouping of a
   representative-weighted atom sum into the signed block-defect current.
4. `norm_atom_sum_sub_blockDefectCurrent_le` — equation `(1)`.
5. `sum_range_mul_eq_prefix_last_add_sum_prefix_mul_sub` — the exact discrete Abel identity `(2)`.
6. `abs_sum_range_mul_le_endpoint_add_prefixEnergy` — the Cauchy–Schwarz form `(3)`.
7. `sum_exp_blockWeightGradient_sq_le` — the squared-gradient budget `(4)`.
8. `sum_range_mul_eq_sum_prefix_mul_sub_of_total_eq_zero` — the endpoint-free identity `(4a)`
   for a zero-total extended current, and
   `abs_sum_range_mul_le_prefixEnergy_of_total_eq_zero` its quadratic bound.
9. `abs_exp_blockDefectCurrent_le_endpoint_add_prefixEnergy` and
   `abs_exp_zeroTotalSectorFluxCurrent_le_prefixEnergy` — the Gibbs and sector-flux
   specializations.
10. `twoPhase_zeroTotal`, `twoPhase_geometricCurrent_transfer` — the hostile two-phase transfer law
    `S_m(r)(1−r) = A(1−r^m)²` that rules out deducing `(6)` from small individual defects.
11. `geometricDefectMode_zeroTotal`, `geometricDefectMode_weighted_transfer` — the exact transfer
    of one complex defect frequency against a geometric Gibbs mesh.

## Verification

- `lake env lean` clean, no warnings, on both modules.
- `lake build GaloisForLFunctions.RHTower.MobiusBlockDefectEnergy` — green.
- `#print axioms` on all thirteen statements: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella imports present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

The card does not prove `(6)`; Route E remains open. That is a research gate on the parent card
`../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`, not formalization debt here.
