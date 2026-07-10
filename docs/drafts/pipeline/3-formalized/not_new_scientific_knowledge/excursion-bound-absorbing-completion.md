# Absorbing completion discharges finite excursion bounds

- **ID:** excursion-bound-absorbing-completion
- **Stage:** 3-formalized
- **Type:** NOT-NEW / INTERFACE DISCHARGE
- **Source:** RHTower `RelayLedger`
- **Statement:** `[PROVED]` If a finite signed-depth walk is nonpositive at its terminal index, it satisfies `ExcursionBound` with budget equal to the list length. Appending the single compensating push that makes terminal depth zero therefore gives an unconditional `ExcursionBound` provider for every finite push list.

## Goal

Replace the abstract finite-walk ephemerality Prop by a checkable terminal condition, then construct
that condition canonically with one absorbing push.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: focused build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: not intended; interface discharge only

## Approach

An upcrossing at `m` has positive depth at `m+1`.  If terminal depth is nonpositive, then
`m+1 < pushes.length`; choose `j = pushes.length-(m+1)`.  This is positive, lies within the list
length, and lands exactly at the terminal index.  For an arbitrary list, append the negative of
its final depth; the completed walk ends at zero and the preceding theorem applies.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/ExcursionBoundDischarge.lean`
- High-level consumers: `formal/GaloisForLFunctions/RHTower/ExcursionConsumerDischarge.lean`
- Terminal reduction: `excursionBound_of_terminal_nonpos`
- Unconditional provider: `absorbingCompletion_excursionBound_length_succ`
- Direct consumers: `run_bounded_absorbingCompletion`,
  `exists_upcross_chain_absorbingCompletion`,
  `card_upcross_ge_of_spread_absorbingCompletion`,
  `spread_lt_of_upcross_budget_absorbingCompletion`,
  `spread_lt_of_upcross_selected_kernel_absorbingCompletion`, and
  `spread_lt_of_upcross_thick_kernel_absorbingCompletion`
- Build: `lake build GaloisForLFunctions.RHTower.ExcursionConsumerDischarge` PASS
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
