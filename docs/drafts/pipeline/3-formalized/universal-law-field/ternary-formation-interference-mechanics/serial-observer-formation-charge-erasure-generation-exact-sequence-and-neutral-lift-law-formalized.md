# Serial observer formation charge — Lean certification

- **ID:** ULF-TFIM-2
- **Paper card:** `serial-observer-formation-charge-erasure-generation-exact-sequence-and-neutral-lift-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.SerialObserverFormationCharge`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## Reusable infrastructure

`subQuotMap` — a linear map carrying one nested pair of submodules into another induces a map of
subquotients `N/D → N'/D'`; `subQuotMap_mk` computes it on classes and `finrank_subQuot` gives
`dim (N/D) + dim D = dim N`.  `subQuot_forall_eq_zero_iff` characterises triviality as `N ≤ D`.

## Certified declarations

### §1 setup

`overlapNum L A B = L A ⊓ L B`, `overlapDen L A B = L (A ⊓ B)` with `overlapDen_le`, and
`ObserverOverlap L A B` is the subquotient `(SOF.2)`.  `erasureNum`/`erasureDen`/`ErasedCharge`
are `(SOF.5)`.  Supporting: `map_overlapNum_le`, `map_overlapDen_eq`, `overlapNum_comp_eq`,
`overlapDen_comp_le`.

### Theorem 2.1 `(SOF.6)`–`(SOF.7)`

The three maps are `erasedToOverlap`, `overlapPush`, `overlapProject` (with the `_mk` computation
lemmas), and exactness is

* `erasedToOverlap_injective`;
* `range_erasedToOverlap` — `im ι = ker M_*`, the `(SOF.11)` computation;
* `range_overlapPush` — `im M_* = ker π`;
* `overlapProject_surjective`;

bundled as `serialObserver_exact`.

### §3 the exact charge budget

* `overlapRank`, `erasedRank`, `overlapRank_add_finrank`, `erasedRank_add_finrank`,
  `overlapRank_eq_zero_of_le`, `erasedRank_eq_zero_of_le`;
* `overlapRank_comp` — **Corollary 3.1 `(SOF.14)`**: `o_{ML} = o_L − e_M + o_M`, from
  rank–nullity applied to `M_*` and `π` plus injectivity of `ι`;
* `overlapRank_eq_slack` — **`(SOF.15)`**: the overlap rank *is* the submodularity slack of the
  observed rank function;
* `slack_chain_rule` — **`(SOF.16)`**, the serial chain rule for that slack.

### §4 neutrality classification

* `overlapPush_injective_iff` — injectivity ⟺ `(SOF.18a)`, no upstream charge erased;
* `overlapPush_surjective_iff` — surjectivity ⟺ `(SOF.18b)`, no downstream charge created;
* `overlapPush_bijective_iff` — **Theorem 4.1 `(SOF.18)`**;
* `overlapPush_bijective_of_disjoint` — **Corollary 4.2 `(SOF.19)`**: a downstream observer whose
  kernel meets `L A + L B` trivially transports charge information-neutrally;
* `overlap_comp_trivial_iff` — **Corollary 4.3 `(SOF.20)`**: the composite charge vanishes exactly
  when no downstream charge is created and every upstream class is erased.

### §5 dual reporter sequence

`serialObserver_dual_exact` — **Theorem 5.1 `(SOF.21)`**, obtained from the primal exactness by
`LinearMap.range_dualMap_eq_dualAnnihilator_ker` and
`LinearMap.ker_dualMap_eq_dualAnnihilator_range`, with the two endpoints from
`dualMap_injective_of_surjective` and `dualMap_surjective_of_injective`.

### §7 sharp countermodels

`diagLine`, `axisLine` are the two distinct lines of `k × k`; `diagLine_inf_axisLine`,
`span_one_eq_top`, `map_snd_diagLine`, `map_snd_axisLine` and `overlapRank_snd_lines` (the
second-coordinate observer creates exactly one unit of charge) support

* `countermodel_neutral_transport` — `(SOF.23)`: `1 = 1 − 0 + 0`;
* `countermodel_pure_erasure` — `(SOF.24)`: `0 = 1 − 1 + 0`;
* `countermodel_pure_generation` — `(SOF.25)`: `1 = 0 − 0 + 1`.

Together they prove preservation, erasure and generation are logically independent, so no scalar
monotone data-processing law can replace `(SOF.14)`.

### §8 arbitrary serial chains

Reusing `transport`/`totalTransport` from
`GaloisForLFunctions.HTGeometry.FiniteLawHistoryMachine`:

* `overlapRank_id`, `overlapRank_id_eq_zero`;
* `serial_telescoping` — **Theorem 8.1 `(SOF.28)`**;
* `overlapRank_comp_of_bijective` and `overlapRank_stable_of_neutral` — **Corollary 8.2
  `(SOF.29)`**: a tower of neutral stages cannot change formation charge.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/SerialObserverFormationCharge.lean
```

Elaborates with no errors and no warnings.  `#print axioms` on all 65 public declarations reports
only `propext`, `Classical.choice`, `Quot.sound`.  The module is imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField` and by `GaloisForLFunctions.HTGeometry`.

## Still open (not a proved theorem)

Gate 3 → 4 of the card: a literal arithmetic serial-observer realization.  The card states this as
a construction burden, not a theorem.
