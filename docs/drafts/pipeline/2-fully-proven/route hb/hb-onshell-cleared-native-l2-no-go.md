# On-shell cleared native radial L2 no-go

- **ID:** hb-onshell-cleared-native-l2-no-go
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/rh-current-frontier-map.md · HB literal cyclic Peierls realization
- **Statement:** For every `XiZeroCopy q` and branch, the unit-amplitude literal cleared native reduced coefficient at `w = 2 * physicalRate q branch` is not in `L²(volume.restrict (Iio 0))`.

## Goal

Kill the Hilbert-space version of the remaining HB realization edge. This does not address a distributional/action realization with the compulsory pole cochain.

## Gates

- [x] 1 → 2 fully-proven: exact source identities give the horizon factor and a dependency-closed paper proof.
- [ ] 2 → 3 formalized: source theorem awaits the missing transitive `.olean`; generic negative-ray exclusion is formalized as `not_memLp_two_restrict_Iio_of_atBot_norm_ge_one`.
- [ ] 3 → 4 publication-ready: external novelty audit and a standalone note.

## Proof

Write `s = physicalRate q branch`, `r(t) = radialUnit t`, and take source amplitude `a = 1`.
`clearedOnset_source_rate` gives `clearedOnset s (2s) = 1`. The exact
`reducedCoefficient_frequency_horizon` identity therefore gives

`clearedReducedCoefficient s 1 (2s) t = exp ((2s + 2)t) * H_s(r(t))`,

where `H_s(u) = sourceHorizonProfile s 1 0 u + (2s) * sourceHorizonProfile s 1 1 u`.
Expanding the displayed source definitions at `u = 1` gives the exact cancellation-free value

`H_s(1) = -8 * power (2s) 2 * (s + 1) * (2s + 1)`.

`physicalRate_re_bounds` has `Re s < -2`; consequently every displayed factor is nonzero and
`Re (2s + 2) < 0`. Since `r(t) → 1` as `t → -∞`, continuity gives `H_s(r(t))` bounded away from zero eventually. The exponential factor has norm `exp ((Re (2s + 2)) t) → +∞`; hence the coefficient has norm eventually at least one. The formal generic negative-ray theorem then excludes its membership in native radial `L²`.

## No-go closure

- **Exact killing theorem/mechanism:** the cleared numerator remains entire pointwise, but its literal on-shell radial coefficient has a nonzero horizon profile multiplied by a growing negative-ray exponential; it cannot be an `L²` causal source.
- **Strongest positive survivor:** the exact nonzero factor `-8 * power (2s) 2 * (s + 1) * (2s + 1)` is the compulsory horizon boundary datum.
- **New insight:** any surviving cyclic Peierls realization must be boundary/distributional and transport this datum together with the pole residue and explicit wave cochain; a native Hilbert-space source realization is excluded.
- **Status:** paper proof above; generic `L²` exclusion Lean-checked and standard-axiom audited. Literal source instantiation is pending only source-import closure, not an unproved mathematical premise.

## Log

- 2026-09-16 — paper proof isolated from corpus identities; generic negative-ray exclusion formalized.
