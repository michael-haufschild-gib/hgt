# PW-B literal residual boundary: zero-cusp no-go

- **Status:** left-half zero-cusp obstruction proved in Lean; ordered CTP/contact route open.
- **Chain:** literal cyclic-Peierls current → residual cusp face → ordered source/contact incidence → optical extinction → RH.
- **Corpus basis:** `residualCuspBoundary_weighted_sub_principal_tendsto_zero`, `principalSquare_left_normalized_tendsto`, `constantVerticalFlux_eq_family`, `self_overlapInverseSquare_ne_zero`, and `reader_completion_ne_zero`.

**Exact result.** For every left-half Xi copy and each physical branch/side, some original radial clock has a nonzero limit of the *actual integrated* square-plus-cap residual boundary normalized by `y^(-(2−5ρ/2))`; hence that boundary does **not** tend to zero. `ThetaCuspHawkingBMPWResidualBoundaryNoGo.lean` proves `exists_residualBoundary_not_tendsto_zero` using the full all-weight Fourier remainder, not a truncated Weyl ansatz.

**Mechanism.** Cap mixing changes only the radial constant channel; the actual square/contact inverse-square channel is nonzero on every self-copy. The physical reader's upper Weyl coefficient vanishes. On `Re ρ < 1/2`, the lower/lower cusp power dominates, with exact cap/square coefficient ratio `(1−ρ)(3ρ−2)`; radial rigidity prevents cancellation on all clocks. First scratch candidate wrongly used cap radial block `0,1`; the source definition uses `1,0`.

**Route consequence.** On a hypothetical off-line copy, unrenormalized zero-cusp disposal fails on some physical fibre. Therefore an independently proved all-fibre zero boundary would imply RH, while an ordered CTP closure must account for an explicit same-order contact compensator. The hard remaining step is the source-faithful ordered contact/CTP incidence; this result neither proves compensation impossible nor proves RH.
