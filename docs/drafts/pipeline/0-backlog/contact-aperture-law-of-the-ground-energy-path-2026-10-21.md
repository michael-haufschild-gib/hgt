# The contact law of the ground-energy path

- **ID:** `contact-aperture-law-of-the-ground-energy-path-2026-10-21`
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-2110/route-unification-ledger.md` (the unifying object);
  `Q:TheContactApertureOfTheGroundEnergyPath`, `Q:DilutedOffLineLatticeHidingLaw`,
  `Q:NearTopZerosForceNegativeGroundEnergyBeyondAnExplicitAperture`
- **Statement:** off RH, the contact aperture `A_c = sSup {A : μ(A) ≥ 0}` of the restricted Weil
  ground-energy path is determined by the top zero: with `δ = zetaZeroWidth` and `γ*` the least
  ordinate of a zero of depth within `1/A_c` of `δ`, there are absolute constants with
  `c · log log γ* / δ ≤ A_c ≤ C · (log γ*)² log log γ* / δ`, and the lower bound is sharp up to
  the constant.

## Goal
The ground-energy path `A ↦ μ(A)` carries the three units of the route clusters: its first sign
change is the aperture unit (positivity routes), the rate of its fall is the width (prime-side and
zero-side routes), and the zero forcing the sign change is the top zero (zero-indexed routes). The
corpus proves the upper bound in explicit form (`zetaContactAperture_le_of_near_top_zero`:
`A_c ≤ V/2 + w` with `V = oneParamLag w η (Re z₀)`, polylogarithmic in the height and inverse in
the depth) and proves the lower bound's mechanism in the synthetic diluted-lattice model
(`Q:DilutedOffLineLatticeHidingLaw`: inside an on-line background of density `L ≍ log T` a sparse
off-line family of depth `δ` hides up to aperture `≍ (1/2δ) log log T`). The conjecture is that the
model law is the actual law for `ζ`: the only obstruction to seeing the top zero is the local zero
density, which costs `log log γ*` apertures per unit of `1/δ`, and companions (Wall 3) can only
raise the upper bound by the polylogarithmic factor already present.

Non-circularity: both bounds are statements about a hypothetical off-line configuration; the
conjecture does not produce a sign. Its value is the exchange rate between the aperture unit and
the (height, depth) of the top zero: a certified aperture `A` would then exclude every zero with
`c log log γ/δ ≤ A`, i.e. every zero of depth `≥ c log log γ / A` up to height `γ`, which with the
unconditional strip `δ ≤ ½` says nothing (as it must, by the unbounded-aperture property) but with a
growing aperture reads off the width.

## Gates
- [ ] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  not applicable

## Approach
Lower bound (invisibility below `log log γ*/δ`): a Plancherel–Pólya sampling inequality for
Paley–Wiener functions of type `A` on the on-line zeros near `γ*`, whose local count is
`≍ log γ*` (`R:XiZeroCountLocalCeiling`), absorbs the negative pair term
`−2|f̂(γ* − iδ)|² ≤ 2e^{2δA}‖f‖₁²`; the ratio of the two is `e^{2δA}/(A log γ*)`, which is below
`1` exactly for `A ≲ log log γ*/(2δ)`. Upper bound: the modulated two-bump test of the lag family
at lag `≈ log log γ*/δ` against an isolated top zero, then the companion analysis of
`Q:ZetaNearTopZerosHideOnlyInCollapsedClusters` to remove the isolation premise at the price of
the polylogarithmic factor. Both halves are statements about the Weil form of a tempered
configuration with `ζ`'s local zero count and may be proved for the configuration class first.

## Log
- 2026-10-21 — created from the route-unification round two (the unifying object).
