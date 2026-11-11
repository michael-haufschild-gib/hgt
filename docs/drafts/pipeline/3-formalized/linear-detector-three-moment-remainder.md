# The linear detector has an explicit three-moment main term

- **ID:** A111-analytic-reduction
- **Stage:** 3-formalized
- **Type:** THEOREM

## Statement

For every `0≤θ<1/2`, there are `0<a<1`, `r>0`, and `C>0` such that,
for all sufficiently large `T`, uniformly in

`T≤q≤2T`, `1/T≤d≤min(r,1/40)`, `1<N≤T^θ`,
`0≤λ≤1`, and `λ log N≤1`,

the actual tapered linear-mollifier detector integral differs from
`detectorThreeMomentMain T q (T^a) N (linearDetectorWeights N d) d λ`
by at most `C T^(7/8)`.

The main term retains both direct and reflected gcd sums. Its displacement
jets hold all coefficients fixed. No shifted arithmetic asymptotic or
positive critical-zero proportion is asserted.

## Proof

Write `F=ζΨ`, `G=λζΨ′`, and `H=F−G`. Polarization and two integrations
by parts give the exact energy

`q_H − λ(q_F′−q_G′+q_H′)/2 + λ²q_F″/4`
`+ λ∫W′ Im(F conj G) + λ²∫W″|F|²/4`.

The three coefficient sequences are `w`, `−λ log(n)w`, and
`(1+λ log(n))w`. The actual moment remainder and its first two derivatives
have arbitrary power saving with a common taper. Quadratic homogeneity
handles the residual coefficients, bounded by two.

Both original and correction coefficients are bounded by `n^(−d)`.
The mollifier norm is therefore at most `2 sqrt(N)`. The thin-strip Weyl
bound `|ζ|≪T^(3/16)` and the two transition intervals give both taper
contributions `O(T^(7/8))` when `N≤sqrt(T)`.

## Lean

Namespace `GaloisForLFunctions.MultiscaleMollifiedZetaField`:

- `integral_mollifiedDetector_three_moments` in `TheMollifiedDetectorHasTheThreeMomentIdentity`.
- `exists_twistedMoment_first_three_jet_power_saving` in `TheTwistedMomentErrorKeepsItsDerivatives`.
- `exists_linearDetector_taper_error_bound` in `TheLinearDetectorHasSmallTaperError`.
- `exists_linearDetector_main_remainder_bound` in `TheDetectorMomentErrorsAreSmall`.

All modules passed direct Lean checks and are imported by the umbrella.
