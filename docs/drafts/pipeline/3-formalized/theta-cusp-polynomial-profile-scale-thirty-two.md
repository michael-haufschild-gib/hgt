# Exact quartic cross-load capacity at theta scale thirty-two

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Statement:** At `x=log(32/π)/2`, the quartic repair and its literal weighted
  source fail PSD for every `0<a<1/2`. Their scalar loads have exact positive
  capacities `τ` and `τ(a)=τ/α(a)`, with
  `0<τ<27/35`, `67/70≤α(a)≤1`, and `τ≤τ(a)≤70τ/67<54/67`.
  Each matrix is PD exactly below its capacity, PSD exactly at or below it,
  and singular at the endpoint.

Write `F=thetaCuspFullSource`, `G=3F²+2xFF'`,
`G_P=(1−2x²)²G−8x²(1−2x²)F²`,
`H=nativeShiftedMatrix 5 0 x`, and `B=crossLoad paidSevenSchur`.
The matrices are `H+tG_P B` and `w(a)H+tD(a)B`, where
`w(a)=2x sinh(2ax)` and `D(a)=deriv(flux a)(2x)`.
Thus `α(a)=(D(a)/w(a))/G_P`.

At this center, `9/8≤x≤6/5` and the complete-source slope satisfies
`F'≤−59F`. Therefore `G≤−519F²/4`. With
`u=2x²−1∈[49/32,47/25]`, the identity
`G_P=u²G+8x²uF²` yields `G_P≤−280F²`.
For `K=4·32² exp(x−64)`, the first atom gives `F²≥K·61²`.

Every normalized even jet through order sixteen differs from its first atom
by at most `1/10000`. The exact Gaussian-coordinate majorant makes the last
matrix-entry error at most one. The rational comparison
`polyModel 32 0 (−216·61²) 1 4 4 < 0` then proves a negative last Gaussian
coordinate whenever the normalized load coefficient is at most `−216·61²`.
Congruence transfers this obstruction to the original complete-source matrix.

The exact differentiated flux is
`D=wG_P+P(2x)(2x)[2ax cosh(2ax)−sinh(2ax)]F²`.
Here `0≤2ax≤6/5`, `cosh(2ax)≤4`, and `P(2x)≤4`, so its remainder lies in
`[0,12wF²]`. Consequently
`G_P≤D/w≤G_P+12F²≤(67/70)G_P≤−268F²`.
This proves `67/70≤α≤1` and excludes unit load for every critical aperture.

The native matrix `H` is PD and `−G_P B` is PSD. The PD locus of
`H+tG_P B` is an open initial interval. Unit-load failure bounds it above;
continuity gives a PSD endpoint. PSD beyond that endpoint would, by convex
combination with `H`, make the endpoint PD, a contradiction. Its determinant
therefore vanishes. The negative coordinate at load `27/35` gives
`τ<27/35`, since `(27/35)·280=216`.
The identity `wH+tDB=w[H+(tα)G_P B]` gives the aperture capacity and all
stated bounds. These are pointwise source results; integrated rank-nine
positivity remains open.

Lean files under `formal/GaloisForLFunctions/ThetaCuspSections/`:

- `FifthEvenScaleThirtyTwoData.lean`: `ThirtyTwoCrossData.upper_model_last_negative`.
- `FifthEvenScaleThirtyTwoSourceBounds.lean`: complete slope, jet, profile and aperture bounds.
- `FifthEvenPolynomialCrossObstruction.lean`: `ThirtyTwoCrossObstruction.repair_not_posSemidef`,
  `weightedRepair_not_posSemidef`.
- `CrossLoadCapacity.lean`: shared finite-pencil capacity proof, also used at scale eight.
- `FifthEvenScaleThirtyTwoCapacity.lean`: `ThirtyTwoCrossCapacity.exact_scaling_capacity`,
  `capacity_upper`.
- `FifthEvenScaleThirtyTwoApertureCapacity.lean`: `ThirtyTwoApertureCapacity.fraction_bounds`,
  `fraction_lower`, `posDef_iff`, `posSemidef_iff`, `boundary`, `capacity_gain_bound`, `capacity_upper`.

Canonical module checks passed. All 33 audited declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.
