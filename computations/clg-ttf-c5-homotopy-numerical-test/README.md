# Numerical falsification test of the CLG/TTF C5 likelihood-homotopy core (2026-09-04)

Target card: `1-in-progress/theta-c5-likelihood-homotopy-curvature.md`.  Tested statements
(exactly the card's `[CONJECTURE]` block, on the physical structural tail `0 < t ≤ u`,
`π e^{2u} ≥ 6`, `0 ≤ λ ≤ 1`):

1. `M'''(λ) > 0` (Lean object `thetaCuspC5LikelihoodHomotopyCompensationThree u t λ`);
2. `M''(0) ≥ 0`;
3. atom-tangent reserve `M'(0) ≥ −M(0)/5`;
4. the gate itself, `M(1) > 0`.

## Transcription

`clg_compensation.py` transcribes, line by line, the Lean definitions of
`thetaCuspC5LikelihoodHomotopyData` (files `ThetaCuspSingleAtomReflectedRiccatiContraction`,
`ThetaCuspReflectedLikelihoodCumulantObstruction`, `ThetaCuspFixedActionC5ExactFirstAtomTailReduction`,
`ThetaCuspFixedActionC5LikelihoodCenterFlow`, `ThetaCuspLikelihoodSpectralMeasure`,
`ThetaCuspLikelihoodModularSeam`) and of the `C5LikelihoodAffineData` methods
(`ThetaCuspFixedActionC5LikelihoodHomotopyCurvatureReduction`).  The higher theta likelihood state is
the Laplace transform of the atomic spectral measure `Σ_{n≥2} (w_n δ_{n²−1} + r_n Leb|(n²−1,∞))`; the
moments are closed forms (incomplete Gamma sums).  Validation (`clg_validate.py`, 50 digits): the
three log-partition jets agree with numerical derivatives of `log Z` to 12 digits, and
`compensationThree` agrees with the numerical third `λ`-derivative of `compensation` to 12 digits.

## Results

* `clg_compensation.py` — 2880 points, `u ∈ (0, 3]`, `t ∈ (0, u]`, 21 values of `λ`, 30 digits: no
  negative value of `M'''`; the only zeros are underflow (`dq = 0` at 30 digits for `u ≥ 1.75`).
* `clg_hp.py` — 400 digits, `u ∈ {0.001, 0.005, 0.01, 1.5, …, 8}`, `t/u ∈ {0.001, …, 1}`: `M''' > 0`
  everywhere; the adverse term `W''' H` is at most `1.2 %` of `3W''H' + 3W'H''` in absolute value.
* `clg_signs.py` — sign structure (80 digits): `dq < 0`, `da < 0`, `H < 0`, `H' > 0`, `H'' > 0`
  (the last is the corpus theorem `thetaCuspC5LikelihoodHomotopy_velocityCenterTwo_pos`), `W' < 0`;
  `W''`, `W'''` are negative except near `t = u` where they turn positive.
* `clg_faces.py` — the corpus's four-face Bose cone (`BoseShiftedTransportCone`) fails at 699 of 720
  points, almost always through the first face (`boseShiftedTransportOne > 0`), while the full
  balance stays negative: consistent with the Lean route kill of Conjecture K, and showing that the
  true statement survives that kill.
* `clg_full.py` — 861 points on the structural tail, 120 digits: **zero violations** of any of the
  four statements above.
* `clg_perturb.py` — the homotopy is nearly constant: `max |M(1) − M(0)| / M(0) = 0.19`, attained at
  the corner `u = u_min = ½ log(6/π)`, `t = u`; elsewhere `≤ 0.08` and decaying like the `n = 2`
  atom weight `e^{−3(B+3/2)}`.  All seven likelihood corrections are at most `5.9 %` of the
  first-atom jets on the tail.

## Verdict

`SURVIVES` with large margin.  The falsification pass did not close the branch.  The perturbative
structure suggests a proof of the gate `M(1) > 0` that bypasses `M'''` entirely:
`M(1) ≥ M(0) − ∫₀¹ |M'|`, an explicit quantitative lower bound for the first-atom compensation
`M(0) = c5SingleAtomCompensationMargin(A, t)` (Lean proves only its sign), and explicit upper
bounds for the seven `n ≥ 2` corrections through the atomic spectral measure.  This is a finite
special-function inequality with no RH content of its own; closing it advances only the compact
seam of CLG/TTF, after which the card lists "clustered/general packets and cofinal escape".
