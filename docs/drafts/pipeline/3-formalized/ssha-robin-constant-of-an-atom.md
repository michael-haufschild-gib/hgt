# The Robin constant of an atom

- **ID:** ssha-robin-constant-of-an-atom
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** SSHA §8 "To build: the exact Robin constant"; AIT open topic 2 (sharp archimedean
  constants, `E_φ = ‖φ‖² log(1/δ) + O(‖φ‖²)` with coefficient one).
- **Statement:** For a Lipschitz `C²` bump `g` supported in `[0, w]`, `0 < w ≤ 1`,
  `levyEnergy g = (log(1/w) + 2c_∞)‖g‖² + β(g) + R`, `|R| ≤ (e^{1/2}/2) w ‖g‖²`, where
  `2c_∞ = 2∫_0^1(ω(y) − 1/(2y)) dy + 2∫_1^∞ ω` and `β(g) = ∫_0^w ‖g − g(·+y)‖²/(2y) dy`. For a dilated
  profile `φ(·/w)`, `β` scales by `w`, so `levyEnergy(φ(·/w))/‖φ(·/w)‖² − log(1/w) → κ_L(φ) = 2c_∞ + β(φ)/‖φ‖²`.

## Proof

Split `(0, ∞)` at `w` and `1`. Beyond `w` the shifts are disjoint, `Q = 2‖g‖²`; on `(w, 1]` subtract
`1/(2y)` exactly (`log(1/w)`); on `(0, w]` write `ω = 1/(2y) + r` with `0 ≤ r ≤ e^{1/2}/4` and
`0 ≤ Q ≤ 4‖g‖²`; the remainder `∫_0^w r (Q − 2‖g‖²)` is at most `(e^{1/2}/2) w ‖g‖²`. Dilation:
`Q_w(y) = w Q_1(y/w)` and `y = w t`.

## Significance

Replaces the two-sided `log(1/w) + O(1)` by the exact finite part. Numerically (`φ = sin²(πu)`):
`2c_∞ ≈ 2.957`, `β/‖φ‖² ≈ 1.254`, `κ₀ = 2θ′(0) + κ_L ≈ −1.16`; with the sharp prime counterterm
`log N − γ` the Markov form on the pole vector has finite part `log(1/c) + κ₀ + γ`, the input of the
selectivity card `selective-positivity-on-separated-atoms`.

## Status

Lean: `formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheRobinConstantOfAnAtom.lean`
(`archRobinConstant`, `bumpRobin`, `abs_levyEnergy_atom_sub_le`, `bumpRobin_atomDilate`,
`profileRobin`, `abs_levyEnergy_atomDilate_sub_le`, `tendsto_levyEnergy_atomDilate_sub_log`). Clean
check; axioms `propext, Classical.choice, Quot.sound`; wired into the SSHA umbrella.
Cross pairing (AIT topic 2, second half): `SpacingScaleHarmonicAnalysis/TheArchimedeanPairingOfTwoAtoms.lean`
(`levyMixed_atom_shift`, `levyEnergy_atom_pair`, `integral_bumpAutocorr`, `abs_crossTerm_sub_le`):
`levyEnergy(g + g(·−s)) = 2 levyEnergy g − 2X`, `|X − ω(s)(∫g)²| ≤ (ω(s−w) − ω(s+w))(∫|g|)²`. Clean, wired.
