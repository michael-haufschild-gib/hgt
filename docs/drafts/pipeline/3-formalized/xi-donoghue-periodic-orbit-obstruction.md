# Xi Donoghue periodic-orbit obstruction

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** A nontrivial upper-half-plane periodic orbit of the normalized Xi logarithmic derivative falsifies RH.

## Corpus basis and distinction

`SuzukiXiDonoghueTarget` proves that RH makes
`m(z) = -logDeriv XiC z / xiHedenmalmDonoghueScale` an upper-half-plane self-map fixing `i`.
`SuzukiXiFirstDefectJet` proves unconditionally that `m'(i)` is real and lies in `(77/85,1)`.
`XiNewtonSchwarzPickCriticalLine` provides disk Schwarz rigidity, but concerns Newton maps.

The witness is a periodic orbit of `m`, not a zero of Xi, a negative logarithmic
derivative, or a Newton-invariant disk. Its points can all obey the existing pointwise sign test.
The new mechanism is strict contraction towards the anchored point, using the unconditional
derivative gap to exclude rotations.

## Proven statements

1. RH forces strict decrease of `|(m(z)-i)/(m(z)+i)|` from `|(z-i)/(z+i)|` for every upper point `z ≠ i`.
2. Therefore every upper periodic point of `m` is `i`; any exception falsifies RH.
3. In particular a second upper solution of `XiC'(z) + c z XiC(z) = 0`, `c = xiHedenmalmDonoghueScale`, falsifies RH.

## Paper proof

Write `C(z)=(z-i)/(z+i)` and `g=C ∘ m ∘ C⁻¹`. Under RH, `g` is holomorphic on the disk,
maps it into itself, and fixes zero. Chain differentiation gives `g'(0)=m'(i)`, whose modulus
is strictly less than one by the unconditional first-jet theorem.

Schwarz gives `|g(w)|≤|w|`. Equality at nonzero `w` makes `g` affine by its equality case;
since `g(0)=0`, its slope has modulus one. This contradicts the derivative gap. Thus
`|C(m(z))|<|C(z)|` for every upper `z≠i`.

All iterates remain upper under RH. Cayley radius never increases, and its first step strictly
decreases away from `i`; a positive iterate therefore cannot return to its starting point.
Finally, RH makes XiC nonzero in the upper half-plane, so
`XiC'(z)+c z XiC(z)=0` implies `m(z)=z`. A solution other than `i` contradicts the periodic-point
classification with period one. This argument requires no nonvanishing assumption in the witness.

## Novelty boundary

Targeted semantic searches and all literal occurrences of the established Donoghue target found
normalization, first and second jets, and source-limit theorems; no orbit classification or
stationary-point endpoint. Generic Schwarz theory is reused, not claimed new. The contribution
is the Xi dynamical obstruction and its exact Gaussian-stationary witness. No converse or
existence of a falsifying witness is claimed.

At a fixed point with `XiC(z)≠0`, the witness equation gives
`Im(logDeriv XiC z) = -c Im(z) < 0`: it passes the existing pointwise Herglotz sign test.
The obstruction is dynamical rigidity, not a renamed sign violation.

## Lean statements

- `Bottcher/HalfPlane/AnchoredSchwarz.lean`: `cayleyRadius_strict_decrease`,
  `eq_I_of_iterate_eq_self`.
- `Bottcher/HalfPlane/XiDonoghueDynamics.lean`:
  `not_riemannHypothesis_of_xiDonoghue_periodicPoint`,
  `xiGaussian_stationary_eq_I_of_rh`,
  `xiGaussian_stationary_I`, `xiGaussian_stationary_iff_eq_I_of_rh`.

The stationary classification includes the unconditional anchor; the endpoint excludes exactly
that known solution. It is the period-one case of the same endpoint family, without a second
falsification wrapper.

## Verification

Both leaves passed standalone `lake --old env lean <module>.lean` checks. All nine public
capstones audited by `#print axioms` depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The stationary-wrapper consolidation also passed its standalone source audit.
The general helper's olean was built solely for the Xi specialization. Both leaves are wired
into `Bottcher.lean`; no umbrella build, numerical experiment, or added proof budget was used.
