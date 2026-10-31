# Xi Donoghue periodic-orbit obstruction

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** A nontrivial upper-half-plane periodic orbit of the normalized Xi logarithmic derivative falsifies RH.

## Corpus basis and distinction

`SuzukiXiDonoghueTarget` proves that RH makes
`m(z) = -logDeriv XiC z / xiHedenmalmDonoghueScale` an upper-half-plane self-map fixing `i`.
`SuzukiXiFirstDefectJet` proves unconditionally that `m'(i)` is real and lies in `(77/85,1)`.
`XiNewtonSchwarzPickCriticalLine` provides disk Schwarz rigidity, but concerns Newton maps.

The proposed witness is a periodic orbit of `m`, not a zero of Xi, a negative logarithmic
derivative, or a Newton-invariant disk. Its points can all obey the existing pointwise sign test.
The missing mechanism is strict contraction towards the anchored point, using the unconditional
derivative gap to exclude rotations.

## Conjectures

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
