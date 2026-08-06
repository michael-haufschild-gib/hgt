# The corpus's Möbius saving exponent `1/10` is `1/(κ+1)` — and κ is now improvable

Card: `docs/drafts/pipeline/1-in-progress/moebius-exponent-upgrade.md`.

`RHTower/Sieve/MoebiusTwistMajorantRatio.lean` ends in
`exp(-zeroFreeConst * (log x)^(1/10) / 8192)`. The `1/10` is **not intrinsic**: it is `1/(κ+1)` with
`κ = 9`, inherited from the zero-free region available when the chain was built.

## Where κ enters (localised)

`RHTower/Sieve/MoebiusContourBound.lean`, four definitions:
`leftAbscissa K = 1 - zeroFreeConst/(16 log⁹K)`, `rightAbscissa K = 1 + zeroFreeConst/(2 log⁹K)`,
`invZetaEdgeBound K`, `invZetaRightBound K`. Plus the four `‖invZeta …‖ ≤ …` lemmas in
`RHTower/Sieve/MoebiusContourBoundSharp.lean`. Everything downstream
(`MoebiusTwistContourBoundGeneral`, `CoeffMajorant`, `MoebiusTwistSaving`,
`MoebiusTwistMajorantRatio`) only consumes those.

## The exponent arithmetic

Balance the contour saving `x^{-δ(K)}` against the truncation error `1/K`:
`log K = (c log x)^{1/(κ+1)}` and the saving is `exp(-c'(log x)^{1/(κ+1)})`.

- κ = 9 → `1/10` (matches the corpus exactly, which confirms the reading);
- **κ_eff = 2 → `1/3`** with `mem:route_e/exponent_one_zeta_toolkit_complete_2026_08_06`'s
  `exists_zeta_lower_strip`;
- κ = 1 → `1/2`, unreachable here.

**The binding constraint is the `1/ζ` strip, not the zero-free region.** The contour needs a *bound*
on `1/ζ` at its left abscissa, not just nonvanishing. The corpus's region has width
`1/(10000 log|γ|)` but `1/ζ` is controlled only on width `log^{-2}|γ|`. Hence `κ_eff = 2`.
`mem:route_e/inv_zeta_width_ceiling_2026_08_06` explains why `1/ζ` cannot be pushed to the full
region by this method.

## How to do it safely

**Add the κ=2 definitions alongside the κ=9 ones and build a parallel capstone.** Do not mutate
`leftAbscissa` etc. in place: this is a working multi-module chain from earlier sessions, and the
κ=9 version must keep compiling until the κ=2 one is proved.

Watch the threshold: `exists_zeta_lower_strip` only holds past `≈ exp(50000)`, so the new
`‖invZeta‖` lemmas need a large-`K` side condition. The chain already carries `K₀ ≤ K` in
`exists_norm_tsum_moebiusTwist_smoothWeight_le_general`, which suggests it will absorb one.
