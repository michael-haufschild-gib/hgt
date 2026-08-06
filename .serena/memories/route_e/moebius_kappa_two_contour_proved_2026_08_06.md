# The κ=2 Möbius contour is proved (parallel to the κ=9 one)

`RHTower.Sieve.exists_norm_tsum_moebius_smoothWeight_le_kappa_two`
(`RHTower/Sieve/MoebiusContourKappaTwo.lean`) is the four-edge estimate at the rectangle

    1 - 1/log²K ≤ Re s ≤ 1 + 1/log²K,   |Im s| ≤ (K-3)/2,

replacing the half-width `c₉/(16 log⁹K)` of `exists_norm_tsum_moebius_smoothWeight_le_concrete_sharp`.
Unconditional: `[propext, Classical.choice, Quot.sound]`.  `formal_tools.py lint` passes.

## The structural fact that made it cheap

`norm_tsum_moebius_smoothWeight_le_sharp` in `RHTower/Sieve/PerronSharpSubstitution.lean` is
**fully parametric** in `(c, d, T, Md, Mh, Mc, C₁, C₂, C₃)`.  It takes `hzf`, `hFd`, `hFt`, `hFb`,
`hFc`, `hFccont`, `hbd1/2/3` as hypotheses.  So a new contour is a *second instantiation* — do not
mutate `MoebiusContourBound.lean` or `MoebiusContourBoundSharp.lean`; both still compile untouched.

The same applies to any future width: only the six edge obligations change.

## The three ingredients that had to be built

1. `exists_norm_invZeta_strip_le` / `exists_norm_invZeta_contour_le`
   (`RHTower/Sieve/InvZetaStripBound.lean`).  Inversion of `exists_zeta_lower_strip` through
   `norm_invZeta_eq`.  Pinning the strip to a parameter `K ≥ |t|` is free: `1/log²K ≤ 1/log²|t|`
   widens the hypothesis and `C log²|t| ≤ C log²K` weakens the conclusion.

2. `exists_bound_invZeta_box` (`RHTower/Sieve/InvZetaUniformStrip.lean`) — the compact-box `1/ζ`
   bound at **arbitrary** height.  `exists_bound_invZeta_low_box` was hard-coded to `|Im| ≤ 1`
   although `exists_zero_free_rect` it rests on is general in `T`; only the literal had to go.
   Combined with 1 this gives `exists_norm_invZeta_uniform_strip`: **no height restriction at all**.

3. `exists_zeta_uniform_strip_zero_free` (`RHTower/Sieve/ZetaUniformStripZeroFree.lean`) — the same
   two-branch fit for zero-freeness, stated for `s : ℂ` so a `Complex.mem_reProdIm` membership
   feeds it directly.

## The fitting trick (reusable)

The strip theorem's threshold is astronomical (`≈ exp(50000)`) and the box's `δ` is inexplicit, yet
neither shows up in the final threshold shape.  Both are absorbed by requiring `log K ≥ max 1 (1/δ)`
and using **`log²K ≥ log K`** — so `1/log²K ≤ δ` follows with no square root, and the box constant
`M₀` is absorbed into `C·log²K` because `log²K ≥ 1`.  Take the natural-number threshold as
`max 5 ⌈exp(L₀+1)⌉₊`; the `+1` buys `log K ≥ 2`, hence `1/log²K ≤ 1/4`, hence `leftAbscissa > 0`
(needed by `hc : 0 < c` in the general lemma).

## What is still open

Step 3 of `docs/drafts/pipeline/1-in-progress/moebius-exponent-upgrade.md`: the *consumer* that
optimises over `K` still runs the κ=9 capstone and reports `exp(-c(log x)^{1/10})`.  With the new
rectangle the balance is `log²K` against `(N+H)^{-1/log²K}`, i.e. `log K ≍ (log x)^{1/3}`, so the
report should become `exp(-c(log x)^{1/3})`.

See `mem:route_e/moebius_exponent_is_one_over_kappa_plus_one_2026_08_06`.
