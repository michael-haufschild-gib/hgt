# Beyond 1/3: the exponent-1/2 mechanism is the explicit formula, not the 1/ζ contour

The corpus's formalized Möbius rate is `exp(-(log N)^{1/3}/108)`
(`mem:route_e/moebius_sharp_rate_exponent_one_third_2026_08_06`).  The literature's explicit
unconditional bounds (`arXiv:2208.06141`, Lee–Leong) are `exp(-η√(log x))` and the
Vinogradov–Korobov `exp(-η(log x)^{3/5}(loglog x)^{-1/5})`.

## Why the contour chain cannot reach 1/2

The rectangle needs `1/ζ` polynomially bounded in the logarithm.  Transporting the `σ = 1+log^{-2}`
lower bound leftwards costs `‖ζ'/ζ‖ × (segment length)`, and `ζ'/ζ ≪ log²` is what the region gives.
A segment of length `c/log|γ|` therefore costs `log²·(c/log) = c·log|γ|`, i.e. `‖ζ‖ ≫ |γ|^{-c}` —
polynomial in `|γ|`, useless in a contour.  So the widest usable strip is exactly `≍ log^{-2}`, and
the saving exponent `1/(w+1) = 1/3` follows.  **Do not attempt to widen the rectangle.**

## The mechanism that does reach 1/2

The explicit formula over zeros, which never touches `1/ζ` on the region:

    ψ(x) - x = -∑_{|γ| ≤ T} x^ρ/ρ + O(x log²x / T)
    |x^ρ| ≤ x·exp(-c log x / log|γ|),   #{ρ : |γ| ∈ [n, n+1]} ≪ log n

Balancing `exp(-c log x/log T)` against `x/T` gives `log T = √(c log x)`, hence `exp(-c√(log x))`.
The inputs are the **zero-free region** and a **zero-counting estimate** — both already in the
corpus (`exists_zero_free_region_explicit`, `exists_wide_zero_count` in
`RHTower/Sieve/ZetaZeroCountWide.lean`, on `Re ρ ≥ 3/5`).

What is missing is a **truncated explicit formula**.  That is the next target and it is a different
build from the contour chain, not a re-tuning of it.  Check `PNTPlus` before starting: it proves the
PNT with error term independently and may already carry a Perron/zero-sum layer.
