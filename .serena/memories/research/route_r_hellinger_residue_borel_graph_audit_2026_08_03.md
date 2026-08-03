# Route R Hellinger-residue graph audit (2026-08-03)

## Exact conclusion

The current `COFINAL_HELLINGER_RESIDUE_GRAPH_BOUNDARY` cannot be closed by the obvious coefficient-faithful Hilbert packet or its canonical order-two Borel repair.

For
[
r_n=\frac{\eta(-1-2n)}{-1-2n}\frac{\Gamma(3/2)}{(2n)!\Gamma(3/2-2n)},
]
zeta functional equation plus Gamma reflection gives
[
r_n=(-1)^n(2-2^{-2n-1})\zeta(2n+2)
\frac{\Gamma(3/2)\Gamma(2n-1/2)}{\pi^{2n+3}}.
]
Hence `|r_n|` grows factorially (successive ratios grow quadratically). Any labelled graph chain whose new-cell normalized coordinate is `r_n` and whose coordinate readers are uniformly bounded cannot be Cauchy: Cauchy increments tend to zero, while the coordinate lower bound diverges. This kills same-line and unit/orthogonally-labelled Hilbert realizations; it does not kill graph norms with factorially growing coordinate-reader norms or cancellation before label separation.

The canonical order-two Borel normalization has exact germ, for `|z|<π`,
[
B(z)=\sum_{n\ge0}\frac{r_n}{\Gamma(2n-1/2)}z^{2n}
=\frac{\Gamma(3/2)}{2\pi z}\tanh(z/2).
]
After normalization `\widehat B=(2π/Γ(3/2))B`, coupling before scalarization to source coorientation `z` and Gamma reflection-odd factor `sinh z` gives
[
z\widehat B(z)\sinh z=2\sinh^2(z/2).
]
With `z=2c\log p/\log N`, this is one half of the already formalized local reflected prime-valuation Hellinger energy `4sinh²(c log p/log N)`.

## Hostile audit

This is a route-specific exact bridge, not an RH annihilator. It produces a nonnegative detector whose radical is exactly zero displacement. Existing source papers already prove the corresponding residue/Gamma coordinate vanishes iff displacement is zero; no independent arithmetic source law forces its vanishing. Claiming closure from positivity would assume the missing Route R theorem.

Surviving producer category: singular Borel/graph boundary with coordinate-reader norms growing at least factorially, or relative/distribution-valued cancellation before frequency/cell separation, plus an independently derived arithmetic Stokes/annihilation identity. Safe source-to-Xi landing is already closed; first open arrow remains source-derived horizontal annihilation before scalarization.

No files were modified and no Lean work was started in this audit.