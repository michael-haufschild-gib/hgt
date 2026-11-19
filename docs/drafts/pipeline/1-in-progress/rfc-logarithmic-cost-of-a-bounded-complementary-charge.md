# Logarithmic density paid for a bounded complementary charge

- **Stage** 1-in-progress
- **Target** If the complementary ordinary Möbius prefix stays in \([-K,K]\), the selected positions have upper logarithmic density \(\gg (1+K)^{-2}\).

For a fixed integer \(h\), the logarithmic mean of the square of the Möbius sum on \((n,n+h]\) is \(6h/\pi^2\). Expanding the square gives squarefree density on the diagonal and logarithmic two-point Möbius cancellation at every nonzero lag. Translation by each fixed offset preserves upper logarithmic density. If the selected set has upper logarithmic density \(d\), its contribution to the interval sum has upper logarithmic mean-square norm at most \(h\sqrt d\). The complementary contribution is a difference of prefixes bounded by \(2K\). Thus \(\sqrt{6h/\pi^2}\le 2K+h\sqrt d\). Taking \(h\) of order \((1+K)^2\), with a sufficiently large absolute factor, proves the target. [Tao, The logarithmically averaged Chowla and Elliott conjectures for two-point correlations](https://arxiv.org/abs/1509.05422)

**Formal dependency.** The unweighted-shift logarithmic Liouville theorem alone does not supply all squarefree-restricted correlations. The two-point Möbius theorem, or enough affine Liouville correlations for square-divisor inversion, is still needed. The elementary equal-sign window theorem gives positive lower *natural* densities of both selected signs with a different dependence on \(K\).
