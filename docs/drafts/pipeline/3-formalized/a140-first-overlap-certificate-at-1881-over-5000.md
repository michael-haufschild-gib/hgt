# Positive Weil floor at the first overlap

- **ID:** A140-first-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every real or complex compact `C²` test supported in
  `[-1881/5000,1881/5000]` has Weil energy at least `1/50000` times its squared
  mass. The same floor holds for every block matrix of window ratio
  `≤10609/5000`, at every block size and cutoff `Q≥2`.

## Proof

Put `a=1881/5000`, `G(u)=F(au)`, `M=∫₀¹G²`, and let `m₀,m₂,m₄` be the
first three even Legendre moments on `[0,1]`. Set
`b=log(2)/a−1`, `w=log(2)/sqrt(2)`, and
`U(x)=3029/3000+Σ_{j=1}^{32}x^{2j}/(2j)`.

The exact Gamma decomposition retains the mean, both correlation moments,
and its local remainder. The logarithmic lag splits into one quarter of
the regional energy plus the half-window boundary potential. The sixth
regional gap retains charges `49/20,19/4,33/10` on `m₀²,m₂²,m₄²`.

The centered primitive satisfies
`∫₀¹(∫₀ˣG)²≤(5/49)M+(1/3−5/49)m₀²−(2/3)m₀m₂`.
The cosh pole retains `4a(p₀m₀+p₂m₂)²`, with mass loss `M/50000`, where
`p₀=1+a²/24+a⁴/1920` and `p₂=a²/12+a⁴/672`.

The remaining moment charge is `mᵀDm`, with `ρ=97/50000` and

`D₀₀=49/20+a/2−a²/24−a³/24−4ap₀²−ρ+a²(1/3−5/49)/24`,

`D₂₂=19/4−4ap₂²−5ρ`, `D₄₄=33/10−9ρ`,

`D₀₂=−4ap₀p₂−a³/24−a²/72`, with other off-diagonal entries zero.

Polynomial reciprocal bounds and the signed reflection-pair inverse prove

`mᵀDm≤∫₀¹UG²−w∫_b¹G(x)G(b+1−x)dx+10⁻⁶M`.

The three-dimensional capacity matrix is bounded by `D⁻¹` with a positive
rational cushion. The change from rational reference parameters to actual
`b,w` is included in the estimate.

Seven positive Gamma modes give the mass constant `−14379/10000` after
adding `log 2`. Disjoint half-windows retain remainder `M/6250`.
Finally, `m₀²+5m₂²+9m₄²≤M` absorbs the `ρ` charge. The remaining mass is

`[49/20−14379/10000−3029/3000−5a²/1176−1/50000+1/6250−ρ−10⁻⁶]M`,

whose coefficient exceeds `1/50000`. This proves the even floor. The odd
floor has coefficient `1/2000`; orthogonal parity splitting gives the full real floor.
Complexification and smooth approximation give the closed form and packet
floors. The ratio bound follows from `log(10609/5000)<2a`.

## Lean

Modules in `formal/GaloisForLFunctions/WindowTowerOfSpecZ/`:

- `TheEvenWeilFormHasAFloorAtAperture1881Over5000.lean`:
  `weilQuad_ge_even_at_aperture_1881_over_5000`.
- `TheFirstOverlapWindowHasAPositiveWeilFloorAtEveryBlockSize.lean`:
  `fullZeroForm_ge_at_aperture_1881_over_5000`,
  `zetaZeroConfig_re_W_ge_at_aperture_1881_over_5000`,
  `one_div_50000_le_groundEnergy_of_aperture_le_1881_over_5000`,
  `packetForm_stepPacket_ge_of_first_overlap`,
  `sum_blockMatrix_ge_of_first_overlap`.

Direct Lean checks and transitive axiom audits passed. Only `propext`,
`Classical.choice`, `Quot.sound`. Modules wired into their umbrella.

The larger A140 apertures remain open; see
`../1-in-progress/a140-certificates-through-the-prime-five-boundary.md`.
