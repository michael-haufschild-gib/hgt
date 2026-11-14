# Odd Weil certificate at `1881/5000`

- **ID:** A140-odd-1881/5000
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every odd real compact `C²` test supported on `[-1881/5000,1881/5000]`
  satisfies `weilQuad F ≥ (1/2000)∫F²`.

## Polynomial comparison

Put `a=1881/5000`, `d=log(2)/a`, `b=d−1`, `w=log(2)/sqrt(2)`,
`U(x)=31/80+Σ_{k=1}^{16}x^(2k)/(2k)`, and

`E(G)=∫₀¹U G²+w∫_b^1 G(x)G(d−x)`.

The supersolution is `g=x(80/31−89x²/30+11x⁴/10)` on `[0,b)` and
`g=263/100−23x/10` on `[b,1]`. Polynomial certificates give `Tg≥x`,
`∫₀¹xg≤389/1000`, and `T≥31/80`. The adjugate applied to the position
vector is nonnegative on every reflected pair. Completing squares therefore gives

`2t∫₀¹xG≤E(G)+(389/1000)t²`.

Consequently `E(G)−(77/30)(∫₀¹xG)²≥(1/2000)∫₀¹G²`.
This statement and its transitive axiom audit passed Lean:
`WindowTowerOfSpecZ.firstOverlapOddEnergy_sub_first_moment`, in
`TheFirstOddMomentIsPaidAtAperture1881Over5000.lean`.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.

## Transfer to Weil's form

For `G(u)=F(au)`, the required comparison is

`2a[E(G)−(77/30)(∫₀¹uG)²]≤weilQuad F`.

Use the third regional Legendre gap with first charge `5/2`, the exact exterior
logarithmic potential, and `weilQuad_ge_logarithmic_first_moment`. The constants are

`11/6−firstFoldMomentMassCost−log(2a)≥31/80`,
`5/2+(39/32)a³≤77/30`.

The logarithmic lag tail beyond `2a` equals `−log(2a)∫F²`; the prime-two
correlation becomes `−a∫_b^1 G(x)G(d−x)`. The complete transfer is proved by
`WindowTowerOfSpecZ.weilQuad_ge_odd_at_aperture_1881_over_5000`, in
`TheOddWeilFormHasAFloorAtAperture1881Over5000.lean`.

Direct `lake --old env lean` checks passed for this module, the polynomial
comparison, and `RegionalLogarithmicFirstOddMoment.lean`. All capstone
transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
The even sector and the larger apertures of A140 remain open.
