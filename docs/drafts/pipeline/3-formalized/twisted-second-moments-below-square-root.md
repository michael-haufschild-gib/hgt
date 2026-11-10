# Twisted second moments below square-root length

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, A18.
- **Lean:** `MultiscaleMollifiedZetaField/TwistedSecondMomentsBelowSquareRoot.lean`.

## Statement

For every `0≤θ<1/2` and real `B`, there are `0<a<1` and `C≥0` such
that, for all sufficiently large `T`, every `T≤q≤2T`, `0<d≤1/20`,
`N≤T^θ`, and real coefficient sequence `|w_n|≤1` satisfies

`|∫ blockWindow(T,q,T^a;t) |ζ(1/2−d+it) Σ_{n≤N} w_n n^{−1/2+d−it}|² dt − M₁ − M₂|
 ≤ (q−T+2T^a) C T^{−B}`.

Here `M₁=gcdSum₁·ζ(1−2d)∫blockWindowC` and
`M₂=gcdSum₂·ζ(1+2d)∫blockWindowC·chiPairWeight` are the actual two
main terms. No estimate for either main term is assumed. The interval
moment on `[T,q]` is bounded above by `Re(M₁+M₂)` plus the same error.

## Proof

Set `δ=1/2−θ`, `b=δ/2`, and `a=1−b`. At scale `T`, use taper `T^a`,
frequency split `T^b`, and dual-product split `T^(1+b)`. Integration
orders `K,J` give direct, dual oscillating, and dual shifted exponents
`1−Kδ/2`, `4+b−Kδ/4`, and `2+b−bJ`. The Gaussian tail saves every
power. Contour depth `A=2j+1` gives smooth and dual remainder exponents
`−(1−2θ)A` and `−(1−2θ)A+1`. Choose these orders to absorb any prescribed
saving and the at most `T^(2θ)` coefficient pairs. The exact product
approximate functional equation then gives the formula. Nonnegativity
and window domination give the interval bound.

## Verification

- Endpoints: `exists_twistedMoment_power_saving`, `exists_interval_twistedMoment_le`.
- Direct check: `lake --old env lean GaloisForLFunctions/MultiscaleMollifiedZetaField/TwistedSecondMomentsBelowSquareRoot.lean`.
- Transitive axioms for both: `propext`, `Classical.choice`, `Quot.sound`.
- All five supporting modules are wired into `MultiscaleMollifiedZetaField.lean`.
