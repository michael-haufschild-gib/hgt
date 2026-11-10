# The exceptional square repels the other twisted squares

- **Stage:** 3-formalized
- **Task:** review-1011, A101.
- **Module:** `AbsoluteGeometryOfSpecZ/TheExceptionalSquareRepelsTheOtherSquares.lean`.
- **Endpoints:** `exists_twisted_square_repulsion`, `exists_twistedComb_square_margin`.

There is an absolute `C>0` such that, for every primitive quadratic character
of conductor `q>1` and every positive real zero `β` of its actual L-function,
each nontrivial zero `ρ` other than `β` and its reflection satisfies

`m(Im ρ) ≤ 1/2 − |Re ρ−1/2|`,

where
`m(γ)=log(1/(C(1−β)log(q(|γ|+3))))/(C log(q(|γ|+3)))`.

Put `D(γ)=max(0,1/2−m(γ))` and
`S(δ,a)=∫[-a,a] sinh²(δu)du`. For every continuous complex packet supported
in `[-a,a]`, `a≥0`, the actual spectral square satisfies

`Re Wsummand(f,f,ρ) ≥ −mult(ρ) S(D(Im ρ),a) ∫|f|²`.

The second endpoint includes the actual twisted-comb limit
`twistedForm + 2 weightedContact → −twistedZeroSum` for smooth compact real
packets, together with these bounds on every remaining square. No repulsion,
explicit-formula, or square-energy estimate is assumed.

## Proof

Apply the uniform real-zero Deuring–Heilbronn theorem to a zero in the right
half-strip. Apply it to the reflected zero in the left half-strip; reflection
preserves its ordinate. This gives the displayed margin on both sides.

For transverse depth `δ=Re ρ−1/2`, the conjugate transforms differ by at most
`4 S(δ,a)∫|f|²` after squaring. This follows from the hyperbolic-sine integral
and Cauchy–Schwarz; negative depth swaps the two transforms, and depth zero
gives zero. The real part of a square is at least minus one quarter of this
squared difference, times its multiplicity. Monotonicity of `sinh²` in
absolute depth replaces `|δ|` by `D(Im ρ)`. The proved twisted explicit
formula supplies the comb limit.

`S(0,a)=0`; for `δ>0`, `S(δ,a)=sinh(2δa)/(2δ)−a`. A positive margin gives
`D(γ)<1/2`, retaining the quantitative improvement before strip clearing.

## Verification

Direct check from `formal/`:

```text
lake --old env lean GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheExceptionalSquareRepelsTheOtherSquares.lean
```

Exit 0. Both endpoint axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. Imported by `AbsoluteGeometryOfSpecZ.lean`; umbrella not built.
