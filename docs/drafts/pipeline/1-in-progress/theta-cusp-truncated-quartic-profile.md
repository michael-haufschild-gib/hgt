# Quartic flux truncated at its double zero

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** Positive definiteness of the truncated fifth even repair for every
  `x≥0`, and of its literal weighted source for `0<a<1/2`, `r>0`.
  The flux profile is `P₊(r)=max(1−r²/2,0)²`.

The untruncated quartic fails at theta scale thirty-two, beyond its double
zero. Truncation removes that branch. The profile is continuously
differentiable: both its value and derivative vanish at `r²=2`.
On `r≥0` its flux is compactly supported, vanishes at both endpoints, and
has zero integrated derivative. Thus it should preserve every mixed entry.
These identities have not yet been formalized for the truncated profile.

For `x²<1/2`, its aperture-independent correction equals the original
`G_P=(1−2x²)²G−8x²(1−2x²)F²`. For `x²≥1/2`, it vanishes, leaving the
native matrix, already proved PD once `π exp(2x)≥5`.
Hence the missing sign is confined to `0≤x≤1/√2`.

Known input: the original quartic repair is PD near the origin, near theta
scale eight, and at the truncation point. These neighborhoods do not cover
the compact interval by any proved estimate.

**Unproved input:** an unconditional lower bound for the complete profiled
matrix on the intervening compact interval, retaining all theta atoms.
The conjectured quartic cross-load reserve from scale eight may control its
upper part; that reserve is itself unproved. No finite sampling, endpoint
interpolation, or assumed matrix sign supplies the missing estimate.

## Scalar comparison to formalize

For `q≥8`, `x²≤1/2`, the expected unconditional bound is
`G_P(x)>−(3/20)K(x)q⁴`. Put `b=7/15`, `p=1−2x²`,
`S=firstSlope(q)+10⁻⁵`, and
`J_S(x)=2x(1−2x²)²S+(1−2x²)(14x²−3)`.
The scale-eight center bound gives `x≥b`; the slope formula gives `S≥11`.

The complete-source bounds imply `G_P≥−J_S(x)F²`.
On `[b,1/√2]`,
`J'_S=−2(1−2x²)(10x²−1)S+8x(5−14x²)≤0`:
for `x²≥5/14` both terms are nonpositive; otherwise the negative magnitude
is at least `2332/315`, while the positive term is at most `24584/3375`.
The latter bound follows by factoring
`b(5−14b²)−x(5−14x²)=(x−b)[14(x²+bx+b²)−5]`.
Thus `J_S(x)≤J_S(b)≤(3/10)S+7/250`.
Using `S≤2q−9/2+10⁻⁵` and `F²≤(1000001/1000000)²K(2q−3)²`
reduces the claim to the exact positive polynomial, with `u=q−8≥0`:

`(3/20)q⁴−((61/100)q−13/10)(2q−3)²`
`=469/50+(359/20)u+(289/25)u²+(59/25)u³+(3/20)u⁴`.

This scalar derivation is not yet Lean-verified. The matrix reserve and the
remaining interval below scale eight are separate unproved requirements.
