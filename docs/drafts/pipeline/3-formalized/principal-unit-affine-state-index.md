# Principal-unit restriction preserves the affine Weil index

- **Stage:** 3-formalized
- **Type:** THEOREM; paper proof, Lean proof, direct source check, and axiom audits complete.
- **Parent:** [three approaches](../1-in-progress/argon-three-orthogonal-rh-approaches.md), C4.

## Claim

For prime `p`, resolution `n`, and `c>0`, let `H=H(p,n)` be the positive rational
principal-unit group from `EveryPadicNeighborhoodCarriesTheWholeIndex`. Let
`A_H={x↦ax+b : a∈H, b∈ℚ}`. Then

```text
κ₀(ratCorr|H) = κ(ratCorr),
κ(weilPadicState(p,c)|A_H) = κ(ratCorr)+1.
```

Here `κ₀` is the negative index on coefficient families of total mass zero.
The second identity retains the actual successor square as well as every
off-critical zero square. It imposes no restriction at other primes.

## Paper proof

For any kernel `K` on a commutative group and any `a`, its difference kernel
`L_aK(g)=2K(g)-K(ga)-K(ga⁻¹)` has Gram forms obtained from the doubled family
`x_i,x_i a` with weights `c_i,-c_i`. These weights have total mass zero, hence
`κ(L_aK)≤κ₀(K)≤κ(K)`.

Weak approximation makes `log H` dense in `ℝ`. Choose `a∈H`, `a≠1`.
The double difference of the cubic-spline test has Fourier multiplier
`(exp(iz log a)-1)²`, nonzero at every off-critical ordinate. Its orbit kernel
is `L_a² ratCorr`; dense restriction to `H` retains the full zero-count index.
Thus `κ(ratCorr)=κ(L_a² ratCorr|H)≤κ(L_a ratCorr|H)≤κ₀(ratCorr|H)`.
Restriction gives the reverse inequality.

Every slope in `H` has p-adic norm one, so the place-polar mass is ordinary
total mass. In the gluing lower-bound proof, use a negative mass-zero family
of dilations in `H` and the two translations `1,x↦x+p^(-N)`, with weights
`p^(-N/2)`. The successor cross terms cancel by zero mass; the remaining cross
terms tend to zero. The translation-pair block tends to `-2c`, preserving
one additional negative square. All these affine elements lie in `A_H`.
The upper bound follows from restriction of the global gluing formula.

## Lean declarations

- `negIndex_lap_le_polarIndex`: difference compression into the mass-zero hyperplane.
- `polarIndex_ratCorr_of_dense_log`: full polar index on every subgroup with dense logarithms.
- `polarIndex_ratCorr_padicPrincipalUnits`: specialization to `H`.
- Subgroup version of `add_one_le_negIndex_glueAt`, retaining its existing proof.
- `negIndex_weilPadicState_principalUnits`: the native affine identity.

No RH conclusion follows: the full unknown global index survives the local restriction.

Module: `AdelicKreinGeometry/EveryPadicNeighborhoodCarriesTheWholeAffineState.lean`.
Transitive audits use only `propext`, `Classical.choice`, `Quot.sound`.
Umbrella import is wired; no umbrella build was run.
