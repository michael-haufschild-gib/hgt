# The even-product field and lifting reflection

- **ID:** galois-zero-even-product-field
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-1011/fable.md`, §§10.5(1–3), 10.6.
- **Lean:** `formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheEvenProductFieldOfTheZeros.lean`

## Exact objects and results

Let `a_ρ=ρ−1/2` for every actual ξ zero,
`L=ℚ(a_ρ : ρ)` and `K=ℚ(a_ρ a_τ : ρ,τ)`.

Every anchor is nonzero, `L=K(a_ρ)`, and `[L:K]≤2`. The degree is two
exactly when `a_ρ∉K`. A rational field automorphism of `L` realizes the
functional equation exactly when it negates every centered zero. Such an
automorphism exists iff `a_ρ∉K`; it is unique, and its fixed field is exactly
`K`. These statements hold for every anchor and the complete divisor.

Complex conjugation preserves both fields. Moreover

`K⊆ℝ ⇔ every actual zero has real part 1/2`.

## Proof

For each `τ`, `a_τ=(a_τ a_ρ)/a_ρ`, and both numerator and `a_ρ²` belong
to `K`. Thus a single square root generates the full extension. If the
anchor lies outside `K`, quadratic conjugation negates it and therefore
negates every generator. Conversely a field lift fixes all even products
and moves the anchor. Every element has coordinates `u+v a_ρ` with `u,v∈K`;
the lift sends it to `u−v a_ρ`, proving uniqueness and the fixed-field claim.

Conjugation permutes the generators of both fields. Hardy's theorem supplies
an actual critical zero, hence a nonzero purely imaginary anchor. If all
even products are real, the imaginary part of its product with any other
centered zero forces that zero's real part to vanish. Conversely, products
of purely imaginary centered zeros are real, and field operations preserve
reality.

## Boundary

`K` is defined from actual zero products; no prime-side identification is
claimed. Neither reality of `K` nor exclusion of an anchor from it is
assumed. The result classifies the lifting obstruction and does not prove RH.

## Main declarations and verification

- `centeredZeroExtension_eq_adjoin`
- `centeredZeroExtension_degree_le_two`
- `centeredZeroExtension_degree_two_iff`
- `centeredQuadraticReflection_all`
- `centeredNegation_fixed_iff`
- `centeredFunctionalReflection_lifts_iff`
- `centeredFunctionalReflection_unique`
- `centeredZeroField_conjugation`
- `centeredEvenProductField_conjugation`
- `centeredEvenProductField_real_iff`

Direct Lean source check passed. All 15 axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.
