# Rank-one pole of the actual Mayer determinant

- **Stage:** 1-in-progress
- **Type:** Conjecture
- **Parent:** [three approaches, A](argon-three-orthogonal-rh-approaches.md).
- **Prerequisite:** [source-parameter holomorphy](../3-formalized/gauss-mayer-source-parameter-holomorphy.md), Lean-certified.

## Target

For the actual decomposition `L(w)=R(w)+ζ(w)P`, `P f=f(0)·1`, prove

`D(w,λ)=A(w,λ)+ζ(w)B(w,λ)`

with `A,B` holomorphic in `w` throughout `Re w>0`, including one, and
entire in `λ`. Then the source determinant has at most a simple pole at
one, with exact residue `B(1,λ)`, and is removable exactly when this
residue vanishes. Determine whether `∂λ B(w,0)=−1` throughout `Re w>0`, making cancellation
parameters discrete and the pole genuine for every sufficiently small
nonzero `λ`. The parameter `λ=0` necessarily cancels the pole.

## Mechanism to audit

In the actual Cauchy basis the projection contributes only row zero.
Each finite determinant is therefore affine in its coefficient. The
geometric Fredholm limits should give

`A=det(I−λR)`, `B=det(I−λ(R+P))−det(I−λR)`.

Holomorphy across one still needs a uniform geometric bound for the
remainder matrix. One possible proof uses its already targeted operator
holomorphy and the scalar maximum principle on a parameter circle avoiding
one: uniform source bounds on the circle pass to its interior entrywise.
This avoids inferring a nuclear bound from the full operator norm alone.

The derivative at zero needs a certified first-coefficient identity for the
actual determinant. No pole-order or nonzero-residue claim is certified yet.
Selberg comparison and resonance exclusion remain separate obligations.

## Existing inputs audited

`det2Op_rankOne_update` in `HTGeometry/RegularizedDeterminantRankOne.lean`
proves a general
regularized update after a response vector is supplied; it does not supply
that vector for this source. Finite row multilinearity gives an alternative
that requires no inverse. `GeomFredholm.differentiable_fdet` already gives
entire dependence on `λ`; its parameter theorem handles `w` after uniform
bounds are proved. `norm_le_of_sphere_bound_centre` supplies the intended
maximum-principle step. These are ingredients, not a source certificate.

## First-coefficient proof to formalize

The strengthened derivative target follows from the same source normalization:
the geometric trace bound identifies the determinant near `λ=0` with its
order-one power-trace exponential. Existing termwise differentiation gives
`D′(0)=−Σ_i M_ii`. Subtracting the determinants for `R+P` and `R` cancels
the remainder diagonal; the actual projection diagonal sums to one. This
proves the proposed derivative uniformly in `w`, not merely at one, once the
source matrix and analytic identities pass Lean verification.
