# Finite rational affine unitary representations kill translations

- **ID:** RATIONAL-AFFINE-FINITE-UNITARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Finite-index Mautner rigidity](finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** Every finite-dimensional complex representation of `Aff(ℚ)` has translation trace equal to its dimension. Every finite-dimensional unitary representation therefore kills all translations and factors through the dilation group `ℚˣ`. None of these statements needs continuity.

## Dependency-closed paper proof

Write `T_b` for translation by `b`, `ρ` for a `d`-dimensional complex representation, and `τ=tr ρ(T_1)`. Conjugation by dilation `b≠0` identifies `T_1` with `T_b`, so every nonzero translation has trace `τ`; the zero translation has trace `d`.

Set `N=d²+1`, choose distinct rationals `b_i=i` for `0≤i<N`, and put `b_*=N`. On the `d²`-dimensional matrix space define

`ℓ_j(M)=tr((ρ(T_(-b_j))−ρ(T_(-b_*)))M)`.

The translation law gives `ℓ_j(ρ(T_b_i))=(d−τ)δ_ij`. If `d≠τ`, applying these functionals to any linear relation shows that the `N` matrices `ρ(T_b_i)` are independent, contradicting their ambient dimension. Thus `τ=d`.

For unitary `U=ρ(T_b)`,

`tr((U−I)* (U−I))=2d−tr U−conj(tr U)=0`.

The left side is the sum of squared absolute values of the entries of `U−I`; hence `U=I`. Here `*` denotes conjugate transpose.

Finally `g=T_(affShift g) D_(affSlope g)`, so the unitary representation of `g` equals its representation of the dilation with the same slope. This factorization is the positive classification exposed by translation rigidity.

## Dependency and scope audit

`BiarithmeticGeometry.finite_affine_unitary_rigidity` treats a continuous real family and uses contraction to zero. This result replaces continuity by the rational translation group law and finite-dimensional trace pairing. It is algebraic representation-theoretic calibration; no novelty claim.

Any covariant finite-dimensional negative unitary component is therefore blind to translations. Constructing such a component from an arbitrary finite-index affine kernel remains a separate gap; the existing finite-rank correction theorem does not supply covariance. O5 remains open.

Without unitarity, [translations are unipotent with exponent at most the dimension](finite-rational-affine-representations-have-unipotent-translations.md), also formalized.

## Lean certificate

Module: `GaloisForLFunctions/BiarithmeticGeometry/Affine/FiniteRationalUnitaryRigidity.lean`.

- `finite_rational_affine_translation_trace`
- `finite_rational_affine_unitary_rigidity`
- `finite_rational_affine_unitary_factors_through_dilations`

Direct leaf check passed with `lake --old env lean`. All three transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Imported by the BiarithmeticGeometry umbrella.
