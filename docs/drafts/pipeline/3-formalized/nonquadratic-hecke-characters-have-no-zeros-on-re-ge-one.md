# Nonquadratic Hecke characters have no zeros on Re(s) ≥ 1

- **ID:** hecke-nonquadratic-nonvanishing
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke L-functions and class field theory](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL6
- **Statement:** for every number field `K`, modulus `𝔪`, and ray class character `ψ` with
  `ψ² ≠ 1`, the continued Hecke L-function is nonzero throughout `Re s ≥ 1`.

## Exact results

For `Re s > 1`, the prime-ideal Euler logarithms
`−log(1 − ψ(𝔭) N𝔭^(−s))` are summable, and their sum exponentiates to the actual
Hecke coefficient L-series. At every real `σ > 1` and `t`,

`1 ≤ |L(σ,1)³ L(σ+it,ψ)⁴ L(σ+2it,ψ²)|`.

Consequently, `ψ² ≠ 1` implies `heckeLCont 𝔪 ψ s ≠ 0` for `Re s ≥ 1`.
In particular any zero of `heckeLCont 𝔪 ψ` at `1` forces `ψ² = 1`.
No analytic premise, functional equation, or reciprocity theorem is assumed.

## Paper proof

1. A character of the finite ray class group takes values on the unit circle. At primes dividing
   the finite modulus every extended ideal value is zero. Elsewhere the squared character's
   value is the square of the original character's value.
2. The prime terms are absolutely summable and have norm below one. Summability of
   `log(1−u𝔭)` follows from differentiability at `u = 0`. Exponentiate its negative sum and use
   uniqueness of the previously proved prime-ideal Euler product to recover `L(s,ψ)`.
3. For `0 ≤ a < 1` and `|z| = 1`, expand each negative logarithm into its convergent Taylor
   series. The combined real coefficient of degree `n > 0` is
   `aⁿ(3 + 4 Re(zⁿ) + Re(z^(2n)))/n = 2aⁿ(1 + Re(zⁿ))²/n ≥ 0`.
   Apply this with `a = N𝔭^(−σ)` and `z = ψ(𝔭)N𝔭^(−it)`, whose norm is one. Sum over
   prime ideals and exponentiate to get the three-four-one lower bound. Ramified factors
   contribute zero to the logarithmic sum.
4. Suppose `ψ² ≠ 1` and `L(1+it,ψ) = 0`. Both `ψ` and `ψ²` are nontrivial, so their
   continuations are holomorphic near the points in question. As `σ → 1⁺`, each of
   `(σ−1)L(σ,1)`, `L(σ+it,ψ)/(σ−1)`, and `L(σ+2it,ψ²)` has a finite limit: respectively
   the trivial residue, a derivative, and the continued squared-character value.
   The product of their powers `3,4,1`, multiplied by `σ−1`, equals the product in the
   lower bound and tends to zero. Its norm cannot remain at least one. The open half-plane
   follows from Euler-product nonvanishing.

## Lean declarations

In [HeckeEulerLogarithmsGiveTheThreeFourOneInequality.lean](../../../../formal/GaloisForLFunctions/HeckeLFunctions/HeckeEulerLogarithmsGiveTheThreeFourOneInequality.lean):

- `summable_heckeEulerLog`
- `exp_tsum_heckeEulerLog`
- `heckeValue_sq`
- `heckeEulerLog_three_four_one_nonneg`
- `one_le_norm_heckeL_three_four_one`

In [NonquadraticCharactersDoNotVanishOnTheLineReOne.lean](../../../../formal/GaloisForLFunctions/HeckeLFunctions/NonquadraticCharactersDoNotVanishOnTheLineReOne.lean):

- `differentiableAt_heckeLCont`
- `differentiableAt_heckeLCont_one`
- `heckeLCont_line_one_ne_zero_of_sq_ne_one`
- `heckeLCont_ne_zero_of_sq_ne_one`
- `heckeLCont_one_ne_zero_of_sq_ne_one`
- `heckeLCont_one_eq_zero_implies_sq_eq_one`

The quotient limit reuses `HTGeometry.tendsto_div_sub_of_hasDerivAt_eq_zero`.
The local logarithmic Taylor argument adapts Mathlib's Dirichlet-character nonvanishing proof.

## Validation

- Proof checks pass. The Euler-log module's olean is built because the nonvanishing module imports it.
- Six transitive `#print axioms` audits pass: the exponential identity, the product lower bound,
  and all four nonvanishing/classification results depend only on `propext`, `Classical.choice`,
  and `Quot.sound`.
- Both modules are imported by `HeckeLFunctions.lean`; no umbrella is compiled.
- Both final direct source checks with `lake --old env lean` pass without warnings.

## Remaining Hecke obligations

Nontrivial quadratic characters at `s = 1` remain open. The intended analytic route uses full
Hecke continuation and Landau positivity. Full continuation, the primitive functional equation,
and Hecke Mertens statements remain on the parent card; this result does not close HL6 or HL7.
