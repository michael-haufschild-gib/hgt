# Bernstein's inequality for trigonometric polynomials, from the vendored Riesz interpolation formula

- **ID:** bernstein-from-riesz
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** vendored `QuantumAlg.Util.DirichletKernel` / `QuantumAlg.GeneralizedParamShift`
- **Statement:** a real trigonometric polynomial of degree `≤ R` bounded by `M` has derivative
  bounded by `R · M`; the corresponding increment bound holds for the sieve's exponential sums with
  constant `2π(N-1)`.

## Goal

The vendored library proves, unconditionally, M. Riesz's interpolation formula in the form

`ℓ'(0) = ∑_{μ=1}^{2R} ℓ(x_μ) · w_μ`,  `x_μ = (2μ−1)π/(2R)`,
`w_μ = (−1)^{μ−1} / (4R sin²((2μ−1)π/(4R)))`

(`QuantumAlg.dirichlet_first_identity`, stated there as the generalized parameter-shift rule).
Neither mathlib nor this corpus had Bernstein's inequality: mathlib's `Bernstein` files are the
Bernstein *polynomials* and Weierstrass approximation, and the corpus's `*Bernstein*` modules are
Bernstein-coordinate packets.  Riesz interpolation is likewise absent from both.

The inequality turns a spectral degree bound into a Lipschitz bound.  That is the direction the Bohr
and sieve layers did not have: `BohrFejerPointwise` and `BohrFejerConvergence` consume a modulus of
continuity `hmod` as an input hypothesis, and `Sieve/TrigDerivative` reaches the derivative only in
`L²` through Parseval, never pointwise.

## Gates
- [x] 0 → 1  in-progress: statement fixed, tool located, no corpus/mathlib duplicate
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized: `lake build` green, `[propext, Classical.choice, Quot.sound]` only
- [ ] 3 → 4  publication-ready — not applicable, the theorem is classical (Bernstein 1912)

## Lean

`GaloisForLFunctions/HTGeometry/TrigPolynomialBernstein.lean`

| Theorem | Statement |
|---|---|
| `sum_abs_psWeight` | `∑_{μ=1}^{2R} \|w_μ\| = R` |
| `abs_deriv_genTrigCost_le` | `\|ℓ'(t)\| ≤ R · M` given `∀ x, \|ℓ x\| ≤ M` |
| `abs_sub_genTrigCost_le` | `\|ℓ x − ℓ y\| ≤ R · M · \|x − y\|` |

`GaloisForLFunctions/RHTower/Sieve/ExpSumBernstein.lean`

| Theorem | Statement |
|---|---|
| `genTrigCost_rot` | `Re (w · S(u/2π))` is a real trigonometric polynomial of degree `N−1` |
| `norm_expSum_sub_le` | `‖S x − S y‖ ≤ 2π(N−1) · M · \|x − y\|` for `S = expSum N c` |

## Approach (as executed)

1. **Weight mass.** Signs alternate, so `(−1)^{μ−1} w_μ = |w_μ|` and the claim is
   `∑_μ (−1)^{μ−1} w_μ = R`.  Apply the vendored identity to `ℓ(x) = sin(Rx)`: its right side is
   `∑_p p·b_p = R`, and `ℓ(x_μ) = (−1)^{μ−1}` is the vendored `sin_R_mul_psPoint`.  No cosecant
   summation identity is needed.
2. **Translation.** `x ↦ ℓ(t + x)` is again a degree-`R` trigonometric polynomial with
   `a'_p = a_p cos pt + b_p sin pt`, `b'_p = −a_p sin pt + b_p cos pt`; same sup bound, and its
   derivative at `0` is `ℓ'(t)`.
3. **Bound.** `|ℓ'(t)| ≤ M ∑_μ |w_μ| = R·M`, then the mean value inequality for the increment form.
4. **Complex transfer.** For `z = S x − S y ≠ 0`, `Re(conj z · S)` is a real trigonometric
   polynomial of degree `N−1` bounded by `‖z‖·M`, and its own increment is `‖z‖²`; divide by `‖z‖`.
   Conjugating rather than normalising keeps the argument free of division in `ℂ`.

Sharpness: `ℓ = sin(Rx)` attains step 3, and the single character `S = e(t)` attains step 4.

## Novelty classification (mandatory)

**Formalization of classical mathematics, new to this corpus — not new mathematics.**  Bernstein
1912; the interpolation formula is M. Riesz 1914.  What is corpus-new is only that the corpus now
owns both, with the sharp constant, on its own `expSum` object.  Do not present it as a discovery.

It discharges no RH producer hypothesis and no `Prop` interface: those were already measured to be
re-encodings of RH, and nothing in the vendored library touches them.

## Log
- 2026-08-04 — created in 1-in-progress after the QuantumAlg vendoring audit
- 2026-08-04 — formalized, umbrellas wired, moved to 3-formalized
