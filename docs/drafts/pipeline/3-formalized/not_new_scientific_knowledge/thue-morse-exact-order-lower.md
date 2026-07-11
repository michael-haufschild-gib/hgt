# Thue--Morse exact order-two growth

- **ID:** thue-morse-exact-order
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Source:** `../../2-fully-proven/not_new_scientific_knowledge/thue-morse-entire-dirichlet-order-two.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThueMorseExactOrder.lean`
- **Statement:** The entire continuation of the shifted signed Thue--Morse Dirichlet series has
  matching unconditional upper and lower quadratic growth with leading coefficient `(log 2)/2`.

## Goal

Formalize the paper's exact order-two theorem without assuming a Hadamard-order or asymptotic
Prop. Both the Mellin and reciprocal-Gamma growth bounds are constructed from concrete estimates.

## Gates

- [x] 0 → 1  in-progress: the positive-tail, saddle-window, and Gamma-recurrence route is explicit.
- [x] 1 → 2  fully-proven: the paper proof supplies the two-sided radial argument.
- [x] 2 → 3  formalized: targeted build and axiom audit pass.
- [ ] 3 → 4  theorem certificate complete; publication integration remains editorial.

## Approach

1. Prove the infinite radial product is strictly positive and define its fixed positive unit-radius
   tail constant.
2. Split the product at the unique dyadic bracket for `x`; bound initial factors below by half their
   linear terms and the omitted tail below by the fixed constant.
3. Put `x=exp(-y)` and complete the quadratic to obtain the sharp radial lower law.
4. On the negative real Mellin axis, integrate over a unit interval around the Laplace saddle.
5. Define `thueMorseEntireDirichlet = Gamma⁻¹ · mellin`, prove it is entire and agrees with the
   shifted `LSeries` on `Re s>1`, then use the Gamma recurrence to retain a fixed positive lower
   factor at negative half-integers.
6. Split the Mellin integral at `x=1`; use the exact binary-prefix constant below `1` and a Gamma
   integral above `1` to obtain the sharp quadratic whole-plane envelope.
7. Split the reciprocal-Gamma Weierstrass product at `ceil ‖s‖+1`; use the harmonic bound on the
   finite block and a telescoping reciprocal-square bound on the regularized tail.

## Lean certificate

- `thueMorseKernel_radial_quadratic_lower`
- `thueMorseMellin_neg_real_lower`
- `thueMorseEntireDirichlet_differentiable`
- `thueMorseEntireDirichlet_eq_LSeries`
- `gamma_neg_half_inv_norm_lower`
- `thueMorseEntireDirichlet_neg_half_norm_lower`
- `thueMorseMellin_norm_le_flat_add_factorial`
- `thueMorseMellin_norm_le_exp_quadratic`
- `HilbertSchmidt.norm_Gamma_inv_le_weierstrass_envelope`
- `thueMorseEntireDirichlet_norm_le_exact_order_two_envelope`
- Target build: PASS (`8620/8620`).
- Axioms: `{propext, Classical.choice, Quot.sound}` only.

## Open core

None for the exact order-two theorem. The lower sequence and sharp global upper envelope are both
premise-free Lean declarations.

## Log

- 2026-07-11 — matching radial lower bound, negative-axis Mellin saddle bound, entire continuation,
  reciprocal-Gamma half-integer recurrence, and quadratic lower sequence formalized.
- 2026-07-11 — sharp Mellin upper envelope, global reciprocal-Gamma Weierstrass envelope, and the
  unconditional exact order-two upper theorem formalized.
