# Xi-descent far-field all-rung loop-drain universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL DESCENDED ALL-RUNG DRAIN; LITERATURE AUDITED]`

## Lean-derived conjecture

For every Xi point `ρ` with `1 < Re ρ` and every dyadic rung `k`, there is a positive radius such
that every smaller circle around `(ρ - 1/2)²` has:

- zero additive Xi-descent loop charge;
- trivial multiplicative deck character;
- trivial local Xi-descent carrier charge;
- trivial original Xi carrier charge.

This upgrades the corpus's pointwise Euler-product far-field anchor and its local all-rung descent
triangle to an exact all-rung loop drain in the descended coordinate.

## Corpus inputs

- `xi_ne_zero_of_one_lt_re`
- `carrierCharge_eq_one_of_ne_zero`
- `carrierCharge_xiDescent_center_sq_allRungs`
- `deckChar_loopCharge_xiDescent_center_sq`
- `deckChar_injective`

## Proof plan

1. Embed `Re ρ > 1` into the right half-plane required by quadratic descent.
2. Use the Euler-product zero-free theorem to trivialize Xi's local carrier charge.
3. Transport triviality to the descended carrier at every rung.
4. Use the local-loop triangle to identify the loop deck character with that trivial charge.
5. Apply injectivity of the deck character to force the additive loop charge itself to zero.

No numerical computation is used.

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof searches covered the Riemann Xi functional equation, zero-free regions for zeta,
argument-principle zero counts, winding numbers, local monodromy of roots, and quadratic descent
through the critical-line coordinate.

Nearest sources:

- Riemann Xi background and functional equation, NIST DLMF §25.4:
  <https://dlmf.nist.gov/25.4>
- Mossinghoff--Trudgian--Yang, *Explicit zero-free regions for the Riemann zeta-function*,
  arXiv:2212.06867:
  <https://arxiv.org/abs/2212.06867>
- Kowalczyk, *Locating all the zeros of an analytic function in one complex variable*,
  J. Comput. Appl. Math. 2002, uses the argument principle and winding number for zero counts:
  <https://doi.org/10.1016/S0377-0427(01)00371-5>

These sources contain the classical ingredients separately. No source found states that every
`Re ρ > 1` Xi point, after the quadratic descent `(ρ-1/2)²`, has zero additive small-loop charge
at every dyadic rung together with trivial deck character and both local carrier charges.
Novelty claim is restricted to this exact four-way all-rung drain.

## Lean target

`formal/GaloisForLFunctions/RHTower/XiDescentFarFieldAllRungLoopDrainUniversalityLaw.lean`

## Verification

- source proof exact and warning-free:
  `lake env lean GaloisForLFunctions/RHTower/XiDescentFarFieldAllRungLoopDrainUniversalityLaw.lean`
- imported by `formal/GaloisForLFunctions/RHTower.lean`
- final module and umbrella builds deferred to terminal audit
