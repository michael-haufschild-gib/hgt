# Tame different reduced to monogenicity (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **41** — closes the different arc.
Continues [[research/eisenstein_criterion_no_completeness_2026_08_06]].

## `TameDifferentMonogenic.lean`

- **`eisenstein_iff_addVal_eq_one`** — for a monic relation of degree the ramification index,
  *being Eisenstein* ⟺ *presenting a uniformizer*.  Each direction is one of the two valuation
  computations already proved (`addVal_eq_one_of_eisenstein_root`,
  `eisenstein_of_monic_uniformizer_root`).
- **`addVal_eval_derivative_of_monic_uniformizer_root`** — `= e − 1`.
- **`span_eval_derivative_of_monic_uniformizer_root`** — the local different is `(π^(e−1))`.

Hypotheses are now: the extension `ψ : A →+* B` of DVRs with index `e`, a uniformizer `x`
satisfying a monic relation of degree `e`, and tameness.  **No condition on the coefficients
survives.**

## The different arc (modules 36–41), for reference

36 freed the computation from the constructed polynomial shape;
37 derived the upstairs coefficient bound from Eisenstein-ness downstairs;
38 derived irreducibility of the presented element from the presentation;
39 built the strict-minimum principle for valuations of finite sums;
40 derived Eisenstein-ness itself from a monic relation at a uniformizer (**no completeness**);
41 combined them into the equivalence and the final statement.

The card's `e − 1` now rests on **monogenicity alone**.

## Gate status

`formal_tools.py lint --check-generated` **passed cleanly** this round.

## Remaining for Theorem A

1. `B = A[x]` — existence of the monic degree-`e` relation (needs completeness/Hensel).
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification (shown unavoidable in module 35).
4. Corollary B: MMP.
