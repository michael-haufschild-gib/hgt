# XF1 Square Tests Sit Outside The Standard Weil Test Class

- **ID:** xf1-square-tests-outside-weil-class
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), explicit-formula bridge obstruction
- **Source:** random formula-graph node 95/100, `XF1` in `docs/consolidated/revision01/formulas-graph.md`
- **Statement:** The shifted reciprocal-seam square tests required by the proof route are not admissible test functions for the standard Weil/Guinand explicit formula by direct substitution. They have a nonintegrable hard-edge pole at `t=0` and only polynomial decay at infinity.

## Goal

Close a false shortcut in the proof-route task "derive `Q_0/Q_1` from the fused explicit-formula expression." The explicit formula is the right source object, but the shifted square-test functions live at the reciprocal hard edge. A bridge theorem must therefore prove a regularized limiting transfer, not merely plug the square tests into `XF1`.

## Gates

- [x] 0 -> 1 in-progress: random formula selected and checked against existing square-test cards
- [x] 1 -> 2 fully-proven: endpoint exponent proof complete
- [x] 2 -> 3 formalized: `RHTower/SeamSquareTestNotAdmissible.lean`, axiom audit PASS.
- [ ] 3 -> 4 publication-ready: integrate into the explicit-formula bridge section

## Proof

[PROVED HERE]

Use the on-line reciprocal coordinate

```text
y = -(\rho - 1/2)^(-2) = gamma^(-2)
```

when `rho = 1/2 + i gamma`. The shifted square-test forms become

```text
Q_0[p] = sum_rho y_rho p(y_rho)^2,
Q_1[p] = sum_rho y_rho^2 p(y_rho)^2.
```

Thus the corresponding zero-side test functions in the explicit-formula variable `t=gamma` have the form

```text
h_{r,p}(t) = t^(-2r) p(t^(-2))^2,        r = 1,2,
```

with `r=1` for `Q_0` and `r=2` for `Q_1`.

Let `p` be a nonzero real polynomial of degree `d`. Near the hard edge `t=0`,

```text
p(t^(-2)) = a_d t^(-2d) + lower powers,
```

with `a_d != 0`, hence

```text
h_{r,p}(t) ~ a_d^2 |t|^(-(2r+4d)).
```

Since `2r+4d >= 2`, `h_{r,p}` is not locally integrable at `0`. In particular it is not continuous, not Schwartz, and cannot be inserted into any standard explicit-formula version whose archimedean term is an ordinary integral against a locally bounded gamma-factor kernel.

At infinity, if `j` is the order of vanishing of `p` at `0`, then

```text
p(t^(-2)) = a_j t^(-2j) + O(t^(-2j-2)),
```

so

```text
h_{r,p}(t) ~ a_j^2 |t|^(-(2r+4j)).
```

This is only polynomial decay. Therefore `h_{r,p}` is not a Schwartz test function even away from the hard-edge pole.

The only exception is the zero polynomial, which gives the zero test. Hence every nontrivial shifted reciprocal-seam square test lies outside the direct standard Weil/Guinand test class.

## Consequence For The Proof Route

The proof route should not phrase the bridge as:

```text
plug h_{r,p}(t)=t^(-2r)p(t^(-2))^2 into XF1.
```

That expression is not an admissible input. The required theorem must instead specify a canonical hard-edge regularization, for example a family such as

```text
h_{r,p,eps}(t) = (t^2 + eps^2)^(-r) p((t^2 + eps^2)^(-1))^2,
```

or another completed boundary prescription, and then prove:

1. the explicit formula is valid for the regularized family;
2. the zero side converges to the shifted square-test form `Q_r`;
3. the archimedean and prime sides have controlled finite limits after the pole cancellation;
4. positivity survives the limiting process.

This is a bridge obstruction, not a new detector. It sharpens the open core: `XF1` is the source channel, but the square-test calculus lives beyond the naive test-function boundary.

## Computation

The exponent audit is archived at:

- `computations/2026-06-21-conway-xf1-square-test-class.py`
- `computations/2026-06-21-conway-xf1-square-test-class.txt`

## Log

- 2026-06-21 -- Conway: created from random formula-graph node 95/100 (`XF1`) after checking prior square-test and pole-cancellation cards. Prior work said the explicit-formula residue must be positive on square tests; this card isolates the missing admissibility/regularization theorem needed before `XF1` can be applied to those tests.

## 2026-06-24 canonical finite-part continuation

`even-seam-finite-part-canonicality.md` supplies the next admissibility layer after this obstruction. The square tests still cannot be plugged directly into the standard Weil class, but an even seam cutoff has a regulator-independent Hadamard finite part under the completed source/tail hypotheses, and the resulting boundary form is necessarily Hankel.

This does not prove RH or the scalar Weyl sign. It says the regularized Weil-pullback route has a well-defined source-domain object, so any remaining sign must come from a source theorem rather than from choosing a convenient regulator.

## 2026-08-16 Lean closure

`RHTower/SeamSquareTestNotAdmissible.lean` proves the card unconditionally.

`seamSquareTest r p t = (t^(2r))^(-1) * p((t^2)^(-1))^2` is the zero-side test `h_(r,p)`.

- `seamRevPoly` is the coefficient reversal of `p`, with `seamRevPoly_eval_zero` giving
  `(revPoly p)(0) = leadingCoeff p` and `seamRevPoly_eval_of_ne_zero` the identity
  `(revPoly p)(u) = u^d * p(u^(-1))` for `u != 0`.
- `seamSquareTest_eq` is the card's exact hard-edge exponent:
  `h_(r,p)(t) = (revPoly p)(t^2)^2 / t^(2r + 4d)`.  Since `(revPoly p)(0) = leadingCoeff p != 0`,
  the pole order is exactly `2r + 4d`, which is at least `2` for `r >= 1`.
- `not_intervalIntegrable_seamSquareTest` is the decisive obstruction: for `r >= 1` and `p != 0`,
  the test is not interval integrable on any interval containing the seam.  The proof bounds
  `|h|` below by `(leadingCoeff p)^2 / 2 * |t|^(-1)` near the seam and applies
  `not_intervalIntegrable_of_sub_inv_isBigO_punctured`.  Not being locally integrable, the test is
  in particular neither continuous nor Schwartz and cannot be substituted into an explicit formula
  whose archimedean term is an ordinary integral.
- `seamSquareTest_decay_exact` and `seamSquareTest_decay_limit` are the infinity clause:
  `t^(2r) h_(r,p)(t) = p((t^2)^(-1))^2 -> p(0)^2`, so the decay is exactly polynomial of order
  `2r` and never rapid.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
