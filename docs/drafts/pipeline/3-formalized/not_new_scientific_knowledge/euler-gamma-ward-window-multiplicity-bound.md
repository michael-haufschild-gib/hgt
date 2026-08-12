# Euler--Gamma Ward window multiplicity bound

- **ID:** `euler-gamma-ward-window-multiplicity-bound`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT A 75% THEOREM]`
- **Lean file:**
  `formal/GaloisForLFunctions/RHTower/XiWardSourceWindowMultiplicity.lean`
- **Parent research card:**
  `../../1-in-progress/zeta23-beyond-bandwidth-one-proportion.md`
- **RH used:** no
- **Computation used as proof:** no

## Statement

Let `S` be any finite set of multiplicity copies of strict-right upper Xi zeros, with centered
points `a_q+i gamma_q`.  Fix `h>1/2`, a height center `c`, and a window radius `delta`.  If

```text
(gamma_q-c)^2 <= delta^2       for every q in S,
```

then

```text
card(S) * 2h / ((h+1/2)^2+delta^2)
  <= B_EG(h,c),

B_EG(h,c)
 = 2 Re[ 1/s + 1/(s-1) + (Gamma_R'/Gamma_R)(s)
         - sum_(n>=2) Lambda(n)n^(-s) ],
s=h+1/2+ic.
```

The right side lies in `Re s>1`, so its von Mangoldt series is absolutely convergent.  The lower
quantum is uniform for every `a_q>0`, including arbitrarily small positive displacement.  Critical
line multiplicity is absent by construction because the index type contains only strict-right
copies.

## Proof

At `w=h+ic`, one Schwarz-pair Ward response is the sum of two positive Lorentzians.  The term
centered at `gamma_q` is bounded below by

```text
2h / ((h+1/2)^2+delta^2),
```

using `h<=h+a_q`, `a_q<1/2`, and the window hypothesis.  Summing over `S` gives the left side.
Every remaining Schwarz-pair term has positive real part, so the finite sum is at most the complete
absolutely convergent Ward response.  Functional-equation reflection absorbs its complementary
divisor and boundary self-symbol, leaving the explicit source-only majorant `B_EG`.  Chaining the
three inequalities proves the theorem.

## Formal theorem map

| Content | Declaration |
|---|---|
| finite packet is below complete positive Ward series | `finite_sum_re_xiAntiCausalWardSchwarzPairResponse_le_continued` |
| multiplicity-exact window quantum bounded by Euler--Gamma source | `finite_strictRight_window_card_mul_quantum_le_sourceArithmetic` |

Dependencies carrying analytic content are already unconditional corpus theorems:
`interior_pair_quantum` and
`re_continuedXiAntiCausalWardResponse_le_sourceArithmetic`.

## Exact boundary

This is the requested source-faithful submicroscopic separator, but it is a first-moment estimate.
The source majorant retains the universal Gamma baseline and grows like `log |c|` on a fixed
interior line.  Covering a dyadic height interval therefore yields census order `T log T`, without
the factor `1/8` needed to prove `N_off<=N/4`.  A 75% theorem still requires a centered quadratic
Euler--Gamma correlation bound or a height-local index estimate.  The exact Ward reduction in the
parent card shows the required quadratic source constant: localized real-channel energy must be
at most `(pi/2+o(1))N(T,2T)`, against a `(4pi-o(1))` deposit per right-upper copy.

The mathematical proof is a direct finite-sum consequence of existing Lorentzian positivity and
source absorption.  It closes an important formal interface but is not claimed as new external
scientific knowledge.

## Verification

- targeted module build passes;
- exported axiom audit: `[propext, Classical.choice, Quot.sound]` only;
- formal lint reaches this module through `GaloisForLFunctions.RHTower`; repository-wide lint is
  currently red only on pre-existing unreachable modules listed by the lint command.
