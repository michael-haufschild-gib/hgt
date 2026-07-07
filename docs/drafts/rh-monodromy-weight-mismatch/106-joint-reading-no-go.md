# 106 — The joint {σ_p} × ∂_s reading, attacked to a decision [ROUTE KILLED]

Formal home: `formal/GaloisForLFunctions/RHTower/JointReadingNoGo.lean`
(all endpoints axiom-clean: `[propext, Classical.choice, Quot.sound]`).

Doc 105 closed with "the joint reading" as the one place new RH mathematics might come from. This
document attacks it. Under the lane's own constraints — no flow, no re-expression, not the known
Weil route — it does not survive. The attack angle (entropy-selected) was the q62 transposition;
the outcome is a precise structural kill.

## 1. What the direction is

The hgt mission's native frontier is the weld where `∂_s` (archimedean generator, the functional
equation) and `{σ_p}` (the prime/Euler side) interact. A "joint reading" is a single constraint
coupling both, hoped to locate a strip zero where each side alone fails: the ∂_s side is
Klein-four blind (`WeightMismatchRefutation`), the {σ_p} side is real-axis blind
(`LandauShadowNoGo`, doc 105), the seam datum is the rung itself (`SeamCongruence.seam_iff_rung`).

## 2. The q62 transposition, and why it needs unbounded order

The one mechanism in this repository that kills an off-line object without positivity is the q62
weight mismatch (`Bottcher/Q62.lean`): an automorphism `σ` fixes the base `G` and scales the
target `F ↦ ζ·F`, where `ζ` has **unbounded order**; a relation `P(F,G)=0` must be `σ`-fixed, but
its graded pieces transform by distinct characters `ζ^k` and vanish one weight at a time. The
transposition to ξ needs an automorphism of the ξ world that is (i) external and base-fixing and
(ii) of unbounded order.

## 3. The kill: the pinned joint symmetry has exponent 2 [PROVED HERE]

At a pinned configuration — no Bohr flow, no continuation across the wall — the divisor
symmetries the two constraints supply are exactly two involutions:

- `feEquiv` (`s ↦ 1 − s`): the ∂_s functional equation (`jointSym_feEquiv_order_invariant`);
- `cjEquiv` (`s ↦ s̄`): the {σ_p} reality of the real Dirichlet coefficients
  (`jointSym_cjEquiv_order_invariant`).

They commute (`feEquiv_cjEquiv_commute`), so the group they generate — the whole pinned joint
symmetry `jointSym` — is the Klein four-group `{1, feEquiv, cjEquiv, feEquiv·cjEquiv}`, of
**exponent 2**: every element squares to the identity (`jointSym_sq`) and has order at most `2`
(`jointSym_orderOf_le_two`). Its third nontrivial element is the critical-line reflection
`s ↦ 1 − s̄`, which also fixes the divisor (`jointSym_feEquiv_cjEquiv_order_invariant`) — the group
genuinely acts on ξ's zeros.

`no_q62_unbounded_weight`: **the pinned joint reading contains no symmetry of order exceeding 2**,
so it cannot furnish the unbounded-order weight the q62 mechanism requires; the demand fails
already at `d = 2`.

## 4. Why the unbounded-order symmetry that exists is useless

There is one symmetry of unbounded order in the picture: the Kummer deck group `ℤ/2^k` of the
tower. But its weight around a zero of multiplicity `m` is `exp(2πi·m/2^k)` (`XiDeck`,
`DeckMultiZero`) — the multiplicity itself. Using it as the q62 `ζ` is circular: it presupposes
`m mod 2^k`, which is exactly `RHLadder k`, the thing to be proved. So the two properties the
mechanism needs are **disjoint** here: external-and-base-fixing (the joint symmetry) has exponent
2; unbounded-order (the deck) is internal and tautological. No single automorphism is both. The
weight-mismatch engine has nothing non-circular to run on.

## 5. The other realizations of the direction, and what remains

The direction has exactly these ways to couple the two sides at the constraint level, and each is
closed under the lane's rules:

| Coupling | Status |
|---|---|
| q62 weight mismatch (symmetry) | dead — exponent 2 external, tautological internal (§3–4, here) |
| explicit formula, positive form (Weil) | the known route — excluded by the novelty gate (approach §2.4) |
| explicit formula, identity form | an identity; no localization (carries the count, not the position) |
| Bohr / Kronecker `T^∞` lift | a vertical-translation flow — refused by the mantra |
| de la Vallée Poussin `σ > 1 − c/log|t|` | a height flow, and a zero-free region carries no parity |

Every realization is a symmetry (exponent 2, dead), a positivity (real-axis blind, doc 105), the
known Weil route (excluded), or a flow (refused). The flow-free, non-Weil joint reading is closed.

What a rescue would require is now sharp: a coupling of `{σ_p}` and `∂_s` that is **none of**
symmetry, positivity, the explicit formula, or a flow — a genuinely new object in the category
`𝓜⁺`, not among the mechanisms the program currently has. That is not a result; it is the precise
shape of the hole. The next construction to attempt is exactly such an object — for instance a
`{σ_p}`-graded refinement of the divisor that is finer than the multiplicity yet not a symmetry
character (so it escapes §3) and not a positivity (so it escapes doc 105) — read at one pinned
annulus. Until such an object exists, the joint reading is a named frontier, not a lever.
