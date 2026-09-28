# Prime--Hodge purity-cost firewall

- **ID:** `ULF-PHPCF-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **RH used:** no
- **Divisor used in the source object or bound:** no
- **Parents:** `ULF-PHIN-001`, `ULF-SCIN-001`,
  `source-horizontal-bv-complete-split-primitive-budget-firewall`,
  `ULF-DSA-002`

## 1. Big-picture mechanism

The pre-divisor prime--Hodge defect has total nuclear charge one but distributes that charge so
widely that its operator norm is strictly below one. A completed off-line relation horizon is a
rank-one projection, hence has operator norm one. The missing completion must therefore pay a
nonzero **purification cost** before any integer escape index can appear.

The literal primitive Euler collision budget is not merely below the previously used cubic zero
quantum. It is strictly below this source-to-pure-state norm cost. Thus no additive or
bounded-variation completion financed by the whole primitive Euler budget can turn the source
defect into a rank-one horizon.

This is not the missing RH theorem. Later audit shows actual anomaly-subtracted theta completion
is singular, so it should not be modeled as a homotopy whose total variation is bounded by the
primitive collision budget. The unconditional inequality survives as a firewall for any
source-generated **relative nuclear representative**, not as a completion path-length theorem.

## 2. Data

Let

```text
B = routePPrimitiveCollisionCubicTraceBudget
```

and let `T` be the actual positive prime--Hodge relative-curvature lift
`primeHodgeHistoryRelativeCurvaturePrimeLift` on `PrimeHodgeHistoryHilbert`. Then

```text
T >= 0,  T in S_1,  Tr(T)=||T||_1=1,
||T|| <= 1/3.                                                 (PCF.1)
```

Every same-history cross-prime matrix entry of `T` is nonzero. Neither `T` nor `B` uses a zero,
divisor copy, or ordinate.  An earlier draft incorrectly assigned the bound `8/(3 sqrt(35))`
from the fixed unit-aperture history defect to this source.  The source used by the firewall is
the relative-curvature lift above, and its proved `1/3` ceiling is stronger.

Let `P` be any rank-one orthogonal projection on `H`. Later specialization may take `P` to be a
unitarily transported relation-horizon defect, but the theorem below is independent of that
interpretation.

## 3. Arithmetic budget sharpening

The corpus proves

```text
B <= (115/432) sum_p 1/(p log(p)^2),
sum_p 1/(p log(p)^2) < 2.                                  (PCF.2)
```

Consequently

```text
B < 115/216.                                                (PCF.3)
```

The second inequality in `(PCF.2)` is symbolic: isolate `2,3,5`, dominate later ordered primes
by the integer tail from `7`, and integrate `1/(x log(x)^2)` from `6`. It uses no computed prime
cutoff.

## 4. Theorem: exact coordinate-free purity radius

For every positive trace-class operator `S` with `Tr(S)=1`, define

```text
rho_pure(S)=inf {||P-S|| : P is a rank-one orthogonal projection},
rho_pure,1(S)=inf {||P-S||_1 : P is a rank-one orthogonal projection}.
```

Then

```text
rho_pure(S)=1-||S||,
rho_pure,1(S)=2(1-||S||).                              (PCF.4)
```

**Proof.** For every rank-one `P`, reverse triangle gives
`||P-S||>=1-||S||`. If `P=|psi><psi|`, trace duality against the self-adjoint unitary
`2P-I` gives

```text
||P-S||_1 >= 2(1-Tr(PS)) >= 2(1-||S||).
```

Positive trace-class `S` is compact, so its norm is an eigenvalue. Take `P` to project onto a unit
eigenvector for `||S||`. In the resulting spectral decomposition, `P-S` has eigenvalue
`1-||S||` on that line and eigenvalues `-lambda_j` on its orthogonal complement. Positivity and
`Tr(S)=1` give `lambda_j<=sum_j lambda_j=1-||S||`. Hence the operator norm is `1-||S||`, while
the trace norm is `1-||S||+sum_j lambda_j=2(1-||S||)`. Both lower bounds are attained. QED.

This radius is independent of basis, prime enumeration, horizon vector, or chosen unitary between
two separable Hilbert carriers. Transporting the corpus relation-horizon projection from its
ordered-cross-prime carrier to `H` by any unitary cannot change the lower bounds.

## 5. Corollary: strict arithmetic purity-cost firewall

One has

```text
B + ||T|| < 115/216 + 1/3 = 187/216 < 1.                  (PCF.5)
```

Therefore every rank-one projection satisfies

```text
||P-T|| >= rho_pure(T)=1-||T|| >= 2/3 > B,                  (PCF.6)
||P-T||_1 >= rho_pure,1(T)=2(1-||T||) >= 4/3 > 2B.          (PCF.7)
```

In particular, there is no trace-class `R` such that

```text
P=T+R  and  ||R||_1 <= 2B.                                 (PCF.8)
```

More generally, every operator-norm continuous path `K:[0,1]->B(H)` with `K(0)=T` and `K(1)=P`
has total operator-norm variation

```text
Var(K) > B.                                                (PCF.9)
```

If `K` is absolutely continuous in `S_1`, then

```text
integral_0^1 ||K'(u)||_1 du > 2B.                          (PCF.10)
```

### Proof

From `(PCF.2)`, positivity of `115/432`, and strictness of the prime sum,
`B<115/216`. With `(PCF.1)`,

```text
B+||T|| < 115/216+1/3 = 187/216<1.
```

The first purity-radius identity gives

```text
||P-T|| >= ||P||-||T|| = 1-||T|| >= 2/3 > B.
```

The second purity-radius identity gives

```text
||P-T||_1 >= 2(1-||T||) >= 4/3.
```

Meanwhile `2B<115/108<4/3`. This proves `(PCF.6)--(PCF.8)`. Every path variation dominates
endpoint distance, proving `(PCF.9)`. Absolute continuity and the fundamental variation bound
give `(PCF.10)`. QED.

## 6. Joint reconstruction and fourth-organ prediction

The theorem fuses four structurally different organs:

1. **literal Euler formation:** `B` is the complete primitive collision capacity;
2. **Hodge/open history:** `T` is the canonical first-exit nuclear flux with all Kummer tails;
3. **prime mixing:** every history fibre retains the unsquared cross-prime Stokes kernel;
4. **theta relation horizon:** every off-line copy supplies a rank-one trace-one projection.

It predicts, before using the divisor, that any actual completion producing a horizon must do at
least one of the following:

```text
(a) spend more than the complete primitive Euler collision budget;
(b) leave the operator/trace-norm homotopy category;
(c) use signed relative cancellation whose absolute variation is not source-budget bounded; or
(d) fail to produce the rank-one horizon.
```

Thus a proposed same-boundary identity is falsified immediately if it represents completion as
`T+R` with `||R||_1<=2B`. This includes every bounded additive landing, every trace-norm coherent
finite-packet completion with two reflected copies of that budget, and every doubly
source-budget-bounded absolutely continuous nuclear homotopy.

## 7. Exact surviving RH edge

The endpoint firewall does **not** license a finite-length model of actual theta completion.
Corpus boundary transfer is singular: it closes strongly while its norm germ remains open. Hence
transporting a path-length bound through completion is the wrong category, not a missing estimate.

The surviving use of `(PCF.6)--(PCF.10)` must be relative. Construct before divisor specialization
a prime-marked pairing between open contrast history and the singular-completion ideal such that

```text
off-wall failure gives a nonzero integral index,
the index has a nuclear representative R with ||R||_1<=2B,   (PCF.11)
the completed relative class exhausts the rank-one horizon defect.
```

The firewall would then exclude that relative class. This formulation does not require a
trace-norm path from `T` to the horizon. It requires the budget to bound a source-generated
representative of the **relative obstruction**, which is the only place the endpoint inequality
can legitimately act.

`ULF-PHPTCIS-001` further proves that the relative class cannot be the closed visibility marginal:
off wall, visible and contrast charges are both strictly fractional and sum to the conserved unit.
Nor can it be the total charge, which equals one at every grade. The missing class must pair the
open contrast summand with prime-marked singular completion.

## 8. Hostile audit

- **Not a renamed subunit estimate.** Earlier `ULF-DSA-002` compares `B` with the cubic Loewner
  quantum `115/108`. Here the independently constructed prime--Hodge state supplies a different
  threshold, its exact distance from the pure-state boundary.
- **Not ordinary majorization.** Bistochastic maps contract purity, but no channel assumption is
  used. The theorem is an endpoint-distance and path-action obstruction valid for arbitrary
  operator paths. The doubled nuclear bound uses only trace duality against `2P-I`.
- **Not an RH receiver.** `(PCF.3)--(PCF.10)` are unconditional and do not quantify over Xi zeros.
  Only the future specialization in `(PCF.11)` mentions the completed relation horizon.
- **Not yet an RH proof.** No current corpus theorem constructs the prime-marked relative pairing,
  its budgeted nuclear representative, or the exhaustion clause in `(PCF.11)`.
- **Carrier mismatch exposed.** The explicitly bounded history--prime `T` here and the physical
  Pluecker source used by actual singular boundary transfer are distinct corpus objects. No
  structure-preserving intertwiner between them is proved. Arbitrary unitary transport preserves
  the pure-state radius but not prime formation or completion.
- **Corpus novelty check.** Searches for the combined constants, prime--Hodge norm/collision-budget
  comparison, and source-to-projection variation bound found the ingredients separately but no
  existing fusion theorem.
- **Literature boundary.** Quantum majorization and bistochastic-channel theory study generic
  purity monotonicity; relative-index and spectral-flow theory study endpoint crossings. Neither
  supplies this literal Euler-capacity/prime--Hodge arithmetic inequality or the relative pairing
  required in `(PCF.11)`.

## 9. Formal status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.PrimeHodgePurityCostFirewall`.  Its closed capstone
`primeHodgePurityCostFirewall` certifies the corrected source object, positivity, Schatten-one
membership, trace and trace norm one, the `1/3` norm ceiling, exact pure-state radii, strict
operator/trace-distance firewalls, and same-history cross-prime nonvanishing.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.PrimeHodgePurityCostFirewall`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module `GaloisForLFunctions.RHTower.PrimeHodgePurityCostFirewall` (45 constants, axiom audit clean).

| Claim | Lean declaration |
|-|-|
| (PCF.1) `T ≥ 0`, `T ∈ S₁`, `Tr T = ‖T‖₁ = 1`, `‖T‖ ≤ 1/3`, cross-prime entries nonzero | capstone clauses of `primeHodgePurityCostFirewall` |
| (PCF.2) `B ≤ (115/432) ∑ 1/(p log² p)`, `∑ < 2` | `routePPrimitiveCollisionCubicTraceBudget_le_primeInvLogSq`, `tsum_prime_invNatLogSq_lt_two` (used in the next row) |
| (PCF.3) `B < 115/216` | `routePPrimitiveCollisionCubicTraceBudget_lt_115_div_216` |
| (PCF.4) `ρ_pure(S) = 1 - ‖S‖`, `ρ_pure,1(S) = 2(1 - ‖S‖)` for positive trace-one `S` | `operatorPureRadius`, `tracePureRadius`, `operatorPureRadius_eq_one_sub_norm`, `tracePureRadius_eq_two_mul_one_sub_norm` (with `norm_purityRankOneProjection_sub_ge_one_sub_norm`, `traceNorm_purityRankOneProjection_sub_ge_two_mul_one_sub_norm`, attainment `exists_rankOne_operator_distance_eq_purity_cost`, `exists_rankOne_traceNorm_distance_eq_purity_cost`) |
| (PCF.5) `B + ‖T‖ < 1` | `routePPrimitiveCollisionCubicTraceBudget_add_primeHodgePuritySource_norm_lt_one` |
| (PCF.6) `‖P - T‖ > B` | `primeHodgePuritySource_operator_distance_gt_budget`, `operatorPureRadius_primeHodgePuritySource` |
| (PCF.7) `‖P - T‖₁ ≥ 4/3 > 2B` | `primeHodgePuritySource_trace_distance_gt_two_budget`, `primeHodgePuritySource_trace_distance_gt_four_thirds`, `tracePureRadius_primeHodgePuritySource` |
| (PCF.8) no budgeted additive landing | `no_budgeted_traceClass_additive_pure_landing` |
| (PCF.9) operator-path variation `> B` | `primeHodgePuritySource_operatorPath_variation_gt_budget` |
| (PCF.10) trace-class path action `> 2B` | `primeHodgePuritySource_traceClassPath_action_gt_two_budget` |
| closed capstone | `primeHodgePurityCostFirewall` |

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
