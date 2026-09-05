# Balanced arithmetic periods and the curvature endpoint gate

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); finite endpoint inference falsified
- **Source:** corpus repair grammar, coefficient-lift transgression, and literal deletion coefficients; retrieved with `formal_tools.py research` and inspected with `rg` and source reads.
- **Question:** Does simultaneous finite deletion endpoint closure force the proposed quadratic factorization curvature to vanish?

The current test concerns a finite algebraic implication, not the actual Mellin-weighted infinite source. No RH architecture or novelty claim is made.

## Exact construction and paper proof

Write `a_d(n)=1-d[d|n]`. For pairwise-coprime `p,q,r`, define the literal coefficient

`k(n)=a_p(n)a_q(n)^2+a_(pq)(n)a_r(n)^2-a_q(n)a_r(n)^2-a_p(n)a_(qr)(n)^2`.

The square identity and squarefree multiplication law give the exact positive survivor

`k=(q-1)(a_(pq)-a_q+r(a_(qr)-a_(pqr)))`.

Thus this coefficient is a linear combination of original single-modulus channels. Its single-weight endpoint vanishes whenever those endpoints vanish. This does not give vanishing when the weight is squared.

On two copies of a common period, assign weights `1+h(n)` and `1-h(n)` to the two occurrences of each residue. For every coefficient observable `f`, the endpoint is exactly `2 sum f`. The quadratic observation is exactly `2 sum f + 2 sum f h^2`. If `|h|<1`, all weights are strictly positive. This is a simultaneous statement for all observables, not separately chosen weights for separate endpoints.

For the closed Lean countermodels take `p=2`, `q=3`, `r=5`, and `L=30`. Every deletion channel whose modulus divides `30` has zero endpoint, under one shared choice of weights. The curvature coefficient has zero uniform sum by the displayed linear normal form, with `k(3)=6` and `k(6)=-6`. Set `h(3)=1/2` and all other residue perturbations to zero: the quadratic curvature is `3`. Instead set `h(6)=1/2`: it is `-3`. Both choices use only positive weights `1/2`, `1`, and `3/2`, on the literal integers `1,...,60`. The second occurrence of residue `n` is `n+30`; periodicity, not a relabelled coefficient assignment, identifies its arithmetic coefficient.

The proof does not enumerate the sixty coefficients. It uses the symbolic square and coprime product identities, the zero sum of a complete arithmetic period, and the general two-copy observation formula.

## Falsification boundary

This rejects deriving quadratic curvature annihilation from finite endpoint closure and coefficient algebra alone. It does **not** refute an additional theorem using the exact infinite weights `n^(-s)`, all moduli at once, or a proved analytic constraint. The proposed bridge must identify and prove such additional information. The finite countermodel must not be described as a counterexample to RH or to a theorem restricted to actual Mellin weights.

## Positive survivor and next mathematical obligation

The positive survivor is the exact quadratic freedom formula, valid for arbitrary period, arbitrary real perturbation at each residue, and every periodic real observable simultaneously. A perturbation at one residue changes the quadratic observation by exactly `2 t^2 f(n)`, while preserving every linear observation. This identifies the information lost by endpoint-only observation rather than merely negating one proposed implication.

The curvature's coefficient normal form also identifies a distinct issue: its **single-weight** sum is controlled by the four deletion endpoints, but its **squared-weight** sum is a different observation. Moving from one to the other requires an additional theorem. Neither a third arithmetic label nor an associative label product supplies that theorem.

These elementary mechanisms are not claimed as new mathematics or a new RH architecture. The previously audited static Dirichlet law already belongs to the classical zeta-distribution framework; see Cranston–Peltzer, [equations (5)–(9)](https://escholarship.org/content/qt4kv3q5r6/supp/r-zeta_072721.pdf). That source establishes the divisibility law, not this particular finite countermodel. A search for the exact curvature terminology supplied no novelty certificate.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionBalancedPeriodFreedom.lean`.
Namespace: `RHTower.DeletionBalancedPeriods`.

- `curvature_coefficient_linear`: arbitrary pairwise-coprime label normal form.
- `quadratic_observation` and `quadratic_observation_spike`: exact general freedom formula.
- `all_divisor_endpoints_zero`: one weight choice preserves every divisor endpoint.
- `positive_weights_closed_endpoints_opposite_curvatures`: closed existential countermodels, with no hypotheses or supplied mathematical premises.

Scratch `lake env lean /tmp/hgt-balanced-period-OvOf3g/Proof.lean` passed. Targeted `lake build GaloisForLFunctions.RHTower.EulerDeletionBalancedPeriodFreedom` passed; no umbrella build ran. The module is wired into `RHTower.lean`. Imported scratch axiom audit of the five listed capstones passed with only `propext`, `Classical.choice`, and `Quot.sound`. No added axioms, unfinished proofs, or computation certificates occur. All owned Lean/Lake handles are terminal.

The first repository-wide lint after this build found an independently created, unwired `EulerDeletionBalancedPeriodCurvatureNoGo` module. That concurrent module overlaps the coefficient normal form and positive-curvature counterexample. This module additionally keeps the two literal consecutive integer periods and proves opposite curvature signs plus arbitrary perturbation amplitudes. Neither file's existence establishes novelty. The global lint result must be reported separately from this module's successful compilation and axiom audit.

The subsequent global scan also found unwired concurrent `HTGeometry.ChronologicalTensor.FourPoint`
and `HTGeometry.ChronologicalTensor.SixPoint` modules. Global lint therefore remains unpassed in
this worktree snapshot. The checked source still matches its successful scratch file byte for
byte; scoped whitespace validation passed. No owned Lean process remains running.

## Broader corpus audit behind the test

The adjacent search manifest records ranked corpus queries and requested limits, not exhaustive hit counts. Exact proof inspections included:

| Corpus mechanism | What its proof establishes | Missing source information; resulting decision |
|---|---|---|
| `ArithmeticControlledLeibniz` | A Leibniz map with uniformly linear additive defect is fixed by its value at two. | No zero-derived map with that defect bound was constructed; no architecture claimed. |
| `ConstitutiveCoefficientLiftTransgression` | A supplied coarse cocycle's refined associator lies in a coefficient kernel; vanishing means a corrected strict lift exists. | No arithmetic coarse cocycle was produced; the generic extension theorem is not a producer. |
| `ThreeSlotExchangeabilityInformation` | Repeated independent experiments have information cost equal to repetition count times one fixed divergence. | The uniform bound is the missing input; repetition does not prove it. |
| `ConstitutivePrimitiveExecutionGenesis` and `ConstitutiveFailureAntichainQuotient` | Locally admitted integer resource laws have a canonical primitive grammar; redundant constraints preserve it. | No arithmetic admission theorem was produced. Its distinction between constraints and realizations motivated the finite redistribution test. |
| `ConstitutiveSequentialRepairHeredity` | The explicitly classical Arens topology has two strict sequential-closure stages. | No arithmetic topology or zero-selective completion follows from the toy space. |
| `PrimePrimitiveDisconnectedGrammar` | Two nonempty disjoint prime-support packets have support cardinality at least two. | Connectedness here is defined as one occupied prime; it provides no analytic zero obstruction. |

Spectral entropy results were rejected at retrieval. Integer-translation matroid results were discovery hits, not an audited arithmetic zero mechanism. The searches range over the indexed corpus; this is not a proof-body audit of every declaration in it.

Follow-up exact-phrase inspection checked `HardExclusionJointCumulants` (the displayed definition
is classical partition inversion with all higher occupation moments already zero),
`FreeDifferentialVariationalOreBasis` (a basis in an already free differential field), and the
concurrent `IntegerCarryTransport` source. The last supplies a concrete carry but proves why its
argument must be transported under multiplication; forgetting transport works only at integer
offsets where the carry vanishes. None supplies a new arithmetic zero bridge.

The earlier audit used the former OR-default search implementation. The current tool uses
spaces as AND, `--any` as OR, inner quotes for phrases, and `--exact` to disable prefix expansion.
Use the current semantics for subsequent work. The historical missing phrase hit for
`"integer carry"`, despite a module hit for `IntegerCarryTransport`, remains a reminder that
search misses do not prove absence. Pair corpus discovery with `rg` on actual statements and
proof bodies. This audit did not modify search code.
