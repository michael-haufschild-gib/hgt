# Quantum-clock cycle residue factorization

- **ID:** `quantum-clock-cycle-residue-factorization`
- **Stage:** 3-formalized
- **Type:** STRUCTURAL QRF THEOREM / SUPPORTING MACHINERY
- **Scientific status:** `[PROVED] [FORMALIZED] [NOVELTY UNVERIFIED] [NOT YET A GRAVITY LAW]`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/QuantumClockCycleFactorization.lean`

## Theorem

Let `P` be a perspective-neutral normed state space and `A,B,C` three possibly different clock
perspective spaces. For each clock `X`, let

```text
reduce_X : P -> X,
lift_X   : X -> P.
```

Let `V_1,V_2,V_3 : P -> P` be physical continuous linear evolutions. Define the physical frame
change from source `X` to target `Y` by

```text
S^V_(X->Y) = reduce_Y o V o lift_X.
```

If the intermediate reductions are exactly reversible on `P`,

```text
lift_B o reduce_B = I_P,
lift_C o reduce_C = I_P,
```

then the typed three-clock cycle factors exactly:

```text
S^V1_(B->A) o S^V2_(C->B) o S^V3_(A->C)
  = reduce_A o (V_1 o V_2 o V_3) o lift_A.                   (1)
```

Consequently:

1. if all `V_i=I_P` and `reduce_A o lift_A=I_A`, every pure QRF triangle is exactly `I_A`;
2. if `V_1 o V_2 o V_3=I_P`, the represented physical cycle is exactly `I_A`;
3. intermediate clock-coordinate choices cannot create a cyclic residue. Every residue in `(1)`
   is the base-clock representation of physical perspective-neutral evolution.

No common observer-space identification is assumed. The theorem is typed across distinct spaces
`A,B,C`.

## Physics provenance

Chen--Giacomini define a pure X-QRF change by composing perspective-neutral reduction maps and
allow a constraint-preserving physical unitary between them:

```text
S_(B->A) = T_A T_B^dagger,
S^V_(B->A) = T_A V T_B^dagger.
```

The formal theorem extracts the exact cycle consequence of this structure. It is also compatible
with the perspective-neutral QRF construction of Höhn and collaborators.

Primary sources:

- L.-Q. Chen and F. Giacomini, *Quantum Reference Fields Transformations in Linearized Quantum
  Gravity*, <https://arxiv.org/abs/2606.09344>.
- A. Vanrietvelde, P. A. Höhn, F. Giacomini, and E. Castro-Ruiz, *A change of perspective:
  switching quantum reference frames via a perspective-neutral framework*,
  <https://arxiv.org/abs/1809.00556>.

## Scientific boundary

Equation `(1)` is necessary supporting machinery for
`docs/drafts/pipeline/0-backlog/gravity-is-clock-change-holonomy.md`, but it does not identify
`V_i` with gravitational transport, derive a connection, reconstruct Riemann curvature, certify a
quantum mediator, or invoke hypertranscendence.

The strongest honest interpretation is a separation theorem:

> Pure clock-coordinate changes close exactly. Any nontrivial closed clock residue must come from
> physical evolution, imperfect reduction, a boundary operation, or an anomaly.

Calling the right side of `(1)` gravity before deriving its physical carrier would be circular.

## Lean declarations

- `physicalClockFrameChange`
- `physicalClockFrameChange_cycle_factorization`
- `pureClockFrameChange`
- `pureClockFrameChange_cycle_eq_id`
- `physicalClockFrameChange_cycle_eq_id_of_evolution_cycle`

## Verification

- Direct file check:
  `lake env lean GaloisForLFunctions/HTGeometry/QuantumClockCycleFactorization.lean`
- Final module audit:
  `lake build GaloisForLFunctions.HTGeometry.QuantumClockCycleFactorization`
- Axiom audit for all three theorems:
  `[propext, Classical.choice, Quot.sound]`
- Formal lint: passed.
- `git diff --check`: passed for touched files.

## Gates

- [x] 0 -> 1: typed QRF cycle and exact hypotheses isolated
- [x] 1 -> 2: dependency-closed proof completed
- [x] 2 -> 3: direct Lean check, module build, axiom audit, and lint passed
- [ ] 3 -> 4: source-derived gravitational `V_i`, physical novelty, and Nature-scale consequence

