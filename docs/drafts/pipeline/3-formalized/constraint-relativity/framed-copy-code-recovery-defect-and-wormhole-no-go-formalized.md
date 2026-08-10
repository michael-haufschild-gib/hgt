# Framed copy-code recovery defect and fixed-code wormhole no-go — formalized

- **ID:** `framed-copy-code-recovery-defect-wormhole-no-go-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `framed-copy-code-recovery-defect-and-wormhole-no-go.md`
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.FramedCopyCode` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/FramedCopyCode.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorem 2.1, exact regional admission:

1. `IsRegionalRepresentative` — **card `(2.2)`**: the coefficient comparison that an `A`-supported
   code-preserving representative must satisfy.
2. `isDiag_of_regionalRepresentative` — **card `(2.3)` boxed**: only diagonal logical operators are
   admitted by one region, so `S_A = S_B = D_d`.
3. `representative_isDiag` — the representative is forced to be that same diagonal operator.
4. `regionalRepresentative_of_isDiag` — conversely every diagonal logical operator is admitted, so
   the inclusion is an equality.

Theorem 3.1, the framed Choi class:

5. `choiState`, `dephased`, `framedClass` — **cards `(3.1)`, `(3.2)`**, in the `d`-dimensional GHZ
   sector where the whole computation lives.
6. `framedClass_diag_zero` — **card `(3.3)`**: every proper marginal of the connecting class
   vanishes.
7. `choiState_mul_self` — the framed Choi class is idempotent, i.e. a pure state.
8. `trace_framedClass_sq` — **card `(3.4)` boxed**: `Tr(κ_φ²) = 1 − 1/d`.
9. `one_sub_exp_neg_log` — **card `(3.5)` boxed**: `1 − e^{−log d} = 1 − 1/d`, the exponential form
   of the same defect.

The recovery optimum:

10. `entanglement_fidelity_le` — **card `(3.4)`**: after full dephasing the recovery only sees the
    classical labels, so its transition matrix has nonnegative rows summing to one and the
    entanglement fidelity is at most `1/d`.  This is the card's separable-Choi bound, in the form
    the dephasing channel actually forces.
11. `entanglement_fidelity_eq` — the label-preserving recovery attains `1/d`, so
    `F_e^opt = 1/d` and the chain `Tr κ² = 1 − 1/d = 1 − F_e^opt` closes.

Theorem 4.1, the skew code:

12. `skewCoherentInfo` — **card `(4.3)` boxed**: `h₂((1−γ)/2) − h₂(γ/2)`.
13. `skewCoherentInfo_strictAnti` — it decreases strictly in the damping parameter, proved from
    strict monotonicity of the binary entropy on `[0, 1/2]` rather than by differentiating.  With
    item 2's constancy of the admitted algebra (**card `(4.2)` boxed** — the θ-code admits only
    scalars), this is the card's exact-admission insufficiency.

Theorem 5.1, the fixed-code no-go:

14. `recovery_defect_bounded` — **card `(5.1)`**: every fixed finite-code recovery defect lies in
    `[0,1]`.
15. `wormholeLength`, `wormholeLength_unbounded` — **cards `(5.2)`, Theorem 5.1**: `2 log cosh(Jt)`
    exceeds every bound, so no bounded fixed-code quantity can equal it for all time.

## Scope

§6 is the literature boundary and §7 is a proposed experiment; neither is a theorem.  The card
states plainly that it proves neither gravitational backreaction nor any RH connection, and nothing
of that kind is formalized.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/FramedCopyCode.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.FramedCopyCode          # green
```
