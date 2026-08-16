# Route P joint-depth Gamma--Julia log-Krein matrix completion

- **ID:** `route-p-joint-depth-gamma-julia-log-krein-matrix-completion`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105F]`
- **Parent:** `route-p-joint-depth-gamma-julia-scalar-intertwiner-no-go.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveJointDepthGammaJuliaLogKreinMatrixCompletion.lean`

## Goal

Carry P-G105E's exact prime-log source/co-source derivative through arbitrary finite incidence,
without discarding off-diagonal entries or pretending the universal scalar block is literal Xi
landing.

## Conjecturing loop

### Conjecture 1 — log correction can be paid labelwise after determinant formation

**Rejected.** A post-determinant scalar retains neither individual prime labels nor the exact
source/co-source relation. Correct finite operation is pre-determinant congruence

```text
L = diag(log p_i),                 G ↦ L G L.
```

This preserves every incidence with exact weight
`(LGL)_ij=log(p_i) G_ij log(p_j)`.

### Conjecture 2 — operator-valued correction may create new finite degeneracies

**Falsified.** Every prime logarithm is positive, hence `det L ≠ 0`. For universal Julia--Krein
block `B` from P-G105C, `det B=-1`, and

```text
K = B tensor (L G L),
det K = (-1)^N det(L)^4 det(G)^2.
```

Therefore `det K ≠ 0 ↔ det G ≠ 0`, with no distinct-label, positivity, Hermitian, or rank
hypothesis.

## Paper proof

Diagonal multiplication gives `(LGL)_ij=L_ii G_ij L_jj`, proving exact incidence retention.
Multiplicativity of determinant gives `det(LGL)=det(L)^2 det(G)`. Every packet prime is greater
than one, so every `log p_i` is positive and `det L=∏_i log p_i` is nonzero. Kronecker determinant
law for the `2 × 2` block and `N × N` weighted Gram gives

```text
det(B tensor LGL)=det(B)^N det(LGL)^2
                  =(-1)^N det(L)^4 det(G)^2.
```

All other factors are nonzero, yielding exact degeneracy equivalence. `QED`

## Novelty and anti-theatre audit

Generic diagonal congruence is elementary. Route-specific new knowledge is that the only surviving
arithmetic weld from P-G105E is compatible with P-G105C's full off-diagonal Julia--Krein
completion, and it has an exact fourth-power prime-log Jacobian. Thus primitive promotion changes
finite volume but cannot create or remove finite degeneracy. This closes a real obstruction:
operator-valued correction does not destroy matrix-complete incidence.

The P-G186 specialization is explicitly only a construction on its window Gram. No identification
between P-G186 half-line features and literal joint-depth Xi vectors is asserted. No Stokes
orientation, stable pencil, cofinal determinant, Xi divisor identity, or RH claim is made.

## Formal status

Lean proves unconditionally:

- exact entry formula for prime-log conjugation;
- exact determinant and unconditional invertibility of every finite prime-log diagonal;
- determinant formula for arbitrary complex source matrix `G`;
- nondegeneracy equivalence with `G`;
- P-G186 finite-window specialization;
- combined P-G105F capstone with no hypotheses.

Direct Lean and target-only module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Forbidden scan and `git diff --check` pass. Module is wired;
no umbrella build was run.

## Refined open core

Give this full log-conjugated finite completion a literal signed bivariate Stokes pencil and prove
upper-half-plane stability without diagonalizing away prime/depth incidence. Then prove cofinal
compatibility and identify its limiting divisor with completed Xi.

## Higher universal principle

Primitive promotion is a multiplicative half-density. The universal Julia channel acts on channel
index, while arithmetic Radon--Nikodym derivative acts on label index; tensor separation makes the
two compatible. Earlier scalar-normalization failures were shadows of confusing these independent
functorial directions.

## Log

- 2026-08-16 — P-G105F full prime-log-conjugated finite matrix completion paper-proved and
  formalized.
