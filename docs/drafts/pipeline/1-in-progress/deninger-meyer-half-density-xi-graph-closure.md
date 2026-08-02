# Deninger--Meyer half-density Xi graph closure

## Status

Paper proof and unconditional Lean formalization complete. This card strengthens the canonical
half-density continuity selector from boundedness to exact graph-closure behavior. Route L remains
open on construction of a source-selected proper singular domain that excludes the graph-null
Gaussian orbit without selecting divisor displacement.

## Route

Route L (Deninger/Meyer arithmetic cohomology).

## New conjecture

Let `H_M` be literal all-weight Meyer cohomology, let `B_{1/2}` be its canonical half-density
completion, let `j : H_M -> B_{1/2}` be the completion map, and let `E_rho` be the actual zeroth Xi
evaluation. Define the algebraic graph relation

```text
G_rho = range (u |-> (j u, E_rho u)) <= B_{1/2} x C.
```

Then:

1. if `Re rho = 1/2`, `G_rho` is contained in the closed graph of the already constructed
   continuous extension, so the vertical fibre of `closure G_rho` is zero;
2. if `Re rho != 1/2`, the vertical fibre of `closure G_rho` is all of `C`;
3. therefore the algebraic Xi evaluation is sequentially closable through `j` exactly on the
   critical line.

The off-line claim has an explicit target-free witness. Put `z = rho - 1/2`,
`a = Re z != 0`, `c_n = n a`, and let `u_*` be the log-Gaussian Meyer class. Then

```text
u_n = exp (-c_n z) * V_{c_n} u_*.
```

Centered-flow isometry gives

```text
norm (j u_n) = exp (-n a^2) * norm (j u_*) -> 0,
```

while the exact Xi eigencharacter gives

```text
E_rho(u_n) = E_rho(u_*) != 0.
```

Complex scaling then puts `(0,y)` in `closure G_rho` for every `y : C`.

## Why this moves the frontier

This is stronger than another RH-equivalent boundedness wrapper. It classifies the canonical
closed relation forced by the literal Deninger source. Off-line Xi evaluation is not merely
unbounded: every scalar becomes a vertical value over zero. Hence no closed or closable
single-valued operator on the full half-density source image can repair admission. Any successful
singular Gamma/Hellinger transport must restrict its source domain before completion and must
exclude this explicit Gaussian graph-null sequence by a source-derived condition.

## Non-overlap audit

Existing Meyer modules prove the Gaussian nonvanishing orbit criterion and the half-density
continuity selector. Existing maximal-verticality modules concern prime codiagonals or completed
Hellinger--Gamma cofaces, not actual Xi evaluation on literal Meyer cohomology. Repository and
formal-index searches found no Xi graph-closure classification for the half-density completion.

## Lean targets

- [x] define the actual Xi graph linear map and range relation;
- [x] construct the scaled Gaussian graph-null sequence;
- [x] prove its completion coordinate tends to zero;
- [x] prove its Xi coordinate is constant and nonzero;
- [x] prove full verticality of graph closure off line;
- [x] prove zero vertical fibre on line;
- [x] characterize sequential closability exactly;
- [x] prove every closed relation retaining an off-line graph is maximally vertical;
- [x] exclude every closed single-valued extension of the full off-line source graph;
- [x] wire `RHTower` umbrella.

Formal module:
`formal/GaloisForLFunctions/RHTower/DeningerMeyerHalfDensityXiGraphClosure.lean`.

Verification: direct `lake env lean` and targeted `lake build
GaloisForLFunctions.RHTower.DeningerMeyerHalfDensityXiGraphClosure` pass. Axiom audit of maximal
verticality, critical single-valuedness, no closed single-valued extension, and exact closability
reports only `propext`, `Classical.choice`, and `Quot.sound`.

Latest global lint is blocked by unrelated shared-worktree umbrella omissions:
`BurnolCoPoissonQuotientOrder`, `CriticalHalfDensityPrimeTailResolventLaw`,
`DisconnectedProjectiveGapModuleLaw`, and `FiniteGraphTemporalCurvatureLaw`. This module is wired
into `RHTower` and contains no banned declaration.
