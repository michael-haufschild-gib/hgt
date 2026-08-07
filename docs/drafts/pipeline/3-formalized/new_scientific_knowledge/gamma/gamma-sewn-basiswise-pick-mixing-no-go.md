# Basiswise quadratic Gamma loss forbids continuous operator-Pick mixing

- **ID:** `gamma-sewn-basiswise-pick-mixing-no-go`
- **Stage:** 3-formalized
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [CCM SOURCE NO-GO]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Live research card:** `../../1-in-progress/gamma-sewn-basiswise-pick-mixing-no-go.md`

## Exact theorem

On an arbitrary real Hilbert space with an arbitrary Hilbert basis, let `T_x` be bounded operators
which converge strongly to the identity on each basis vector at the zero-aperture boundary. If
their normalized operator-valued Pick cross defects obey Cauchy--Schwarz and every basiswise
normalized diagonal defect tends to zero, then `T_x=I` at every positive aperture. Operator-norm
continuity is a sufficient specialization, not a hypothesis of the strongest theorem.

For the actual Gamma-sewn Möbius multiplier, exact quadratic contact makes every basiswise
normalized defect tend to zero. Therefore there is no continuous operator-Pick family—of any
dimension and with arbitrary off-diagonal entries—whose prime basis marginals retain those actual
Gamma multiplier norms. Strict interior Gamma loss contradicts the forced identity.

## Proof certificate

For fixed interior `x` and basis vector `e_i`, test Pick Cauchy--Schwarz with
`h=e_i-T_x^*e_i` at `x` and `e_i` at a moving aperture `y->0+`. Moving diagonal defect tends to
zero. Cross defect tends to `||h||^2/(1-exp(-x))`. Hence `h=0`. Totality gives `T_x^*=I` and
`T_x=I`. Actual Gamma marginal norm is strictly below one at positive aperture, contradiction.

This proof uses neither finite dimension nor a uniform basis limit. Parent boundary mechanism is
classical operator-valued Caratheodory--Julia theory; source-specific impossibility and escape
classification remain novelty candidates.

## Formal certificate

`HTGeometry/BasiswiseBoundaryPickRigidity.lean` proves the dimension-free law.
`RHTower/GammaSewnBasiswisePickMixingNoGo.lean` proves the actual common-aperture Gamma defect
limit and both strong-boundary and norm-continuous no-existence theorems. Targeted module build and
ordinary-axioms audit pass.

## Stage-3 Lean certificate

```text
HTGeometry.continuousLinearMap_eq_id_of_basiswise_boundaryPick
RHTower.tendsto_gammaSewnMobius_commonAperturePickDiagonal_nhdsGT_zero
RHTower.not_exists_gammaSewnMobius_basisMarginal_commonAperturePickFamily
RHTower.not_exists_continuous_gammaSewnMobius_basisMarginal_commonAperturePickFamily
```

in `HTGeometry/BasiswiseBoundaryPickRigidity.lean` and
`RHTower/GammaSewnBasiswisePickMixingNoGo.lean`.  The separate certificate card
`../gamma-sewn-basiswise-pick-mixing-no-go.md` records the same declarations.

Every declaration named above was resolved against the built Lean tree and `#print axioms`
reported only `propext`, `Classical.choice`, `Quot.sound`.  `scripts/formal_tools.py lint`
reports no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration in the tree.
