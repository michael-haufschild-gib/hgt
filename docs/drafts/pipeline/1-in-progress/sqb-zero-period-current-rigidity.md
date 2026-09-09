# SQB zero current-period limit: source rigidity

Status: source rigidity, nonflat-node positivity and the exceptional-source
alternative are formalized and audited.
RH remains open. Frontier map is read-only.

Full chain: original modular source → independent current comparison or
full-Xi spectral occurrence → critical-line classification → RH.

The full current limit E₀(y) is finite and nonnegative. A bounded resistance/
current product at a nodal height already forces E₀(y)=0. Determine what
this vanishing implies before attempting any rate estimate or global bound.

A fixed positive regulator in the pair-plus-phase part gives a continuous
nonnegative density. Its integral over any full period lies below E₀,
because it lies below the complete current at all smaller regulators.
Any nonzero pair or phase current therefore forces E₀>0. Consequently
E₀=0 forces all horizontal pair/phase currents to vanish, and at positive
density every component derivative has the same real radial slope.

At a common zero with nonzero horizontal source derivative, use original
C¹ derivative continuity and the already source-derived linear amplitude
bound to retain a positive regulator-gradient mass on a shrinking interval.
This forces E₀>0 without a guessed nodal measure or a pointwise-limit
interchange. Its contrapositive isolates nodes with zero first horizontal derivative
as the only nodal case compatible with zero limiting current.

- [x] Broad OR corpus discovery and source/positive-integral inspection.
- [x] Prove fixed-regulator current certificates and positive-limit detection.
- [x] Prove zero-limit pair/phase vanishing and common real radial slope.
- [x] Prove positive limiting current at original nonflat nodes.
- [x] Combine the constraints for bounded original nodal products.
- [x] Audit scratch/source, targeted builds, all axioms, wiring, index and lint.
- [ ] Derive the missing quotient-area lower bound from original source structure.

No original nodal point, nonzero node derivative or strict E₀ positivity is
assumed to exist. These are source-case constraints, not a proof of RH.

Actual exceptional Maass zero means also force E₀>0 on every zero-free
period. If E₀=0 there, unit density periodicity makes the whole height
zero-free, the normalized component derivatives vanish, and the components
are constant. This contradicts the original source's proved negative
correlation at that height. Thus every exceptional-source height has
positive E₀ or a common zero with zero horizontal first-derivative energy.
The latter case is retained; no global nodal exclusion is claimed.

All 31 public declarations pass scratch/source, sole-target build and
standard-only axiom checks. All are indexed once and wired once; repository
formal lint passed. No owned compiler remains.
[Complete proof and audit](../3-formalized/sqb-zero-period-current-rigidity.md).
Flatness concerns horizontal derivatives only, not the full gradient.
