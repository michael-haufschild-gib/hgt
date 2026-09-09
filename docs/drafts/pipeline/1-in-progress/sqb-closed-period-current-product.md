# SQB full closed-period resistance/current product

Status: closed-period product theorem and all Lean audits passed.
RH remains open; frontier map is read-only.

Full chain: original modular source → independent current comparison or
full-Xi spectral occurrence → critical-line classification → RH.

At every positive height of the actual source with 0<μ<1/4, there are
r>0 and c>8 such that 0<ε≤r implies

    c ≤ (N+1)² × periodResistance_ε × periodCurrentEnergy_ε.

Every finite product limit satisfies the same strict level-scaled
threshold. The full product never tends to zero, including when the
current factor does. The complete current has a lower rate strictly above
8/((N+1)² × periodResistance_ε) for all sufficiently small regulators.

The proof retains the complete augmented unit source and both arcs on its
closed level-period curve. The same squared chord is charged to each arc;
their combination gives four times the chord as a lower bound for the
total product. Original slice positivity and zero means produce a fixed
negative correlation at every height. Its small-regulator chord margin
and exact integer-period scaling supply the stated floor.

- [x] Broad OR searches for joint limits, capacity, closed curves and zero means.
- [x] Prove the two-arc inequality with every original source coordinate retained.
- [x] Prove actual level-period closure and full-period resistance/energy splitting.
- [x] Produce a strict small-regulator product floor at every positive height.
- [x] Extract the consequences for finite product limits and zero limiting current.
- [x] Audit scratch/source, targeted build, axioms, wiring, index and lint.

Dependency-closed proof and complete 21-theorem audit:
[formalized result](../3-formalized/sqb-closed-period-current-product.md).
Lean module: `GaloisForLFunctions.RHTower.SelbergMaassClosedPeriodProduct`.

No source node, nodal order, or bounded joint product is assumed to exist.
A positive product does not imply positive limiting current when resistance
diverges. Common flat nodes and zero current remain unexcluded. The
quotient-area quarter comparison and independent full-Xi occurrence remain
open. The full SQB route is retained.
