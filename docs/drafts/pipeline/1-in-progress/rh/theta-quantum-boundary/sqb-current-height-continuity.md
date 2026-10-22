# SQB complete current: continuity in height

Status: height continuity, full rectangle-current convergence and positive
band consequences are formalized and audited. RH remains open; frontier
map is read-only.

Full chain: original modular source → independent current comparison or
full-Xi spectral occurrence → critical-line classification → RH.

The complete current-period limit E₀(y) is continuous in height, including
heights with common source zeros. The signed source-acceleration formula
already gives the full integrated limit and a second-derivative majorant.
At a fixed height, second horizontal derivatives vanish at almost every
common zero: the exceptions to each derivative's vanishing on its zero set
are isolated points and hence countable. Apply this fact twice. Away from
nodes the quotient is continuous; at nodes with zero acceleration its
source majorant tends to zero. A compact height neighborhood gives a common
integrable bound, permitting dominated convergence in height.

- [x] Broad OR corpus searches: zero sets/calculus and integral continuity.
- [x] Formalize the countable-exception derivative lemma.
- [x] Prove source acceleration quotient is height-continuous almost everywhere.
- [x] Prove complete current-period limit is continuous at every positive height.
- [x] Prove full original rectangle-current convergence through common zeros.
- [x] Extract positive-height-band consequences without a uniform lower bound.
- [x] Audit scratch/source, targeted build, axioms, umbrella wiring, index and lint.
- [ ] Derive the missing uniform quotient-area comparison from original source structure.

Continuity and a positive band do not by themselves give the quotient-area
quarter inequality or full-Xi spectral occurrence. No source-node exclusion,
analyticity, nodal measure formula, or uniform positive current is assumed.

Strict positivity at one height now gives a closed positive-height band
with E₀≥E₀(y₀)/2 and positive limiting rectangle mass. The actual full
horizontal-current integral over that rectangle has a fixed positive
lower bound for every sufficiently small regulator. Zero limiting mass
on a nondegenerate band is equivalent to zero E₀ at every height in it.
A nonflat original common node supplies one proved positivity trigger;
its existence remains unasserted.

All 24 public theorems passed scratch/source checks, the sole-target final
build and standard-only axiom inventories. All are indexed once and wired
once. Formal lint passed. No owned compiler remains.
[Complete proof and audit](../../../3-formalized/sqb-current-height-continuity.md).
