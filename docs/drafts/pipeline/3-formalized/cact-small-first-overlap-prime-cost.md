# Small actual prime cost beyond touching

Status: formalized, individually checked, and wired.

## Actual source bound

Every fixed `C²` profile supported in `[0,1]`, with positive square mass,
produces a constant `C_phi>0` such that, for `1<=c<=2`, `N>=2`, and all
signed vectors,

```
abs(NR(phi_(c/N),N,x)) / mass(phi_(c/N))
  <= C_phi * ((c-1)+1/N) * (poleDefect(N,x)+sum_(1<=n<=N) x_n^2).
```

For every `epsilon>0`, one `delta in (0,1]` and one eventual horizon make
the normalized correction at most
`epsilon*(poleDefect(N,x)+sum_(1<=n<=N) x_n^2)` for every ratio in
`[1,1+delta]` and every vector. Every prime power is retained.

## Mechanism

Distinct positive integers with one at most `N` have logarithmic gap greater
than `1/(N+1)`. Height control of the actual autocorrelation leaves amplitude
`B^2*max(0,w-1/(N+1))` at every non-ratio lag. Retain that amplitude through
the weighted Schur and divisor-row argument. At `w=c/N`, normalization
costs at most `(B^2/M)*((c-1)+1/N)`. The actual prime defect pays the remaining
top-row logarithm through the existing `sum_top_le_poleDefect_param`.
Compact smoothness produces the required height bound.

## Lean closure

- `IntegerSeparationShrinksTheNonRatioPrimeRows.lean`: needed check46159 and final check84487 passed clean; capstone `abs_nonRatioForm_le_overlap_rows`.
- `TheFirstOverlapPrimeCostHasASmallDefectCoefficient.lean`: final check97294 passed clean; capstones `exists_small_overlap_nonRatio_defect_budget` and `exists_overlap_interval_with_small_nonRatio_cost`.

Every printed capstone dependency list contains only `propext`,
`Classical.choice`, and `Quot.sound`. Both modules are imported by the
programme umbrella. No full or umbrella build was run.

## Scope and remaining obligation

TransMetzlerWeilPositivity already proves complete positivity at a genuine
first overlap for an explicit smooth profile. This batch supplies a
non-ratio prime estimate for arbitrary fixed smooth unit profiles; it is
not a new first-crossing positivity theorem. The overlapping Gram and joint
archimedean and polar terms still need a complete relative comparison.
Splitting an overlapping pair into separate singular cross integrals is
not justified. No paper proof of the missing complete-form comparison is
claimed or left awaiting formalization.
