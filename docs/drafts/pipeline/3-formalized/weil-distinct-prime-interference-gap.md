# Distinct outer-prime interference gap

- **ID:** WEIL-DISTINCT-PRIME-GAP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Sources:** `CCMRestrictedWeilPrimeOuterShell`, exact aperture cutoffs, current Hilbert contraction calculus, and mathlib Bertrand.
- **Modules:** `HTGeometry.NilpotentContractionInterference` (5 public theorems), `RHTower.CCMRestrictedWeilPrimeInterference` (12 public theorems), both wired into their umbrellas.

## Full proof chain and remaining scope
Literal prime–Gamma source → joint source estimate on constrained ground → exclude zero-ground forced equations → positive ground at every aperture → weighted pole exclusion → RH. The joint prime estimate is proved. A sufficiently strong comparison with Gamma energy on the same constrained vector remains open; RH is neither proved nor disproved here.

## Conjecture loop
1. **Conjecture:** distinct outer shifts cannot simultaneously preserve one constrained vector's norm. **False:** their overlap projections are nested. `exists_polarConstrained_common_outerShift_norm` constructs a nonzero constrained form vector preserving both norms whenever `a<h<k<2a`.
2. **Pivot:** output alignment is obstructed quantitatively. **Proved:** the product of two actual shifts moves support inward by their lag difference on each application. Its sufficiently high power vanishes.
3. **Sharper conjecture exposed by the support proof:** only the endpoint-overlap width, rather than the whole diameter, needs to be crossed. **Proved:** `(S_h S_k)^N=0` for `N>0` and `N(k-h)>2a-h`.
4. **Source consequence:** positive weights give a strict operator-norm gain. **Proved:** `N²||uS_h+vS_k||²≤N²(u+v)²-uv`. The gain transfers to literal von Mangoldt atoms, persists after adding all remaining source atoms, and occurs at every aperture `a≥log 5` by Bertrand.

## Dependency-closed paper proof [PROVED HERE]
Let `T_h f(x)=f(x+h)`, let `P_a` be cutoff to `[-a,a]`, and let `S_h=P_a(T_h+T_{-h})P_a` act on the actual aperture Hilbert space. The preceding outer-shell theorem gives self-adjointness and `||S_h||≤1` whenever `h>a`.

Fix `a<h<k` and put `d=k-h>0`, `C=S_h S_k`. Expanding the two exact cutoff formulas leaves

- `Cf(x)=f(x-d)` on `[-a,a-h]`;
- `Cf(x)=f(x+d)` on `[-a+h,a]`;
- zero elsewhere.

All statements are almost everywhere. The other two translated terms lie outside the aperture because `h+k>2a`. On the left interval `x<0`, so the argument `x-d` has absolute value `|x|+d`; on the right the same holds for `x+d`. Induction therefore shows `C^N f` vanishes wherever `|x|>a-Nd`. Every positive iterate also lies in the two endpoint intervals, where `|x|≥h-a`. If `Nd>2a-h`, the two support requirements are disjoint, proving exact nilpotence. This is a source-support identity, not a finite-dimensional approximation.

For an arbitrary Hilbert contraction `C`, finite telescoping gives

`||x-C^N x||≤N||x-Cx||`.

If `C^N=0`, squaring and using `||Cx||≤||x||` yields

`2N² Re<x,Cx>≤(2N²-1)||x||²`.

For contractions `A,B`, with `A` symmetric and `(AB)^N=0`, expand `||uAx+vBx||²`. The mixed term is `2uv Re<x,ABx>`. For `u,v≥0`, applying the numerical-range bound gives

`N²||uAx+vBx||²≤[N²(u+v)²-uv]||x||²`.

A square-root operator bound gives the same inequality for `||uA+vB||`. If `u,v>0`, the right side is strictly below `N²(u+v)²`. In the actual application choose any positive integer `N` exceeding `(2a-h)/(k-h)`; no nilpotence premise is left to establish.

The source scalar normalization is exact:

`Λ(n)T(n) = [Λ(n)/sqrt(n)] S_{log n}`.

Consequently `ccmPrimeSourcePair_opNorm_sq_bound` gives the explicit gain with literal weights, and `ccmPrimeSourcePair_norm_lt_separate` gives strict subadditivity for two distinct positive outer prime-power atoms. Extracting that pair from the finite sum and applying the already proved shell bounds to the remaining atoms proves

`||ccmFinitePrimeOperator a|| < ccmPrimeOuterShellBudget a`

whenever such a pair is present.

For a uniform elementary supply, put `X=exp(a)≥5`, `b=ceil(X)`. Bertrand gives primes `b<p≤2b` and `p<q≤2p`. Then `X<p<q≤4b<4X+4≤X²`. Thus both distinct positive source atoms lie strictly between `exp(a)` and `exp(2a)`. This proves the strict full-source budget at every `a≥log 5`, without a prime-counting asymptotic or computation.

Finally, to verify the failed first conjecture, take a constrained `+1` eigenvector for `S_k` supplied by the preceding module. Its support lies in the endpoint projection for `k`, a subset of the endpoint projection for `h`. Therefore `S_h² f=f` and self-adjointness gives `||S_h f||=||f||`; `S_k f=f` already gives the other equality. Common norm preservation and strict weighted-sum norm coexist because the output directions do not align.

## No-go closure and positive survivor
- **Exact obstruction:** `exists_polarConstrained_common_outerShift_norm` refutes the proposed exclusion of simultaneous individual norm preservation.
- **Strongest positive survivor:** support drift, exact nilpotence at overlap-width scale, explicit weighted interference gap, strict literal pair norm, and strict full-source budget for every `a≥log 5`.
- **Consequence:** sharp individual estimates cannot be combined as if their worst-case outputs were compatible. The joint gain is proved on the entire aperture space and therefore also applies to the constrained sector. It gives no order comparison with Gamma energy by itself.
- **Novelty audit:** the preceding corpus had sharp single-atom bounds and generic finite/spectral receivers. The new actual-operator support product and source-weighted quantitative gap are neither another RH equivalence nor a numerical certificate. No external novelty is claimed for the general telescoping inequality.

## Verification
- Scratch `lake env lean` checks: all 17 public theorem bodies pass; the final source copy removes one redundant tactic warning.
- Named final audits for `GaloisForLFunctions.HTGeometry.NilpotentContractionInterference` and `GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimeInterference`: PASS.
- `lake env lean /tmp/hgt-prime-interference.ysms8iuq/Audit.lean`: all 17 public declarations use exactly `[propext, Classical.choice, Quot.sound]`; the actual mathlib `RiemannHypothesis` definition is printed.
- `python3 scripts/formal_tools.py lint`: PASS (large-file warnings only); `git diff --check`: PASS.
- All owned Lean and build processes terminated normally.
- No umbrella build, numerical experiment, computational oracle, or added axiom.
