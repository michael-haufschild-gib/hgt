# Central multiplicity and the full heated coefficient cone

- **ID:** central-multiplicity-full-heat-cone
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; formalization pending)
- **Source:** Arithmetic Local Divisor Geometry; growing degree and all-order detection
- **Statement:** For `P_m(X)=X^(2m)(X²−a)²`, `a>0`, its forward-heat coefficient cone has an exact finite quadratic-index criterion. Its heat threshold lies between `a/(8m+10)` and `a/(8m+5)`. Consequently the threshold is asymptotic to `a/(8m)`, rather than the order `a/m²` seen by the highest adverse coefficient alone.

## Scope and duplication audit

`RHTower/XiSliceHeatMaskedPairThreshold.lean` already constructs every Hermite moment of the masked pair, its actual-source cofactor-error receiver, the top-order threshold, and a double-multiplicity example where a lower order detects later heat. Those are inputs, not new claims. This statement optimizes the whole growing family and supplies a uniform multiplicity law. It does not bound the actual Xi cofactor error.

Corpus searches: `central multiplicity forward heat coefficient threshold`, `maskedPairPoly`. Complete the declaration-level duplication audit before promotion. No numerical experiments are involved.

## Complete symbolic paper proof

Use `E_s=exp(sD²)`, with `s>0`, and put

`B=(2m+2)(2m+1)`, `C=(2m+4)(2m+3)`, `d=C−B=8m+10`, `t=s/a`.

The monomial formula is

`[X^(2j)] E_s X^(2r) = (2r)! s^(r−j)/((r−j)!(2j)!)` for `j≤r`,

with zero outside that range. For `0≤j≤m`, factor the positive quantity

`a²(2m)!s^(m−j) / ((2j)!(m+2−j)!)`

from the coefficient of `E_s P_m`. The remaining sign polynomial is

`F_t(k)=k(k+1)−2B(k+1)t+BCt²`, where `k=m+1−j`.

The coefficient at `X^(2m+2)` has sign `Ct−2`, hence the same sign as `F_t(0)=Bt(Ct−2)`. The leading coefficient is one and all odd coefficients vanish. Therefore the complete coefficient cone is exactly

`F_t(k)≥0 for every integer 0≤k≤m+1`.

This criterion retains all orders and multiplicities. Completing the square gives

`F_t(k)=(k−Bt+1/2)² + Bdt²−Bt−1/4`.

### Uniform upper bound

Put `e=8m+5`. For `t≥1/e`,

`Bt(dt−1) ≥ (B/e)(d/e−1) = 5B/e² > 1/4`,

because `20B−e²=16m²+40m+15>0`. Thus every `F_t(k)` is strictly positive. All even coefficients of `E_s P_m` are positive for `s≥a/(8m+5)`.

A sharper nonrational sufficient bound is

`s ≥ a(1+√(C/B))/(2d)`,

the positive zero of the completed-square remainder. The rational bound suffices for the asymptotic law and avoids square-root estimates.

### Uniform lower bound

Suppose `0<t<1/d` and choose the explicit integer `k=⌊Bt⌋`. Since `B/d<(m+1)/2`, this integer belongs to `[0,m+1]`. The floor inequalities give `−1/2<k−Bt+1/2≤1/2`, so

`F_t(k)≤Bt(dt−1)<0`.

This works also for `m=0`; no generic-multiplicity or positive-central-order assumption is needed.

So coefficient positivity fails below `a/(8m+10)`. At zero heat it fails directly because the coefficient at degree `2m+2` is `−2a`.

The coefficient cone is closed, nonempty at the upper bound, and upward closed by the forward-heat semigroup and coefficient-positivity preservation. Its threshold `σ_m` therefore exists and satisfies

`a/(8m+10) ≤ σ_m ≤ a/(8m+5)`.

For positive integer `m`, multiplication by `8m/a` and squeezing gives `8mσ_m/a→1`. In contrast, the top-coefficient threshold `2a/C` has order `a/m²`. Near the full threshold the detecting index is near `j=m/2`, explaining why the top coefficient alone loses a factor proportional to multiplicity.

## Programme significance

Central factors are exactly removable from the unheated coefficient cone but not from its forward-heat counterpart. Heat transfers the adverse sign into lower orders. The full degree must be retained when pricing a local multiple zero. Any actual-source use must additionally pay the existing signed cofactor-deviation budget at the chosen order and heat; this polynomial result does not discharge that arithmetic estimate.

## Gates

- [x] Dependency-closed symbolic paper proof.
- [ ] Complete source/corpus novelty audit.
- [ ] Formalize exact coefficient criterion and rational threshold bracket.
- [ ] Formalize asymptotic threshold law and audit transitive axioms.
- [ ] Connect normalization to the existing Hermite-moment receiver.
