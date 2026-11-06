# Nonrepelling zeta values have dimension zero

- **ID:** exceptional-zeta-values-dimension-zero
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ49
- **Statement:** `dimH zetaNonrepellingValues = 0`, hence the dense residual set of exponentially close equal-value pairs also has dimension zero.

## Paper proof

For a complex polynomial `P` of degree at most `k`, values at points `z` in a disc of radius `r` with `|P′(z)|≤ε` lie in at most `k+1` discs of radius `2^k rε`. Use the value at the disc centre and all critical values. If a nearest critical point lies within `r` of `z`, integrate along that segment; otherwise integrate to the disc centre. In either case segment length is at most `r` and no greater than the distance from `z` to any root of `P′`. Each factor in `P′` grows by at most two along the segment, so `|P′|≤2^k|P′(z)|`. Constant derivatives, including zero, satisfy the same argument directly.

Fix `k≥1`. For a holomorphic function bounded by `M` on a disc of radius `1/2` centred at `q`, its degree-`k` Taylor polynomial has value error `O_k(Mh^(k+1))` on the disc of radius `4h`, for `h≤1/64`. Indeed Cauchy's coefficient bound on radius `1/4` and summation of the geometric tail give this bound. Cauchy's derivative estimate on a disc of radius `h` then gives derivative error `O_k(Mh^k)` on radius `2h`. All constants depend only on `k`.

Suppose `|s-q|≤2h`, `F(s)=F(s′)` and `0<|s′-s|≤h^k≤1/64`. The radius-`1/4` disc at `s` lies in the radius-`1/2` disc at `q`. The second-order Taylor bound at `s`, divided by `|s′-s|`, gives `|F′(s)|≤128M|s′-s|≤128Mh^k`. Applying the polynomial cover with `r=2h`, then adding the value error, covers `F(s)` by at most `k+1` discs of radius `C_k Mh^(k+1)`, for a fixed finite `C_k>0`.

A mesh of size `h=2^-n` up to height `Y=2^⌊n/D⌋` requires `O_k(Yh^-2)` discs, each of radius `O_k(Y^B h^(k+1))` under polynomial strip growth. Use mesh points within distance `2h` of the original strip at heights at least two; the larger-strip hypothesis supplies every radius-`1/2` disc needed above. The dimension-`s` cover costs are summable when `(k+1)s>2+(Bs+1)/D`. Choose `k` and then `D` for each `s>0`.

For completeness, avoiding all covers at scales `n≥n₀≥6` implies polynomial separation with exponent `kD`. For a pair at distance `d≤1/64`, choose `j` with `2^(-j-1)<d≤2^-j` and put `n=⌊j/k⌋`. Then `d≤2^(-kn)`. If `n<n₀`, then `d>2^(-kn₀)`. Otherwise the common value would lie in the cover unless `|Im s|>2^⌊n/D⌋`. In that case `j+1≤k(n+1)≤kD(⌊n/D⌋+1)` gives `d>2^(-kD)(2+|Im s|)^(-kD)`. The minimum of these constants and `1/64` is a positive separation constant. Thus every nonrepelling value belongs to the limsup cover. The Hausdorff covering criterion proves zero measure in every dimension `s>0`, hence dimension zero.

Zeta's established polynomial strip bound supplies the analytic input. The residual exponential-pair set is already proved to lie in `zetaNonrepellingValues`.

## Lean

- `PolynomialCriticalValuesControlSmallDerivatives.lean`: `exists_polynomialCriticalCentre_near`, finite cover independent of coefficient lower bounds.
- `HigherTaylorPolynomialsCoverNearCoincidences.lean`: `close_pair_value_near_taylorCriticalCentre`, degree-`k` Taylor cover with radius `C_k M h^(k+1)`.
- `TheExceptionalValuesHaveDimensionZero.lean`: `hausdorffMeasure_nonrepellingValues_eq_zero_of_pos`, every positive-dimensional Hausdorff measure vanishes under polynomial strip growth; `dimH_zetaNonrepellingValues_eq_zero` and `dimH_exceptional_values_of_riemannZeta_eq_zero`, unconditional ζ conclusions.

All declarations lie in namespace `GaloisForLFunctions.ArithmeticDiscreteness`. Dependency checks and direct `lake --old env lean GaloisForLFunctions/ArithmeticDiscreteness/TheExceptionalValuesHaveDimensionZero.lean` passed. Modules are wired into the umbrella.

Membership of the particular value zero remains undecided; dimension zero does not prove zero repulsion. Γ49 remains partially solved.
