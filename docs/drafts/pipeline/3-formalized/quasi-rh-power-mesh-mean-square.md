# Mean-square exponent on integer-power meshes

- **ID:** quasi-rh-power-mesh-mean-square
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [quasi-rh.md §8.4](../../../report/quasi-rh.md)
- **Statement:** For every integer m≥1, the infimum of exponents r≥1 for the cumulative square energy of T(j^m)/j^m is 1+2m(Θ−1/2).

## Paper proof

Let u(N)=T(N)/N and E_m(J)=Σ_{2≤j≤J}u(j^m)². Suppose E_m(J)≤CJ^r, r≥1. Finite-window averaging gives, for every 0<θ<1 and all large j, an index k≤j with j−k≤j^θ and |u(k^m)|≤Dk^((r−θ)/2).

These selected powers retain a physical power gap. Given large n, set x=n^(1/m) and j=floor(x). Then j is large, j^m≤n<(j+1)^m, and j+1≤2x. For a selected k in its backward window,

    n−k^m ≤ (j+1)^m−k^m
           ≤ m(j+1)^(m−1)(j+1−k)
           ≤ 2^m m n^(1−(1−θ)/m).

The positive gap saving (1−θ)/m permits the existing one-sided Abel power-gap receiver, with amplitude exponent (r−θ)/(2m). Letting θ increase to one proves Θ≤1/2+(r−1)/(2m). Conversely the intrinsic bound u(N)=Oε(N^(Θ−1/2+ε)) gives E_m(J)=Oε(J^(1+2m(Θ−1/2)+ε)), proving the exact infimum law.

## Arithmetic target exposed

For even m=2s, use D=j^(m−1). The existing normalized head bound (3/5)j^(s−1) gives cumulative head cost at most (9/25)J^(m−1). The normalized diagonal costs at most 9/25 per j. Thus the ordered covariance sum

    W_m(J)=Σ_{2≤j≤J} covariance(j^m,j^(m−1))

has sufficient and necessary upper bounds Oε(J^(5+ε)) for m=6, Θ≤5/6, and Oε(J^(3+ε)) for m=4, Θ≤3/4. The exact hyperbola reduction keeps q<j. These numerical covariance estimates are conjectures, not consequences of the mean-square classification.

## Gates

- [x] Dependency-closed paper argument from finite averaging, polynomial difference, and inspected power-gap receiver.
- [x] Formalize preservation of power gaps under integer powers.
- [x] Formalize sharp mesh mean-square receiver, converse, and exact exponent law.
- [x] Formalize averaged covariance reductions at m=6 and m=4.
- [x] Focused check, standard-axiom audit, wiring, report update.
- [x] Run formal lint: no error in this leaf; global gate flags unrelated unreachable module `SquareRootThreshold.OnLineShadowIndistinguishability`.

`QuasiRHPowerMeshMeanSquareAbscissa.lean` passes `lake --old env lean` without warnings. All 11 public theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The two finite-averaging helpers exposed from `QuasiRHMeanSquareAbscissa.lean` also pass their axiom audits. The module is wired into `RHTower`.

External novelty is unclaimed. No numerical strip bound or RH assumption is introduced.
