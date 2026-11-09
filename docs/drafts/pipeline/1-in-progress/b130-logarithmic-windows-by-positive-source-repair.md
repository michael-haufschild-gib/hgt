# Logarithmic windows through positive source repair

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B130 scale locality: replace log-square prime windows by `C log(T+2)`.

## Positive quartet quotient

Let `a` be a first-quadrant Xi zero, `L=quadrantListOf [a]`,
`d=|L|=2 xiZeroMult a`, and `P=listDivisor L`. Thus `P` removes the
whole selected quartet with full multiplicity; no simple-zero premise occurs.
Use `N(z)=z^(2d)+c`, choosing `c=1` unless `N(a)=0`, and `c=2` otherwise.
Then `c>0`, `N(a)≠0`, and `N(is)=s^(2d)+c>0` because `d` is even.

The quotient `XiC(z) N(z)/P(z)` has positive real Laplace values.
`listComb_spec` gives a real even Lipschitz source with every exponential
moment, bounded by a constant times the theta source, and asymptotic to
`Π thetaCuspFullSource` at both ends, where `Π=∏_(β∈L)(-β²)>0`.
Hence both tails are strictly positive. The positive leading numerator avoids
needing a sharper tail asymptotic for `XiC/P`.

Relevant corpus declarations: `thetaDivisionList_quadrantListOf`,
`count_quadrantListOf`, `perm_map_conj_quadrantListOf`,
`prod_neg_sq_quadrantListOf`, `listComb_spec`,
`listComb_thetaListDivision_eq_ofReal`, `exists_lipschitz_listComb`,
`XiC_I_mul`, `thetaSourceLaplace_pos`.
Quartet specialization and full-multiplicity survival remain to be assembled.

## Positive translation repair

Proposed sufficient theorem: a Lipschitz real source with every exponential
moment, strictly positive tails, and strictly positive real Laplace values
admits a finite positive translation average that is nonnegative everywhere.
The mesh may be arbitrarily small.

Construct a compact lower grid step `l≤g` preserving every real Laplace sign.
Its transform is a positive interval factor times `P(exp(hs))`; a positive
first cell supplies positivity of `P(0)`. Real factorization and sharp
quadratic repair give `Q=∏(X+r_j)`, `r_j>0`, with `PQ` coefficientwise
nonnegative. Thus `Q(τ_h)l≥0`; positivity of the coefficients of `Q`
implies `Q(τ_h)g≥0`.

`Q` has only negative real roots. Choosing `h` with
`h |Im w₀|<π/2` ensures `Q(exp(hw₀))≠0`, preserving the selected mode.
Finite translations add only `O(|s|)` to logarithmic moment growth.
Evenness of the repaired source is unnecessary.

## Uniform lower approximation

Take `A≥1` with `g>0` for `|x|>A`, a Lipschitz constant `L>0`, and
`B=1+sup_(|x|≤A+1)|g(x)|`. Let `m>0` bound `g` below on
`A+2≤|x|≤A+5`. Choose `S≥1` with `(m/2)exp(S)>2(A+2)B`, and put
`η=min_(|s|≤S)∫exp(sx)g(x)dx>0`.

Choose `R>A+6` with
`exp(-R)∫exp((S+1)|x|)|g(x)|dx<η/4`; let `u>0` bound `g` below on
`A+1≤|x|≤R`. Choose `h=2R/M` below the prescribed mesh bound and
`min(1,1/L,u/(2L),m/(2L),η/(16RL exp(SR)))`.

On each cell use its left value minus `Lh`, and use zero outside `(-R,R]`.
The step lies below `g`, loses at most `2Lh` within the grid, has negative
part supported in `[-A-2,A+2]` and bounded by `B`, and is at least `m/2`
on both outer unit bands. Those bands prove Laplace positivity for `|s|≥S`.
For `|s|≤S`, compact error is below `η/4`, as is the discarded weighted tail.
The first coefficient is positive since `g(-R)≥u`.

## Lean status and remaining work

- `ArithmeticLocalDivisorGeometry/PositiveMultipliers.lean`: polynomial repair
  and nonvanishing in the closed right half-plane proved.
- `HTGeometry/PositiveTranslationRepair/`: polynomial translation order,
  lower grid errors, grid polynomial transform, positive outer bands, compact
  Laplace margins, and uniform weighted approximation bounds proved.
  Checked capstones depend only on `propext`, `Classical.choice`, `Quot.sound`.
- `PositiveLaplaceRepair.exists_positive_average_of_laplace_positive` proves
  complete positive-source repair at arbitrarily small mesh. Its transitive
  axiom audit contains only the standard three axioms.
- Missing: actual quartet source specialization, preservation of its selected
  mode, theta moment bound `O(|s| log(2+|s|))`, logarithmic leakage, and
  continuous and prime-window conclusions.

Chernoff parameter `q=T` would turn that moment bound into exponentially
small leakage at radius `C log(T+2)`. Exponential tilting then supplies the
shifted-depth tests for prime-gap iteration. This changes observation scale;
it supplies no arithmetic lower bound. B130 remains open. No external novelty
claim; no web search used.
