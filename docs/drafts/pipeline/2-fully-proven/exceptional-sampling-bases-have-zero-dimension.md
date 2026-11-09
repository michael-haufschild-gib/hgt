# Exceptional sampling bases have zero dimension

- **Stage:** 2-fully-proven; Lean formalization in progress
- **Type:** THEOREM on paper; not yet counted
- **Obstacles:** B13, B112; geometry of bases that miss a finite exceptional top.
- **Statement:** For a finite visible isolated top, bases admitting infinitely many sub-top readings form a set of Hausdorff dimension zero. For actual zeta AAL failure, this applies below `zetaZeroAbscissa-1/2`. A positive-Hausdorff-dimension family of recurrent bases at every positive rate, together with zeros approaching the line, would therefore characterize RH.
- **Sharpness target:** A positive conjugate pair can have a residual set of bases with arbitrarily strong exponentially small subsequences. Thus a dimension-zero exceptional set need not be countable or topologically small.
- **Novelty boundary:** The verified metric detection law gives Lebesgue-null exceptional bases. Dimension zero would allow recurrence on singular sets of any positive dimension to exclude isolated tops.

## Approach

Upgrade uniform finite-jet sublevel measure to a uniform finite-ball cover: a bounded number of intervals of radius `K epsilon^(1/k)` per fixed-radius window. At level `n`, a compact interval of positive bases needs `O(n)` such windows, while exponentially small thresholds give exponentially shrinking radii. Summable diameter costs for every positive dimension force zero-dimensional limsup sets. Countable compact base intervals and decay rates yield one zero-dimensional exceptional set. Transfer through the summable lower layer as in the metric theorem.

For sharpness, neighborhoods of the resonant bases of a cosine pair are open and dense after every finite level cutoff. Baire intersection gives recurrent exponential cancellation at all integer decay rates.

## Corpus leads

- `UniformOscillatoryJets`, `FiniteJetSublevelMeasure`: uniformly nonzero finite jets and local sublevel control.
- `KleinbockMargulis/DerivChain`, `SmoothGoodOne`, `CutInterval`: interpolation, finite level sets, and bounded sublevel components.
- `TheExceptionalValuesHaveSmallHausdorffDimension.hausdorffMeasure_eq_zero_of_tail_covers`: shrinking finite covers with summable diameter costs.
- `ZetaMetricTopDetection`: actual top detection and positive-measure recurrence criteria.

## Proof

Write the normalized finite top as `P(t)=sum c_j exp(i gamma_j t)`, after merging equal frequencies, with `k` distinct frequencies and a nonzero coefficient. The inverse Vandermonde bound and uniform derivative bounds give `r,A>0` such that every interval `(x-r,x+r)` has a real component `f` and an order `m<k` with `|f^(m)|>=A` throughout.

For `m>=1`, suppose `m+1` sublevel points `|f|<epsilon` are mutually separated by at least `d`. Lagrange interpolation and the derivative-chain mean-value theorem give
`A <= m! (m+1) epsilon/d^m`.
Consequently `d <= (((m+1)!/A) epsilon)^(1/m)`. Taking twice this radius, every separated finite sublevel subset has at most `m` points. A separated subset of maximal cardinality covers the entire sublevel set by at most `m` balls of that radius. This maximum exists because possible cardinalities are a nonempty bounded subset of the naturals. For `m=0`, the sublevel is empty when `epsilon<=A`, and one radius-`r` ball otherwise. For `epsilon>=1`, one radius-`r` ball always suffices. Since `epsilon^(1/m)<=epsilon^(1/k)` for `0<epsilon<=1` and `m<k`, a common constant `K` gives at most `k` balls of radius `K epsilon^(1/k)` in every window.

Fix `0<L<=U` and `delta>0`. For `nu=n+1`, the interval `[nu L,nu U]` is covered by at most `B nu+1` fixed-radius windows, where an integer `B>U/r+1` suffices. If `ell in [L,U]` and `|P(nu ell)|<=exp(-delta nu ell)`, apply the preceding cover with `epsilon=2 exp(-delta nu L)`. Scaling centers by `1/nu` covers these bases by at most `k(B nu+1)` balls of radius at most `R exp(-b n)`, with `R=K 2^(1/k)` and `b=delta L/k>0`. For every `s>0`, total diameter cost is bounded by a constant times `(n+1) exp(-bs n)`, a summable sequence. Tail covers therefore give zero `s`-dimensional Hausdorff measure for the limsup. Countably many compact positive-base intervals cover `(0,infinity)`, so the exceptional set has dimension zero. A countable union over `delta=1/(j+1)` contains all bases with exponentially small subsequences at any positive decay rate and still has dimension zero.

For a summable isolated top, write the trace as `exp(theta t)P(t)+R(t)`, where `theta=Theta-1/2` and `|R(n ell)|<=W exp((Theta2-1/2)n ell)` with `Theta2<Theta`. Fix `a<theta` and choose `0<delta<min(theta-a,Theta-Theta2)`. Any recurrent bound `|trace(n ell)|<=C exp(a n ell)` forces `|P(n ell)|<=exp(-delta n ell)` along an infinite subsequence: both `C exp(-(theta-a-delta)n ell)` and `W exp(-(Theta-Theta2-delta)n ell)` tend to zero. Thus its base set has dimension zero. Actual zeta AAL failure supplies this isolated top, summability, and visibility unconditionally. Positive dimension at every positive rate contradicts failure by choosing `a=(Theta-1/2)/2`. Conversely RH bounds the Weil lag uniformly, so every positive base satisfies every positive-rate recurrence condition. Combining this with `RH iff ZAL and AAL` gives the stated criterion.

For sharpness take `P(t)=cos t=(exp(it)+exp(-it))/2`. For every pair of naturals `m,N`, the union over integers `n>=max(N,1)` of `{ell: |cos(n ell)|<exp(-(m+1)n)}` is open and dense. Density follows from the resonant grids `(pi/2+j pi)/n`, whose spacing `pi/n` tends to zero and on which cosine vanishes exactly. Baire's theorem makes the intersection over `m,N` a dense G-delta. At each positive base in this intersection, every prescribed `delta>0` is dominated by some `(m+1)/ell`, giving infinitely many exponential cancellations. This residual set is contained in the dimension-zero exceptional set already proved. In every open positive interval it is uncountable, since a countable residual subset would make that Baire interval meagre in itself.

## Novelty audit and formalization gate

The boundary in the rate is exact. At every rate `a>=zetaZeroAbscissa-1/2`, the global strip bound gives `|lag(n ell)|<=lagWeightTotal exp(a n ell)` for every positive base and every level. Thus the recurrent-base set is the whole positive half-line and has dimension one. Under AAL failure its dimension therefore jumps from zero below the top exponent to one at and above that exponent. This is a corollary of the same dimension law and counts with it.

The corpus already has residual dimension-zero sets of exceptional zeta **values**. Here the parameter is the **sampling base** of a finite top, and the consequence is a positive-dimension recurrence criterion for AAL and RH. The previous sampling theorem controls Lebesgue measure only. The finite-cover estimate, dimension-zero sampling law, transfer to zeta, and cosine sharpness constitute one contribution. Not counted until direct Lean and transitive-axiom audits pass.
