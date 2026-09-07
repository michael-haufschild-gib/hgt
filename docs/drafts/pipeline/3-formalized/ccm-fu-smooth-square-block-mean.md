# CCM-FU: exact smooth square-block mean and bounded-quotient obstruction

- **Stage:** 3-formalized
- **Parent:** [source-local two-prime comparison](../1-in-progress/ccm-fu-two-prime-local-blocks.md)
- **Result:** Exact smooth mean, logarithmic Abel error, and unconditional factor-two dilation control above one universal quotient threshold. Any original two-prime ceiling failure must involve a bounded quotient profile. The all-cutoff comparison, complete adaptive ceiling and SD1 remain open.

## Exact correction bounds

For every positive integer n the harmonic error satisfies

`1/(2n)-1/(12n^2) <= H_n-log(n)-gamma <= 1/(2n)-1/(12(n+1)^2)`.

The new lower bound follows from `log(x)>=2t+2t^3/3`, with `t=(x-1)/(x+1)`, by differentiating its remainder and comparing the corrected harmonic sequence with its actual limit. The upper bound was already formal.

Put `c=log(2*pi)/2`. The actual Stirling sequence and its reciprocal difference bound prove, for every positive N,

`0 <= log(N!)-N log(N)+N-log(N)/2-c <= 1/(12N)`.

These are analytic proofs from monotonicity and limits, with no numerical premises.

## Complete square-block mean

With `s=floor(sqrt(N))`, define

`q(N)=c-gamma-1/3+(N-s^2-s)^2/(2s^2)`.

The literal smooth hyperbola source obeys `q(N)-5/s <= smooth(N) <= q(N)+2/s`. The rational logarithm upper bound retains the quadratic coefficient exactly; the lower bound loses at most `4/s`. The second harmonic correction is essential to retain the leading constant.

Define `a=c-gamma-1/6`. The exact quadratic sum over a complete block is `s(s+1)(2s+1)/3`. Hence each complete square block has total error at most 15 from its mean `a`. The final partial block is bounded separately. At every natural cutoff,

`|sum_(k=1..N) smooth(k)-a N| <= 33 sqrt(N)`.

Finite Abel summation retains the terminal term and uses `sqrt(k)(w_k-w_(k+1))<=1/(4k)`. It gives the actual half-order estimate

`|smoothAbel(M)-a sqrt(M)| <= 9 log(M+1)+25+|a|`.

The Stirling sequence also proves `c>=11/12`; the existing analytic Euler-constant bound gives `gamma<7/12`. Therefore `a>1/6` strictly, without decimal approximations.

## Dilation comparison and remaining obstruction

Combining the exact smooth mean with the already formal centered bounds gives, for all natural M,

`(a-5/48)sqrt(M)-10log(M+1)-26-|a| <= K_1(M)`,

`K_1(M) <= (a-1/24)sqrt(M)+10log(M+1)+26+|a|`.

For every positive epsilon these imply a common eventual coefficient band with lower endpoint `a-5/48-epsilon` and upper endpoint `a-1/24+epsilon`. Choose `epsilon=(a-1/6)/4`. The upper coefficient is strictly below twice the lower coefficient. Exact clipped interpolation preserves the upper coefficient at every dilation whenever both adjacent quotient endpoints are in this common tail. The parent cutoff is in the same tail. Thus Lean proves

`exists T>=1, forall M,p>0, T<=M/p -> K_p(M)<=2K_1(M)`.

Consequently every actual factor-two failure has `M/p<T`, uniformly in M and p. Combining this with the complete original two-prime reduction gives one universal T such that every original two-prime ceiling either holds or has a witness `r<N<=M`, with r one of those primes, `N/r<T`, and `2K_1(N)<K_r(N)`.

Bounded quotient does not mean bounded cutoff or a finite list of arithmetic cases: the dilation and clipped phase can still vary without bound. These remaining profiles have not been eliminated. No all-cutoff two-prime ceiling, complete growing schedule or RH conclusion follows yet.

## Lean certificate

`RHTower.HarmonicStirlingExactBounds` contains two new correction theorems. `RHTower.DivisorSmoothSquareBlockMean` contains one definition and ten public theorems covering the exact source estimates and their bounded-quotient consequence. The complete scratch proof and both exact leaves passed `lake env lean`; only the required new leaf oleans were generated. All 13 new public declarations were axiom-audited once in a separate scratch file: their dependency closures use only `propext`, `Classical.choice` and `Quot.sound`, with no added axioms or computational certificates. Formal lint passed with existing large-file warnings only. Both leaves are wired once, without dependency, full or umbrella builds. Card links and scoped whitespace checks passed. No channel table was recomputed.
