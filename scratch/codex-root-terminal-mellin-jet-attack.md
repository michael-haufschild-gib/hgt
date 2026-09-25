# CCM-FU: deterministic-prefix Mellin-jet obstruction

Status: dependency-closed paper argument below; Lean closure remains open.
This concerns full deterministic prime prefixes, including the literal
square-root prefix `P_N={p prime : p≤N}` at `M=N²`.
It does not exclude source-selected, macroscopic terminal cores, nor prove RH.
The read-only frontier map is unchanged. Corpus audit found the terminal
energy identity, exact source Abel sum, Mertens' constant, strong PNT errors
for `ψ` and `π`, and source-selected checkpoint cores, but no theorem for this
square-root-prefix asymptotic. The deep search was partial; an exhaustive
relevant-file source search likewise found no such result.

## Statement

Let `E(M,P)` be `mobiusDivisorSelectionEnergy M P`. Fix `0<β<1/2`.
Uniformly over integer thresholds `B=B(M)` satisfying
`M<B²` and `B≤M exp(-(log M)^β)`, set `P_B={p prime : p<B}`.
Then `E(M,P_B)/M² → +∞` as `M→∞`. In particular,

`E(N²,P_N)/N⁴ → +∞` as `N→∞`.

More precisely, there are an integer `r≥1` and nonzero real `c_r`, both
independent of the admissible threshold, such that the empty-label head satisfies

`H(M,P_B) = c_r M^(3/2)/(log M)^(r+1)
             + O(M^(3/2)/(log M)^(r+2))`.

Thus `E(M,P_B) ≥ H(M,P_B)² ≫ M³/(log M)^(2r+2)`.
This covers every full power-law prime prefix at threshold `M^α` for
`1/2≤α<1` (round upward at `α=1/2`). It is a no-go for this broad class of
deterministic prefixes. Its
positive survivor is an exact Mellin-jet detector of delayed source payment:
any successful core in this threshold range must depart from the full-prefix
choice and cancel the coherent transformed head. Source-sensitive selections
and nearly complete prefixes remain possible; this result does not choose
between them.

## Proof

Write `F(n)=ψ(n)-n+2γ` and define, for real `y≥1`,

`C(y)=∑_{1≤n<floor y}(√(n+1)-√n)F(n)
       +(√y-√(floor y))F(floor y)`.

At integer `m`, `C(m)=∑_{1≤n<m}(√(n+1)-√n)F(n)`, the already-proved complete
Möbius dilation source. The exact prime clipping weight is

`(√M-√(p floor(M/p)))/(√(p(floor(M/p)+1))-√(p floor(M/p)))`
`=(√(M/p)-√(floor(M/p)))/(√(floor(M/p)+1)-√(floor(M/p)))`.

Therefore the already-proved terminal child source equals `C(M/p)` for every
remaining prime, including quotient endpoints. The terminal energy identity
gives `H(M,P_B)=C(M)+T_B(M)`, where

`T_B(M)=∑_{B≤p<M, p prime} √p C(M/p)`.

The strong PNT bound `|ψ(x)-x|≤K x exp(-a√log x)` from
`ChebyshevPsiErrorInputs.exists_psi_error_eventually` implies, after
splitting the defining sum at `√y`,
`|C(y)|≤K' y^(3/2) exp(-a'√log y)` for sufficiently large `y`.
This also makes every logarithmic moment
`J_k=∫₁∞ C(y)y^(-5/2)(log y)^k dy` absolutely convergent.

For `s>1`, integrate the step function `F(floor t)` and use the von Mangoldt
Dirichlet series to obtain

`A(s):=∫₁∞ F(floor t)t^(-s-1)dt
      =(-ζ'(s)/ζ(s)-ζ(s)+2γ)/s`.
The exact identity, including step-source integrability, is now Lean-proved
in `MobiusDivisorCriticalStepMellinWeld`; it is expressed through the
centered-current gap.

The Lean theorem `tendsto_mobiusDivisorCriticalMellinMass_zero` proves
`A(1)=∑_{n≥1}F(n)/(n(n+1))=0`. Fubini, justified by the preceding bound,
gives for real `z≤0` near zero

`J(z):=∫₁∞ C(y)y^(-5/2+z)dy=A(1-z)/(3-2z)`.
This identity is now formalized for the open convergence half-plane
`Re z<0` in `MobiusDivisorCriticalAbelMellin` as a `HasMellin` theorem.
`MobiusDivisorCriticalChildAbelMellinWeld` proves that its real source is
exactly the clipped terminal child at every prime quotient. Convergence at
`z=0`, analytic continuation there, and differentiation of the literal
moment integral remain separate Lean obligations.

The right-hand quotient has an analytic extension through `z=0`: ζ has a
simple pole at `1`, while the two pole terms in `-ζ'/ζ-ζ` cancel. It is not
identically zero. Indeed, if `A(s)` vanished for all large real `s`, the
Dirichlet-series uniqueness limit as `s→∞` would give `F(1)=0`, then after
subtracting the first block and multiplying by `2^s` would give `F(2)=0`;
but `F(2)-F(1)=log 2-1≠0`. Hence some finite Taylor coefficient is nonzero.
The Lean weld now proves directly that the literal integral `A(s)` is
nonzero throughout a punctured right neighborhood of `s=1`, using the
already-proved finite analytic current jet. Thus nonflatness no longer
rests only on the paper Dirichlet-uniqueness argument.
Because `A(1)=0`, let `r≥1` be the first nonzero derivative of `J` at `0`
from the left. Differentiation under the integral is valid to every finite
order, so `J_r=J^(r)(0)≠0` and `J_k=0` for `k<r`.

Here is the weighted prime transfer, with no unproved short-interval PNT.
Put `L=log M`, choose any `0<β<1/2`, and set `Y=exp(L^β)`.
On primes `p≤M/Y`, the source bound gives, uniformly in `B`,

`∑_{B≤p≤M/Y} √p |C(M/p)|
 ≤ K M^(3/2) exp(-a'√log Y) ∑_{n≤M}1/n
 = o(M^(3/2)L^(-h))` for every fixed `h`.

On `x∈[M/Y,M]`, let `g_M(x)=√x C(M/x)`. This function is continuous and
piecewise `C¹`. Its total variation is at most `K√M Y`: under `y=M/x`,
the derivative of `y^(-1/2)C(y)` is bounded, since `|F(n)|=O(n)` and
`|C(y)|=O(y^(3/2))`. Its endpoint supremum is at most `K√M Y^(3/2)`.
The corpus's quantitative prime-counting estimate
`Sieve.PrimeCountingBigO.primeCounting_sub_logIntegral_isBigO`, namely
`|π(x)-Li(x)|≤K x exp(-b√log x)`, gives by Stieltjes integration by parts

`∑_{M/Y<p<M}g_M(p)
 =∫_{M/Y}^M g_M(x)dx/log x
  +O(M^(3/2) exp(-b'√L) Y^(3/2))`.

This error is smaller than every `M^(3/2)L^(-h)` because `β<1/2`.

An alternative discrete transfer now has an exact Lean foothold in
`MobiusDivisorCriticalPrimeQuotientBands`. On the band `n=floor(M/p)`, put
`A_n=∑_{k<n}(√(k+1)-√k)F(k)` and `B_n=A_n-√n F(n)`. Then the literal clipped
term is `√p C(M/p)=√M F(n)+√p B_n`. Therefore each band's prime contribution
depends only on its prime count and sum of `√p`; the nonsmooth moving weight
needs no global bounded-variation theorem. The corpus's `π` error and one
Abel summation give
`Σ_{p≤x}√p-∫₂ˣ √t/log t dt=O(x^(3/2)e^(-b√log x))` for some `b>0`.
Since `F(n)=O(n)` and `B_n=O(n^(3/2))`, the two prime-statistic errors cost
`O(M^(3/2)e^(-b'√L))` per band, uniformly for `n<Y`; the sum over `Y`
bands remains smaller than every `M^(3/2)L^(-h)`. The weighted `√p` PNT
error on every subband of `[X/e,X]` is now a Lean theorem in
`PrimeRpowStrongPNTBandTransfer`, simultaneously with prime count
(`a=1`). Converting quotient geometry to those bands and summing the
uniform errors remain Lean-open.

Substituting `y=M/x` turns the integral into

`M^(3/2)∫₁^Y C(y)y^(-5/2)/(L-log y)dy`.

The exact finite geometric expansion of `(L-log y)^(-1)` through degree `r`
has an integrated remainder `O(L^(-r-2))`, because `log Y=o(L)` and
`∫₁∞ |C(y)|y^(-5/2)(log y)^(r+1)dy<∞`. Replacing truncated moments by
full moments costs less than any power of `1/L` by the source tail bound.
Consequently

`T_B(M)=M^(3/2)(J_r/L^(r+1)+O(L^(-r-2)))`, uniformly in `B`.

Finally `C(M)=O(M^(3/2)exp(-a'√L))` is negligible. The terminal energy
identity includes `H²` plus a nonnegative singleton second moment, proving
the statement.

## Lean gap and route meaning

Lean now has the mass-zero theorem, terminal energy identity, exact clipped
finite Abel expression, full quotient-band disintegration, uniform subband
weighted-prime transfer, step-source Mellin identity, and the exact Mellin
transform of the same real Abel source sampled by terminal children on
`Re z<0`. Its transform is nonzero in a punctured right neighborhood of
the boundary. The remaining hard analytic gates are a uniform moving-band
PNT error sum, strong-PNT decay of the continuous Abel source, and the
boundary moment/differentiation theorem that identifies the first nonzero
logarithmic moment with the known finite current jet. Do not assume the
literal moment integral is analytic on a two-sided neighborhood. The
deterministic-prefix no-go is still a paper result, not a Lean theorem or an
RH proof; source-selected terminal cores remain live.

## Alternative boundary-regularity attack (new, not yet a closed no-go)

Put `C(x)=criticalContinuousAbel(x)` and `J(s)=∫₁∞C(x)x^(-s-1)dx`.
The new Lean theorem `MobiusDivisorCriticalPrimeMellinSingularity` proves
`J(3/2+δ)/δ^r→c≠0` for some finite `r≥1` and
`‖primeZeta(1+δ)J(3/2+δ)/δ^r‖→∞`. Its log-normalized version has finite
nonzero limit. This uses the formalized exact Abel Mellin identity, finite
current jet, and prime-zeta logarithmic asymptotic.

Consider the continuous full-prime head
`F(x)=C(x)+Σ_p √p C(x/p)` and its low-prime part
`L(x)=Σ_{p≤√x}√p C(x/p)`. The prime-dilation identity on real `s>3/2`,
`M_{F-C}(s)=primeZeta(s-1/2)J(s)`, is now proved in Lean by
`mellin_criticalPrimeAbelHead`, including the absolute-convergence
interchange. The same leaf proves a nonzero log-normalized Mellin boundary
limit for this **actual all-prime head**. No moving-cutoff prime asymptotic
enters. Quantitative PNT implies
`C(y)=O(y^(3/2)e^(-a√log y))` for some `a>0`. Hence
`L(x)=O(x^(3/2)(1+log x)e^(-a'√log x))`: for `p≤√x`, the decay at
`x/p≥√x` is uniform and `Σ_{p≤√x}1/p≤1+log x`. Therefore the Mellin
transform of `L` has all logarithmic derivatives finite at `s=3/2`.
The transformed terminal head `H=F-L` cannot be `C^r` at that boundary,
since its full-prime part retains the `δ^r log δ` singularity.

For integer `M`, choose square-root core `B=⌊√M⌋+1`. The existing
terminal transform identifies `H(M)` with its squared-head factor and gives
`E(M,P_B)≥H(M)^2`. A hypothetical uniform `E(M,P_B)=O(M²)` would make
`H(M)=O(M)`. To contradict boundary singularity, one still must prove
integer-to-real transfer: between integers the Abel primitive has
derivative controlled by `ψ(⌊x⌋)-⌊x⌋+2γ`, summed dilates vary by at most
`O(√x log x)` per unit interval, and crossing a prime-square selection
threshold changes the head by at most `O(x)`. Thus an integer `O(M)` bound
would imply a real `O(x log x)` bound, giving a Mellin transform analytic
around `s=3/2`, contradiction. The all-prime Mellin interchange is closed;
low-sector moment estimate, interpolation transfer, and final boundary
regularity contradiction are **not yet Lean-proved**. This is an alternative
attack, not a completed no-go.

## Reinterpretation and falsifier

The prime-sampling kernel is a resolvent in logarithmic scale:
`1/(log M-log y)`. Its expansion reads the successive Mellin moments of the
complete source. Thus the exact zeroth-moment cancellation is not, by itself,
payment of the terminal head: it exposes the first nonzero higher moment to
coherent prime sampling. The parameter-free, falsifiable consequence is
`E(N²,primes≤N)/N⁴ → +∞`. This is a candidate route-level reframe, not yet a
Lean theorem or a universal RH mechanism. A counterexample to the proposed
weighted-prime asymptotic, or a correction to the clipped-source identity,
would kill it. Even if proved, it selects against full deterministic prefixes;
it leaves exhaustive source-selected histories and their signed cross-scale
matching as the hard CCM-FU problem.
