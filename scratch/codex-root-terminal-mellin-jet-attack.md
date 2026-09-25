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
all-cutoff quadratic control requires macroscopic, source-sensitive prime
selection capable of cancelling this coherent transformed head.

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

The Lean theorem `tendsto_mobiusDivisorCriticalMellinMass_zero` proves
`A(1)=∑_{n≥1}F(n)/(n(n+1))=0`. Fubini, justified by the preceding bound,
gives for real `z≤0` near zero

`J(z):=∫₁∞ C(y)y^(-5/2+z)dy=A(1-z)/(3-2z)`.

The right-hand quotient has an analytic extension through `z=0`: ζ has a
simple pole at `1`, while the two pole terms in `-ζ'/ζ-ζ` cancel. It is not
identically zero. Indeed, if `A(s)` vanished for all large real `s`, the
Dirichlet-series uniqueness limit as `s→∞` would give `F(1)=0`, then after
subtracting the first block and multiplying by `2^s` would give `F(2)=0`;
but `F(2)-F(1)=log 2-1≠0`. Hence some finite Taylor coefficient is nonzero.
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

Lean currently has the mass-zero theorem and terminal energy identity,
but not this full result. Next proofs should connect clipped child source to
`C(M/p)` and formalize weighted prime transfer using the existing `π-Li`
error. The analytic nonzero-jet step needs a precise ζ continuation and
Dirichlet uniqueness argument; do not assume the integral `J(z)` itself is
analytic on a two-sided neighbourhood. The statement is a route-selection
no-go, not a proof of RH and not a no-go for source-selected terminal cores.
