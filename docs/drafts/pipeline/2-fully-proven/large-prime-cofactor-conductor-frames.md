# Composite conductor frames beyond the square-root horizon

- **Stage:** 2-fully-proven.
- **Type:** THEOREM (paper); Lean pending.
- **Wall:** Σ1e.
- **Statement:** For `1/2<θ<1`, `ε>0`, and `θ+2ε<1`, the normalized Ramanujan vectors with conductors `dp`, `d≤N^ε`, `sqrt N<p≤N^θ` prime, have a uniform positive lower frame bound.

## Frontier

`primeConductorBand_lower_frame` treats prime conductors only. Whole-prefix frames require the square-root horizon. The proposed family allows a growing composite cofactor and arbitrary mixtures across both indices. It supplies a frame, not a prime-residual estimate.

## Derivation

Write the unnormalized profile sum as `X=S−B`. Coprime multiplicativity makes `S` a sum of spikes on the multiples of the large primes; their supports are disjoint below `N`. The background `B` is a packet of conductors at most `D=floor(N^ε)`.

On the multiples of `p`, multiplication by `p` preserves each small conductor mode. Thus the spike square mass equals a sum of small-conductor packet masses at horizons `floor(N/p)`. The square-root frame there gives

`‖S‖² ≥ (1−θ−2ε) log N Σ_(p,d) a_(p,d)²`.

Before `M=floor(sqrt N)` every spike vanishes, so `X=−B`. Put `δ=1/2−2ε>0`. The lower frame uses `log(M+1)`, which is at least `log N/2`; thus `δ log N Σ b_d²≤‖B|_[1,M]‖²`. The upper frame on the full horizon gives `‖B‖²≤6 log N Σ b_d²`. Hence `δ‖B‖²≤6‖X‖²`. Squaring `S=X+B` and using `δ≤1/2` gives `δ‖S‖²≤13‖X‖²`.

After logarithmic normalization, the proposed lower constant is

`(1−4ε)(1−θ−2ε)/26`.

All norms in this derivation are finite harmonic row sums. This holds already when `4 exp(7)≤log N` and `2≤D≤N^ε`. Indeed `ε<1/4` gives `D²≤N` and `D<sqrt N<p`, hence coprimality. Distinct primes have product greater than `N`. Finally `N/p<floor(N/p)+1` gives `log(floor(N/p)+1)≥(1−θ)log N`, proving the spike bound without a floor loss. These discharge every analytic and geometric input.

## Gates

- [x] Corpus novelty check: prime-only and whole-prefix frame results located; no cofactor-family theorem found.
- [x] Dependency-closed paper proof with precise floor inequalities.
- [ ] Lean theorem, leaf check, transitive axiom audit, umbrella import.
