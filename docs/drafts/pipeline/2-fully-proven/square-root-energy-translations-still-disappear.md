# Square-root-energy translations still disappear

- **ID:** square-root-energy-translations-still-disappear
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-2410/opus.md`, Mechanism A and Q-III; `FixedSuccessorsDisappearFromEscapingProfiles.lean`.
- **Statement:** For the actual damped Möbius receiver, every moving successor of length `O(sqrt(E))` has vanishing normalized displacement on escape.

## Paper proof

Fix `0 < epsilon < 1/2` and write `A(n)` for the centered receiver prefix.
The corpus proves `|A(n+k)-A(n)| <= k`. Its all-damping hyperbola estimate,
with splitting parameter `D=n` and the elementary bound
`|sum_{e<=x} mu(e)| <= x`, also gives

`|A(n)| <= (3 + 13/epsilon) n^(1-epsilon)` for `n >= 1`.

Consequently `A(n)/n -> 0`. No zero-free estimate is required.

Define, for `k >= 1`,

`b(k) = sum_{n>=1} ((A(n+k)-A(n))/k)^2 / (n(n+1))`,

and put `b(0)=0`. Each summand is nonnegative and bounded by
`1/(n(n+1))`; these weights sum to one. For fixed `n`, sublinearity gives
`(A(n+k)-A(n))/k -> 0`. Dominated convergence therefore proves `b(k)->0`.
At every horizon `T`, the displacement energy obeys

`0 <= D(k,T) <= k^2 b(k) <= k^2`.

Let `E(T)->infinity` and let `k(T)^2/E(T) <= C` eventually, increasing
`C` to at least one if needed. Given `eta>0`, choose `K` such that
`b(k) < eta/(2C)` for `k>=K`. For these lengths,
`D(k,T)/E(T) < eta/2`. For `k<K`, the coarse budget gives
`D(k,T)/E(T) <= K^2/E(T)`, which is below `eta/2` eventually.
Hence the normalized displacement tends to zero. This proof does not assume
`k(T)->infinity`.

Equivalently, every positive tolerance `delta` admits a constant `B_delta`
with `D(k,T) <= delta*k^2+B_delta` simultaneously for all lengths and
horizons. This uniform subquadratic budget is the positive structural result.

## No-go closure

- **Exact killing mechanism:** Sublinearity and summable pronic mass improve
  the quadratic increment estimate to a uniform little-oh quadratic budget.
- **Strongest positive survivor:** Uniform subquadratic successor energy and
  collapse of every translation with bounded `k^2/E`; nonvanishing along a
  subsequence forces that ratio to be unbounded there.
- **New insight:** The report's proposed `k ~ sqrt(E)` scale is still too
  small. Its original quadratic estimate supplied only a necessary lower
  bound, not a scale supporting a nontrivial translation action.
- **Status:** Dependency-closed paper proof above. Lean formalization and
  transitive axiom audit pending. The no-go is not closed.

## Next conjecture

The same power bound, splitting the pronic sum at `n=k`, suggests
`D(k,T) <= C_epsilon k^(2-2epsilon)` uniformly in `T` for `k>=1`:
use the power bound on `n<=k` and the increment bound on the tail, whose
pronic mass is at most `1/k`. This quantitative refinement is separate
from the proved qualitative argument above and remains to be formalized.

## Gates

- [x] Exact actual-source inputs checked.
- [x] Dependency-closed paper proof.
- [ ] Lean proof, axiom audit, final check, umbrella import.
- [ ] Apply the corrected scale throughout the Q-III analysis.

## Stronger survivor: translations carry an origin trace

The uniform quadratic remainder has a sharper decomposition. Put
`r_k(n)=A(n+k)-A(n)-A(k)`; the zero-origin prefix and unit increment bound give

- for `n<=k`, `|r_k(n)| <= |A(n+k)-A(k)|+|A(n)| <= 2n`;
- for `n>k`, `|r_k(n)| <= |A(n+k)-A(n)|+|A(k)| <= 2k`.

The head pronic energy is at most `4k`, since
`n^2/(n(n+1)) <= 1`. The tail is at most
`4k^2 sum_{n>k}1/(n(n+1)) = 4k^2/(k+1) <= 4k`.
Consequently, at every horizon,

`||A(.+k)-A(.)-A(k)||_pronic^2 <= 8k`.

This is a dependency-closed paper proof from the existing unit increment bound.
On escape, every translation with `k=o(E)` is therefore, in normalized pronic
norm, the constant row `A(k)/sqrt(E)` plus a vanishing remainder. If this scalar
converges to `a`, its surviving displacement is exactly `a` times the constant
pronic vector. Thus all such translation effects occupy one origin-boundary
coordinate. They do not provide an additional diffuse escape coordinate.

For `k=O(sqrt(E))`, sublinearity gives `A(k)/sqrt(E)->0`; the linear remainder
budget gives collapse again. This decomposition is stronger than the initial
little-oh quadratic bound and must also be formalized before closing the no-go.

## Sharp source refinement

The actual uncentered divisor response lies in `[0,1]`. Therefore the difference
between any two centered increments has absolute value at most one. Summing
`n` such differences gives `|r_k(n)|<=n`; symmetry gives `|r_k(n)|<=k`.
Thus the actual source satisfies the sharper pointwise law

`|A(n+k)-A(n)-A(k)| <= min(n,k)`.

Its total pronic envelope is exactly

`sum_{n>=1} min(n,k)^2/(n(n+1)) = 2k-H_k`,

where `H_k=sum_{n=1}^k 1/n`. Hence the uniform remainder budget improves from
`8k` to `2k-H_k <= 2k`. The envelope is sharp for the class of prefix rows with
increments in an interval of width one: the hinge prefix `v(n)=max(n-k,0)`
has additive defect exactly `min(n,k)` for the specified shift `k`.
This sharp source refinement and the origin-trace classification are the
strongest positive survivor currently exposed. Lean work remains pending.
