# Square-root-energy translations still disappear

- **ID:** square-root-energy-translations-still-disappear
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-2410/opus.md`, Mechanism A and Q-III; `FixedSuccessorsDisappearFromEscapingProfiles.lean`.
- **Statement:** For the actual damped Möbius receiver, every moving successor of length `O(sqrt(E))` has vanishing normalized displacement on escape.

## Current formalization coverage

The uniform subquadratic raw budget, square-root-scale disappearance, sharp
additive-defect envelope, exact capped-row cost, origin-trace decomposition,
and recentered energy-scale disappearance passed canonical source checks and
standard-axiom audits. Their owners are `TheOriginTraceControlsMovingSuccessors`,
`TheExactPronicCostOfACappedRow`, and `RecenteredSuccessorsVanishAtTheEnergyScale`.
The stronger source-power refinement is already in
`3-formalized/the-source-power-saving-enlarges-the-invisible-translation-scale.md`.

All reset/raw moving-origin Gram and faithful boundary-module consequences,
boundary dimension/index, scalar origin-trace convergence in pronic norm,
and the unbounded squared-length/energy obstruction along nonvanishing cofinal
subsequences passed final canonical checks. The exact declarations and audits
are recorded below and in
[the completion ledger](../1-in-progress/q-iii-existing-findings-lean-completion.md).

## Proof mechanism

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
- **Status:** The raw square-root collapse, positive origin-trace survivor,
  reset/raw boundary consequences and exact dimension/index refinements all
  passed final canonical checks and standard-axiom audits.

## Stronger raw source-power bound

The same power bound, splitting the pronic sum at `n=k`, suggests
`D(k,T) <= C_epsilon k^(2-2epsilon)` uniformly in `T` for `k>=1`.
The stronger result is already formalized in
`TheSourcePowerSavingControlsMovingSuccessors`:
`successorPowerRatioBudget_tendsto_zero` and
`exists_uniform_subpower_successor_budget` give a uniform little-oh bound
at this power, and `admits_or_sourcePower_successors_disappear` gives its
escape consequence. The corresponding source-power card is in `3-formalized`.

## Gates

- [x] Exact actual-source inputs checked.
- [x] Dependency-closed paper proof.
- [x] Lean proof, axiom audit, final check, umbrella import.
- [x] Apply the corrected scale throughout the Q-III analysis and report.

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
little-oh quadratic bound. Its exact pronic-norm convergence is formalized as
`normalized_successor_tendsto_origin_trace` in
`MovingSuccessorLimitsAreOriginTraces`.

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
This sharp source refinement and the origin-trace decomposition are positive
survivors. The sharp envelope and raw square-root-scale collapse passed
Lean, standard-axiom audits and final source-only checks.

## Zero-origin translations and the corrected surviving scale

A translated prefix with the same zero-origin convention is
`tau_k A(n)=A(n+k)-A(k)`. Its difference from `A` is precisely `r_k`.
The sharp source bound therefore implies

`||tau_k A-A||_pronic^2 <= 2k-H_k <= 2k`.

Consequently **every recentered translation with `k=o(E)` becomes the identity
on the normalized actual receiver**, without any sublinearity premise. A
nontrivial recentered successor scale must reach at least order `E`, stronger
than the report's order `sqrt(E)` lower bound.

This distinction matters for the dilation action. The raw translated row has
value `A(k)` at index zero; the sharp cofactor contraction requires zero-origin
rows. Pronic norm does not see the value at zero, but floor dilation does: it
copies that value onto the first `j-1` positive cells. Thus the raw origin trace
cannot be silently inserted into the same contractive Wiener module. Resetting
the origin preserves the source convention and exposes the linear translation
budget above. No new bounded translation representation has yet been proved.

## The recentered budget is little-oh linear

Sublinearity improves the recentered defect budget from `O(k)` to `o(k)`,
uniformly in the horizon. Here is a finite-sum proof. Fix an integer `q>=1`
and split at `floor(k/q)` and `q*k`. The head costs at most `k/q` by the
`min(n,k)` envelope. The tail costs at most `k^2/(q*k+1)<=k/q`.
For any `a>0`, sublinearity supplies `N` with `|A(m)|<=a*m` for `m>=N`.
For `k>=q*N`, every index in the middle segment and all three arguments in
`r_k(n)` exceed `N`. Therefore `|r_k(n)|<=2a(q+1)k`. Its pronic mass is at
most `1/(floor(k/q)+1)<=q/k`, so the middle costs at most
`4a^2*q*(q+1)^2*k`. Thus the whole energy divided by `k` is at most
`2/q+4a^2*q*(q+1)^2`. First choose large `q`, then small `a`.
This proves the uniform little-oh linear law without a limit exchange.

The same bounded/large-length split used for raw translations now proves that
every recentered translation with bounded `k/E` disappears on escape.
This consequence passed final canonical verification in
`RecenteredSuccessorsVanishAtTheEnergyScale`; its source-power strengthening
is also formalized. The old scratch status is superseded.

## Origin reset and its boundary module

Recentring subtracts `A(k)` at every cell. A different operation resets only
index zero: `B_k(0)=0`, `B_k(n)=A(n+k)` for positive `n`. Define
`u(0)=0`, `u(n)=1` for positive `n`. Then exactly
`B_k=A+r_k+A(k)u`. The strengthened recentered estimate makes the remainder
disappear whenever `k/E` is bounded. Every fixed
dilation of `u` is the step row `1_{n>=j}`, whose limiting covariance is
`1/max(j,l)`. Its cross pairing with each normalized actual cofactor row
tends to zero on escape: fixed cells vanish and the fixed step row has
summable pronic square mass.

Consequently, if `A(k)/sqrt(E)` converges to a finite scalar `b`, these
zero-reset moving profiles have Gram limit `K+b^2/max(j,l)` at the original
receiver scale, or `(K+b^2/max(j,l))/(1+b^2)` at their own scale. This is a
structural consequence of the stated trace limit. The record construction
realizes every positive squared boundary mass on escape, without asserting
any particular escaping damping. The step-row module is faithful: applying a
Wiener kernel to its cyclic vector gives its finite prefix sums, so zero
action forces every coefficient to vanish. Thus a surviving reset-origin
component has the full Bohr hull. It need not preserve the original
paid-ideal bridge automatically. This distinguishes raw translation,
recentring, and a reset at one cell; they cannot share an unproved action law.
These consequences passed final canonical source checks and Lean axiom audits.

The raw, unreset row has a different boundary term: its displacement is
`r_k+A(k)` including at index zero. Dilation preserves this constant row, so
its limiting boundary Gram is constant `b^2`, rather than `b^2/max(j,l)`.
A nonzero constant row violates the sharp zero-origin contraction and cannot
be inserted into the original critical Wiener action. This pinpoints the
domain change caused by raw translation.

For the reset-origin kernel, faithfulness survives even if the cyclic Gram
realization is only a subspace of the ambient orthogonal sum: projecting its
cyclic orbit to the step-row factor gives the full step-row cyclic orbit.
An annihilating operator must therefore kill that orbit, forcing every Wiener
coefficient to be zero. No claim that the cyclic subspace splits as an
orthogonal direct sum is needed.

## Lean proof route consolidated around the origin trace

The exact decomposition also gives the simpler uniform estimate

`D(k,T) <= 4k + 2 A(k)^2`,

by `(r_k(n)+A(k))^2 <= 2r_k(n)^2+2A(k)^2` and pronic mass at most one.
Sublinearity now yields the uniform little-oh quadratic budget directly:
`(4k+2A(k)^2)/k^2 = 4/k+2(A(k)/k)^2 -> 0`.
This replaces the planned dominated-series implementation for the same theorem.
The initial dominated-convergence paper proof remains valid, but its temporary
Lean draft can be superseded by this stronger shared origin-trace argument.

## Explicit trace and nonvanishing-scale corollaries

`MovingSuccessorLimitsAreOriginTraces` proves the quantitative squared-error
bound `4*k/E + 2*(A(k)/sqrt(E)-a)^2`, then both energy and pronic-norm
convergence to the constant trace under `k/E -> 0` and `A(k)/sqrt(E) -> a`.
It also proves `admits_or_nonvanishing_successors_require_unbounded_scale`:
along every cofinal horizon sequence on escape, failure of normalized
displacement to tend to zero forces `k^2/E` to exceed every real bound
frequently. This retains the subsequence quantifiers from the no-go survivor.

The exact application declarations are
`normalized_successor_tendsto_origin_trace` and
`admits_or_nonvanishing_successors_require_unbounded_scale` in namespace
`GaloisForLFunctions.ArithmeticDefectRigidity`. Final canonical source check
`80601` passed; both transitive audits contain only `propext`,
`Classical.choice`, `Quot.sound`. The umbrella import is wired.
