# Direct attack on the actual Weil pole sign

Status: the actual sign remains unproved. No new closed source estimate is claimed here.

Target: prove `H(a)≥2a[psi(exp(2a))+M1(exp(2a))]-A(a)-C_sm(a)` for the actual Mangoldt source, including its unbounded even-minimum range. Combine it with actual odd checkpoint signs to reach pole positivity → square-root integrated prime-error control → bounded critical resolvent → RH.

The generic Jensen/moment classification work is not pursued: it does not supply the required arithmetic sign. The attempts below concern that sign directly. They are proof attempts, not new formalized results or route retirements.

## Attempt 1: exact divisor renewal at the required square-root scale

Set `D(X)=X-1-sum_{2≤n≤X}Lambda(n)log(X/n)` for `X≥1`. This is the actual logarithmic integrated Chebyshev deficit. The exact divisor law `sum_{d|m}Lambda(d)=log m` gives

`sum_{1≤k≤X} D(X/k) = X H_floor(X)-floor(X)-sum_{1≤m≤X}log(m)log(X/m) =: F(X)`.

Derivation: expand every `D(X/k)` and regroup the finite prime sum by `m=kn`. Its coefficient is the full divisor sum, with `Lambda(1)=0`. Thus the ordinary integer lattice, rather than an auxiliary prime-weight model, supplies `F`.

The proposed proof was to control this recursion in the norm `sup |D(X)|/sqrt(X)`. It does not close. After isolating `k=1`, a positive majorization multiplies a putative bound by `sum_{2≤k≤X}1/sqrt(k)`, which grows with `X`; it is not a contraction. Exact finite inversion instead yields

`D(X)=sum_{1≤k≤X}mu(k)F(X/k)`.

This keeps the required cancellation in an actual signed Möbius sum. No estimate of that sum at square-root scale has been obtained. Reindexing alone is not progress on the sign. The corpus's `CCMCriticalMellinRieszMobiusRenewal` already gives a related exact collapse of complete Möbius–log dressing back to positive Mangoldt renewal, so it supplies no extra independent cancellation here.

## Attempt 2: use the positive actual prime–polar self-pairing

The corpus proves that midpoint evaluation at every prime jump gives the positive self-pairing `integral E dE = E(T)^2/2`, with the exact half jump-square correction retained (`CCMPolarPrimeMidpointCodiagonal`). I tested whether that result controls the actual even pole pairing.

For `f_a(x)=2cosh(x/2)` on `[-a,a]`, its overlap kernel on `0≤h≤2a` is

`K_a(h)=4sinh(a-h/2)+2(2a-h)cosh(h/2)`.

The actual diagonal-plus-cross Mangoldt atom is `Lambda(n)/sqrt(n) * K_a(log n)`; the even energy subtracts twice this atom. The relevant source pairing therefore uses this fixed `K_a`, not the source error `E` used by the positive self-pairing.

The attempted monotone-kernel comparison fails at the actual kernel:

`K_a'(h)=-2cosh(a-h/2)-2cosh(h/2)+(2a-h)sinh(h/2)`.

It is negative at `h=0` and positive at `h=a` for every `a≥8`. The derivative and these two signs passed `lake env lean` in the scratch file `/tmp/hgt-pole-direct-sign.1IP7IP/KernelCheck.lean`; no tree module was added for them. The positivity at the midpoint follows from `exp(a)>3`, hence `cosh(a/2)<2sinh(a/2)`, and `a≥8`.

Integration by parts consequently produces a signed weight against the actual source error. Also, the Stieltjes source has negative prime atoms, so Cauchy–Schwarz for a positive measure cannot be used to turn its positive self-pairing into an estimate for this fixed pairing. The explicit Gamma contribution is still required. No comparison controlling the residual mixed pairing has been proved. Since `K_a(2a)=0` and the source error starts at zero, the mixed integration-by-parts identity is `integral K_a dE + integral E dK_a = 0`. Thus the endpoint-square identity only fixes the symmetric part; the actual fixed-pole pairing retains the signed area. The required Gamma-versus-area comparison remains the direct target.

## Attempt 3: an invariant across actual prime entries

Let `Y=E_even`, `v=Y'`, and `F=Y''` inside a late prime-power gap. The candidate is `B=Y-v²/(2F)`, with `F>0`. Nonnegativity of `B` would imply the required nonnegativity of `Y`, and at an interior minimum `B=Y`. Direct differentiation gives `B'=v² F'/(2F²)` between entries. Establishing `F'≥0` alone would control only that continuous part.

At an actual prime-power entry `n`, put `b=log(n)/2` and `J=4Lambda(n)(1+exp(-b))²`. The value `Y` and one-sided curvature `F` agree across the entry; velocity changes from `v` to `v-J`. Consequently

`B_after-B_before = J(2v-J)/(2F)`.

The proposed monotone induction therefore requires `v_before≥J/2` at every genuine entry. This condition concerns actual arithmetic, not a free-weight model. A Runpod scan of all 148,798 genuine entries from the late-curvature threshold through 2,000,000 found 67,155 decreases. The first scanned entry, 2767, decreases the barrier by approximately 0.0700013595; an 80-digit recomputation agrees. The fallback that pays all negative jumps from initial barrier plus continuous growth already has a negative budget at 4733. At the final entry, continuous growth totals about 0.307, negative jump debt 396.959, and positive jump credit 548.068. Both propagation arguments are rejected as numerical leads. The outgoing barrier itself stays positive at every scanned entry; its all-aperture nonnegativity remains unproved and still requires signed arithmetic control. [Reproducible computations and report](../2-fully-proven/computations/weil-pole-entry-barrier-2026-09-06/REPORT.md). No numerical output is used in Lean.

## Attempt 4: center the integrated divisor renewal before inversion

The conjectured producer was that removing the explicit main term from the exact integer-lattice
forcing in Attempt 1 would make the actual inverse sum small enough at square-root scale.
The following paper calculation does make the forcing small, but the proposed absolute estimate
still fails. These deductions have not been promoted to new Lean theorems; the route is not retired.

Let `N=floor X`, `T=log X`, `c=1+gamma`, and

`F(X)=X H_N-N-sum_{1≤m≤X}log(m)log(X/m)`,
`G(X)=F(X)-c floor X`, for `X≥1`.

The full divisor identity and finite Möbius inversion give exactly

`D(X)=c+sum_{1≤n≤X}mu(n)G(X/n)`.

Indeed `sum mu(n) floor(X/n)=1`, so subtracting the floor main term has a known constant inverse.
There is no prime truncation or alteration of the Mangoldt coefficients.

**The centered forcing is logarithmically bounded.** Put `f_X(t)=log(t)log(X/t)` on `[1,X]`.
Its integral is `X log X-2X+log X+2`, and its total variation is `(log X)^2/2`.
Integration against the fractional part therefore gives

`epsilon_Q=sum_{m≤X}f_X(m)-integral_1^X f_X(t)dt`, `|epsilon_Q|≤T²/2`.

The harmonic estimate `|H_N-log N-gamma|≤1/N` and `0≤log(X/N)≤1/N` give
`|epsilon_H|<4`, where `epsilon_H=X(H_N-log X-gamma)`.
Consequently

`G(X)=(2+gamma){X}-T-2+epsilon_H-epsilon_Q`,
`|G(X)|≤T²/2+T+9`.

**Small forcing does not make its absolute inverse small.** For `1≤y<2`, the exact kernel is
`G(y)=y-2-gamma`, hence `|G(y)|≥gamma>0`. Thus, without replacing the actual inverse weights,

`sum_{n≤X}|mu(n)G(X/n)| ≥ gamma sum_{X/2<n≤X}mu(n)^2`.

The existing `RHTower.Sieve.tendsto_window_squarefree_density` in
`Sieve/SquarefreeDyadicDensity.lean`, together with `squarefreeDensity_eq`, makes the right side
asymptotic to `3gamma X/pi²`. In particular the absolute inverse cannot be `O(sqrt X)`.
This failure comes from actual squarefree labels in the last dyadic interval, where the argument
of the forcing stays between one and two; it is not caused by its large-argument error estimate.

**Pivot retaining signs.** On that same interval the exact signed contribution is

`X sum_{X/2<n≤X}mu(n)/n-(2+gamma)sum_{X/2<n≤X}mu(n)`.

It must remain combined with the smaller-index contribution. Neither the small forcing bound nor
the squarefree density law controls this signed quantity, or its cancellation with the rest.
The unconditional Selberg core bound `abs_psiDefect_selberg_core` supplies an `O(N)` estimate for
a different convolution, which is also too large for the required square-root conclusion.
No signed inverse bound has been obtained. The surviving useful information is the explicit
centered kernel and its small forcing bound; this is a paper-level reduction, not an RH producer
or a completed formal no-go.

## Hard obligation retained

Supply a source-derived signed estimate for the actual prime–polar–Gamma pairing at the even minimum, or a square-root estimate for the exact divisor-inverted error. Neither the renewal identity nor the positive self-pairing provides it. Derivative bounds, generic moment bounds, and additional equivalent criteria are not accepted as closing this obligation.

No RH proof, new proved value inequality, new axiom, or tree Lean module is claimed by this card. The scratch check and both foreground Runpod computations completed. The frontier records the failed experimental leads explicitly as numerical evidence; no universal proved-status entry is added for them.

## Source normalization and the required constant

The reciprocal cumulative includes **every prime power**. The existing closed theorem
`RHTower.tendsto_sum_vonMangoldt_div_sub_log` in `MertensSecondTheorem.lean` states that
`sum_{n≤N}Lambda(n)/n-log N -> -gamma`. The prime-only constant must not be substituted here.

Put `X=exp(2a)`, `T=2a`, `kappa=-gamma-log(2pi)`, `epsilon_M=E_M(T)+gamma`,
`E_psi=psi(X)-X`, and `delta=2+gamma-log(4pi)`. The exact diagonal identity gives

`A(a)=delta*sqrt(X)-2sqrt(X)*epsilon_M+2E_psi/sqrt(X)`
`     +[B1(a)-(1-log 2)sqrt(X)]+(1-T-kappa)/sqrt(X)`.

In particular the reciprocal-error term cannot be dropped into an `O(a²)` remainder without
an additional rate theorem. From the boundary primitives,

`B1(a)/exp(a) = (1/2) integral_0^T exp(-t)L(2t)dt`
`               + exp(-T) integral_0^T exp(t)[L(t)-L(2t)/2]dt -> 1-log 2`.

For the first limit, `u=exp(-t)` gives
`integral_0^1 -log(1-u²)du=2-2log 2`. In the second term,
`L(t)-L(2t)/2=atanh(exp(-t))`; beyond `t=log 2` its product with `exp(t)` is at
most `4/3`, and the initial integral is finite. Thus that term vanishes. Combining these
paper deductions with the corpus PNT and full Mangoldt Mertens limit gives
`A(a)/exp(a) -> delta`. The displayed limit for the actual diagonal has not been added as a
new Lean theorem here. There is no justified factor-27 allowance.

**A sharp constant is not required to prove RH through this chain.** The existing
`riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound` quantifies over **any** finite
nonnegative constant `B` in `|D(X)|≤B sqrt(X)` for all `X≥1`. Such a bound proves RH and then
recovers the exact pole positivity. Therefore the assertions that every constant loss is fatal,
or that no sieve or mean-value input could contribute, do not follow from the normalization.
No assertion about a zero infimum of the normalized parity energy is made without the additional
spectral and phase-approximation hypotheses it needs.

### Stationary normalization retains the signed source

Set `I=integral_1^X (psi(u)-u)du/u`, `R=integral_0^T E_M(t)dt`, `r=exp(-T)`, and
`L=L(T)`. Existing cross and first-jet identities give, inside a prime-power chamber,

`E_even-E_even'/2 = (2A-A')+2E_psi-2I+2kappa(T-1)+4r-2+2B0-2L-2R+2E_M(T)`.

In particular the retained point-error and integrated-error terms have signs `+2E_psi-2I`.
At an interior minimum the left side is the energy itself. Stationarity controls `E_psi` there;
it does not bound `I`. This normalization has not supplied the missing arithmetic comparison.

Verification: the coefficient simplification and stationary algebra passed `lake env lean`
in `/tmp/hgt-pole-renewal.VbKJRf/NormalizationCheck.lean`, using only mathlib. The full Mertens
limit and RH transfer were inspected in their existing source modules. A scratch import of
`MertensSecondTheorem` encountered the currently missing transitive
`MobiusLaplaceBoundaryMultiplicity.olean`; no successful dependency re-audit is claimed.
