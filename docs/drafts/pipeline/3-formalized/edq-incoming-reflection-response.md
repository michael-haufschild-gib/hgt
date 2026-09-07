# EDQ reflected incoming response and exact zero-pair balance

- **ID:** EDQ-IRR
- **Stage:** 3-formalized
- **Type:** THEOREM; paper proof and Lean audited
- **Source:** [current frontier](../1-in-progress/rh-current-frontier-map.md), [horizontal comparison](edq-incoming-horizontal-comparison.md)

## Full chain

Euler deletion → exact remainder and reflected zero-pair balance → signed source comparison of the incoming response, keeping all other sectors → off-line-zero exclusion → RH. The common positive critical head must cancel before attempting a sign selector. This component identifies its actual first horizontal response and controls the nonlinear error uniformly in height and cutoff.

## Source response

Let `delta=sigma-1/2`, `|delta|<=1/2`, `t=Im(s)`, and `K` any finite frequency cutoff. Define the critical logarithmic incoming moment

`L(t,K)=sum_(1<=k<=K) w_(-k)*integral_(1,t/(2*pi*k)] x^(-5/2)*log(x)*exp(i*(-2*pi*k*x+t*log(x))) dx`.

The exact amplitude difference is

`x^(-sigma-2)-x^(-(1-sigma)-2)=-2*x^(-5/2)*sinh(delta*log(x))`.

The corpus cubic inequality `sinh(a)-a <= a^3*cosh(a)/6`, together with oddness and `cosh(a)<=exp(abs(a))`, bounds the difference from `-2*delta*x^(-5/2)*log(x)` by

`abs(delta)^3/3*x^(-2)*log(x)^3`.

The exact third logarithmic moment is six, and the full one-sided coefficient mass is `1/24`. Hence the actual complex paired head obeys

`norm(H(s)-H(1-conj(s))+2*delta*L(t,K)) <= abs(delta)^3/12`.

The moment itself has bound `norm(L)<=1/54` from the first logarithmic moment at exponent `5/2`. For nonzero delta, division by `2*delta` therefore has an error at most `delta^2/24` around `-L`. The critical value is the actual logarithmic moment, not a value obtained by totalized division by zero. This supplies a uniform first-response approximation and no signed orientation for its complex moment.

## Complete zero-pair balance

For a strip zero `s`, its same-height reflection `r=1-conj(s)` is also a zero. Set `d=2*sigma-1`, `C=normSq(conj(s)*(1-conj(s)))`, `A=normSq(s+1)`, `B=normSq(2-s)`. Exact rational boundary and mean identities give

`Im(g(s,1)-g(r,1))=d*t/C`,

`mean(s)-mean(r)=-d*t/(4*A*B)`.

Thus the absolutely convergent difference of all literal Fourier atoms has imaginary sum

`d*t*(1/C-1/(4*A*B))`.

Every mode and the exact mean are retained. At strict-right zeros and positive height this is positive, since `A*B>C>0`. This is the required signed balance, not an independent proof that the source cannot attain it. The incoming cubic approximation must still be compared with the remaining actual sectors. RH remains open.

## Lean inventory

Leaf: `GaloisForLFunctions.RHTower.ArithmeticIncomingReflectionResponse`, namespace `RHTower.DeletionMixedRefinement`. 381 lines, 20 theorems and three definitions.

- `criticalIncomingLogMode`, `criticalIncomingLogAtom`, `criticalIncomingLogSection`: actual critical logarithmic source.
- `incoming_reflected_power_identity`, `incoming_reflected_power_cubic`, `incoming_logMoment_Ioc_le`: symbolic odd-power identity, cubic majorant, and exact logarithmic mass control.
- `norm_criticalIncomingLogSection_le`: full critical response norm at most `1/54`.
- `norm_stationaryIncomingSection_reflection_response_le`: uniform cubic remainder for the whole reflected incoming source.
- `norm_stationaryIncomingSection_divided_reflection_response_le`: quadratic error of the divided response for nonzero displacement.
- `normalizedWeightedRemainder_reflection_im_at_zero`, `reciprocalBernoulliMean_reflection_difference`, `hasSum_scaledBernoulliFourierAtom_reflection_im_at_zero`: exact boundary, mean, and complete mode balance.
- `incoming_reflection_denominator_gap`, `incoming_reflection_balance_pos`: strict positivity of the required full balance on the strict-right strip at positive height.

No numerical experiment, computational certificate, or added axiom is used. The conditional zero identities are general implications proved from the actual zero equation; they do not assert the existence of an off-line zero or remove that equation from the remaining RH task.

## Final verification

The full foreground scratch passed with no messages. `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticIncomingReflectionResponse` built only this leaf in 89 seconds; dependencies were replayed from cache. Its umbrella import is wired, and no umbrella or full build ran. Formal lint reported 10 other unwired modules: `UniformPrimeSubsetEnergy` and nine `HTGeometry.PolynomialODEOddCompact*` modules. It reported no issue in this leaf; shared-repository lint is not clean. These concurrently developed modules were left untouched. The corpus index was refreshed. All 23 new declarations were audited once; only `propext`, `Classical.choice`, and `Quot.sound` occur. No existing declaration was re-audited. All owned Lean processes exited, and the three temporary Lean sources were removed.

Logs: `/tmp/edq_reflection.check.log`, `/tmp/edq_reflection_build.log`, `/tmp/edq_reflection_axioms.log`, `/tmp/edq_reflection_lint.log`, `/tmp/edq_reflection_index.log`.

## Gates

- [x] Corpus research and exact source inspection.
- [x] Power identity, cubic majorant, moment integrability, uniform aggregate bound, and divided response.
- [x] Exact reflected boundary, mean, full Fourier balance, and positive required value.
- [x] Scratch, leaf wiring, targeted build, new-only axiom audit, lint run, ledgers, index, and cleanup.
- [ ] Global lint clean: ten unrelated unwired modules remain in concurrent work.
- [ ] Signed source exclusion at every off-line zero; RH.
