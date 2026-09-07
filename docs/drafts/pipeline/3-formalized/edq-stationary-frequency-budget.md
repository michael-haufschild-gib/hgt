# EDQ: finite stationary-frequency budget

- **Stage:** 3-formalized
- **RH chain:** literal Euler deletion → actual weighted remainder → source comparison through the exceptional head → exclusion of every off-line zero → RH
- **RH status:** unproved. This target compares the nonstationary infinite sectors and isolates the remaining finite contribution.

## Proved source theorem SFB

Let sigma=Re(s)>0, t=Im(s)>0, integer N>=1, and beta=sigma+2. Define the scaled literal Fourier atom

`A_k = N^(conj(s)+1) * integral_N^infinity bernoulliFourierTerm(k,conj(s),x) dx`.

The exact source sum is

`sum_k Im(A_k) = N^(2*sigma+1)*Im(g_s(N)) + t/[12*normSq(s+1)]`.

For positive k, the reciprocal-clock positive identity bounds

`0 < Im(A_k) <= 2*w_k/(2*pi*k*N+t)`.

The positive coefficient mass is exactly `sum_(k>0) w_k=1/24`. Thus all positive-frequency terms together are at most `1/[12*(2*pi*N+t)]`. For negative frequencies with `2*pi*k*N>t`, the actual term is strictly negative. Retain exactly the finite stationary sector

`S_N = sum_(1<=k<=floor(t/(2*pi*N))) Im(A_(-k))`.

The Lean-proved comparison is

`N^(2*sigma+1)*Im(g_s(N)) <= S_N + 1/[12*(2*pi*N+t)] - t/[12*normSq(s+1)]`.

Paper proof: apply the already proved anchored reciprocal-clock identity with amplitude x^(-sigma-2), frequency 2*pi*k, and gamma=t, then multiply by positive N^(sigma+1). Integer N removes the Fourier endpoint phase. The powers cancel exactly in the upper bound. Reflection of the even Bernoulli weights and their total mass 1/12 gives half mass 1/24. Sum the pointwise comparison using absolute summability, retaining every stationary mode. No numerical estimate is used.

## Proved consequences

For `0<sigma<=1`, `t>=1`, and `N>=1`, `(sigma+1)^2 < 2*pi*N*t`, so the displayed error after S_N is strictly negative. Therefore the scaled source is strictly below S_N at every such parameter. If `t<2*pi*N`, the stationary set is empty and `Im(g_s(N))<0` follows. This proves the frozen R threshold in the strip and height range relevant here, without asserting R for all sigma>0 and t>0.

At high unit zeros the stationary set need not be empty. Its source-dependent magnitude must still be compared with the retained sectors and mean. No nonpositivity of the stationary sector is assumed; critical zeros require its positive contribution. The theorem is not an RH proof.

## Corpus ancestry and plan

Whole-corpus searches for paired Fourier phases, sine transforms, Laplace cosine, Bernoulli integrals, and positive/negative sums identify `ArithmeticUnitFourierOrientation`, `ArithmeticLogarithmicFourierTail`, the general sine-transform integration-by-parts mechanism, and even-integer sum splitting. No imported RH premise or new spectral model is used. No novelty claim is made.

- [x] Prove scaled actual-source Fourier identities at every integer anchor.
- [x] Compare positive coefficient mass, positive-frequency ceiling, and finite stationary budget.
- [x] Derive the sharper strict strip cutoff and retain the high-unit obstruction.
- [x] Scratch checks, one leaf at a time, new-only axiom audit, umbrella wiring, and global lint.
- [ ] Supply the remaining independent source comparison and close RH.

## Necessary positive stationary contribution at zeros

At a strip zero, the exact unit boundary gives the proved lower bound

`S_1 >= t*(2*sigma-1)/[2*normSq(conj(s)*(1-conj(s)))]`

`       + t/[12*normSq(s+1)] - 1/[12*(2*pi+t)]`.

For `1/2<=sigma<1` and `t>=1`, this lower bound is strictly positive. In particular the finite stationary budget is positive at every critical-line zero in this range. Assuming it nonpositive would exclude intended zeros as well. The survivor must compare its actual size with the exact retained opposing sectors and mean, or use a different joint-signature constraint. This is a necessary zero condition, not an independent RH selector.

## Formal scope and audit

`formal/GaloisForLFunctions/RHTower/ArithmeticStationaryFourierBudget.lean`, namespace `RHTower.DeletionMixedRefinement`: 25 new declarations, comprising 21 theorems and four definitions.

- `hasSum_scaledBernoulliFourierAtom_im`: exact source occurrence at every integer anchor.
- `tsum_positiveBernoulliWeight`: exact positive coefficient mass `1/24`.
- `normalizedWeightedRemainder_scaled_im_le_stationary_budget`: complete finite-budget bound with explicit signed error.
- `normalizedWeightedRemainder_scaled_im_lt_stationary_budget`: strict comparison throughout `0<sigma<=1`, `t>=1`.
- `normalizedWeightedRemainder_im_neg_of_subresonant`: full source sign for `t<2*pi*N` in that strip and height range.
- `stationaryFourierBudget_lowerBound_at_zero`, `stationaryFourierBudget_pos_at_closed_right_zero`: explicit necessary finite contribution and its strict positivity.

The Lean index set uses the corresponding negative integer interval `[-floor(t/(2*pi*N)),-1]`; `mem_stationaryFourierIndices` proves its exact stationary interpretation, including boundary equality. All source powers and the Bernoulli mean are retained. No numerical result or added source-sign premise enters any proof.

Foreground scratch passed. Only the new leaf was compiled in the final targeted build (4.4 seconds). Umbrella is wired and was not built. All 25 new declarations have only `propext`, `Classical.choice`, and `Quot.sound`. Global formal lint passes with the concurrent modules wired. The follow-on stationary-dilation audit checked this tree-wide lint state without rebuilding this leaf or repeating its axiom audit. Own scratch sources and Lean processes are cleaned up after the audit.

The retained finite sector has an exact full-complex dilation law and finite Möbius inverse: see [the stationary-frequency dilation certificate](edq-stationary-frequency-dilation.md). This reconstructs a truncated first-harmonic profile and does not close the source comparison.

The [signed stationary-endpoint extension](edq-stationary-endpoint-orientation.md) proves strict negativity of the literal boundary-frequency atom and includes equality in the strip remainder cutoff `t<=2*pi*N`. Positive first-harmonic witnesses forced by closed-right zeros lie strictly inside `2*pi*N<t`; the complex reconstruction retains its known-negative boundary atom. The interior-head comparison remains open.
