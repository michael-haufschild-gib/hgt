# EDQ stationary tails and the reflected arithmetic partial sum

- **ID:** EDQ-SRT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [current EDQ frontier](../1-in-progress/rh-current-frontier-map.md), [exact frequency dilation](edq-stationary-frequency-dilation.md)
- **Statement:** Every outgoing stationary tail factors through one actual complex first-frequency tail; summing the factors produces the ordinary partial sum at `1-conj(s)`, retaining cancellation between frequencies.

## Goal and scope

Proof chain: Euler deletion → actual remainder → full stationary-head comparison → exclusion of off-line zeros → RH. This component treats cancellation across the whole outgoing stationary frequency sum. The desired comparison must still control the retained pre-saddle heads. No source-sign input, numerical certificate, or claim of RH is introduced.

## Dependency-closed paper proof

For `s=sigma+it`, `sigma>0`, `t>0`, let `B=t/(2*pi)` and `b_k=B/k`. Exact integer dilation of the literal Bernoulli integrand gives

`term(-k,conj(s),x)=k^conj(s)*term(-1,conj(s),k*x)`.

Changing variable on `(b_k,infinity)` includes the Jacobian `1/k`. Consequently its normalized tail is exactly

`T(s,N,k)=C(s,N)*k^(conj(s)-1)`,

where `C(s,N)=N^(conj(s)+1)*integral_B^infinity term(-1,conj(s),x) dx` is fixed across frequencies. For every positive finite frequency set, the tail sum is `C` times its reflected Dirichlet polynomial. Its norm is exactly the product of norms, preserving cancellation before any upper estimate.

For a stationary prefix `1<=k<=K`, all `b_k>=N`. Absolute integrability splits each actual atom into its finite pre-saddle head and its outgoing tail. Thus the full complex frequency sum is

`H(s,N,K)+C(s,N)*rawPrefix(1-conj(s),K)`.

The existing centered power-sum remainder gives an exact expression for that reflected prefix, retaining its zeta value, pole, half endpoint, and remainder. At a strip zero, reflection and conjugation cancel only the reflected zeta term; the other terms remain. Bounds must preserve those retained contributions. This identity does not itself assign their signs.

## Quantitative comparison

The common kernel is also bounded before the arithmetic coefficient sum is estimated. For `a>0`, `beta>1`, `t>=1`, `omega>0`, `omega*a=t`, split the literal logarithmic mode at `2*a`. On `[a,2*a]`, the phase second derivative is at most `-t/(2*a)^2`; the existing weighted second-derivative theorem bounds its norm by `20*a^(1-beta)/sqrt(t)`. Beyond `2*a`, conjugation gives a phase derivative at least `omega/2`. The first-derivative theorem and the proved improper limit give `8*(2*a)^(-beta)/omega <= 8*a^(1-beta)/sqrt(t)`. Therefore the complete outgoing integral is bounded by `28*a^(1-beta)/sqrt(t)`.

With `B=t/(2*pi)`, define the explicit nonnegative ceiling

`Q(s,N)=28*N^(sigma+1)*w_1*B^(-sigma-1)/sqrt(t)`.

The actual common factor obeys `norm(C(s,N))<=Q(s,N)`. Hence the entire outgoing frequency sum obeys `norm(T_total)<=Q(s,N)*norm(rawPrefix(1-conj(s),K))`. This magnitude estimate uses the complete arithmetic coefficient sum.

At a strip zero and `K>=1`, the retained endpoint identity and the existing centered-remainder bound imply

`norm(rawPrefix(1-conj(s),K)) <= K^sigma/norm(s) + K^(sigma-1)/2 + norm((1-conj(s))*(2-conj(s)))/(2-sigma)*K^(sigma-2)`.

Call this parameter-only ceiling `P(s,K)`. Then the entire outgoing sector is bounded by `Q(s,N)*P(s,K)` at each strip zero. Every closed-right strip zero has a nonempty actual unit stationary sector. Its previous displacement/mean/positive-ceiling lower bound transfers to the incoming head after subtracting `Q(s,1)*P(s,K)`.

No sign or sufficiently small bound for the incoming aggregate is established here. Nor is the explicit outgoing error asserted to be smaller than the complete opposing budget at every parameter. The full RH comparison remains open.

## Formal scope

`formal/GaloisForLFunctions/RHTower/ArithmeticStationaryReflectedTail.lean`, namespace `RHTower.DeletionMixedRefinement`: 453 lines, 30 declarations (24 theorems and six definitions).

- `stationaryOutgoingAtom_eq_reflected_term`: exact factorization of each literal outgoing tail.
- `sum_stationaryOutgoingAtom_eq_reflected_sum`, `norm_sum_stationaryOutgoingAtom_eq`: full complex cancellation and its exact norm identity, for every positive finite frequency set.
- `stationaryComplexBudget_eq_incoming_add_reflected`: the complete stationary sum retains every finite incoming head and the reflected arithmetic partial sum.
- `rawPrefix_reflected_eq_at_zero`, `stationaryComplexBudget_eq_incoming_reflected_at_zero`: only the reflected zeta value disappears; pole, half endpoint, and remainder remain.
- `norm_integral_logarithmicFourierMode_at_saddle_le`, `norm_stationaryReflectedTailFactor_le`: explicit square-root height saving for the actual common kernel.
- `normalizedWeightedRemainder_scaled_im_le_incoming_reflected`: full source inequality with both infinite sectors and the mean retained.
- `norm_rawPrefix_reflected_le_at_zero`, `norm_negativeFourierSection_sub_incoming_le_at_zero`: an explicit parameter-only outgoing-sector ceiling at every strip zero, with `t>=1`, `K>=1`, and the actual stationary cutoff condition.
- `stationaryIncomingSection_im_lowerBound_at_closed_right_zero`: the required zero budget transferred to the literal incoming aggregate, with the complete outgoing error subtracted.

The last conclusion includes critical zeros. The incoming sign/magnitude comparison needed to exclude off-line zeros is unproved; no sufficiently small outgoing error relative to the full opposing budget is asserted. RH remains unproved and unfalsified. No novelty claim is made.

## Verification gates

- [x] Whole-corpus searches and inspection of dilation, saddle geometry, reflected block estimates, and literal power-sum remainder.
- [x] Complete symbolic paper proof of the factorization and retained-boundary identity.
- [x] Foreground scratch passes without warnings.
- [x] Leaf wired once in `RHTower.lean`; final targeted build compiled exactly one leaf in 4.5 seconds. No umbrella build.
- [x] All 30 new declarations audited; only standard Lean axioms. No prior declaration re-audited.
- [x] Current frontier, universal ledger, and corpus index updated.
- [ ] Global formal lint reports one unrelated unwired module, recorded below.
- [ ] Complete the independent remaining-head comparison and unconditional RH proof/falsification.

## Verification and cleanup

`LEAN_NUM_THREADS=1 lake env lean /tmp/edq_reflected_tail.lean` passed without warnings. The final command `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticStationaryReflectedTail` compiled exactly one leaf in 4.5 seconds. All other build output was cached replay; no dependency or umbrella rebuild was performed.

A separate `/tmp` scratch audited exactly the 30 new declarations. Every dependency list contains only `propext`, `Classical.choice`, and `Quot.sound`. Global `python3 scripts/formal_tools.py lint` reports one unrelated concurrent wiring error: `GaloisForLFunctions.RHTower.ThetaCuspAllOrderLikelihoodCooling`. No lint error concerns this leaf; the unrelated module was not modified, built, or re-audited. Unchanged lint was not repeated.

The corpus index was refreshed once: 32744 files, 399826 declarations, 3911 gap markers. All owned Lean/Lake handles completed, and process inspection found none remaining. Four scratch sources/manifests were removed. Logs remain at `/tmp/edq_reflected_tail_{build,axioms,lint,index}.log`. No numerical result, computational certificate, or added axiom is used.
