# Positive tail annihilation and scale-local prime sampling

- **ID:** B130-PTA
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B130; scale locality B139.

## Conjecture

For the zeta spline trace, a uniform lower bound on all primes in windows
`[exp(T_k-L_k), exp(T_k+L_k)]`, where `T_k→∞` and
`L_k≥c√T_k` for a fixed `c>0`, implies RH. No attained-top premise.

Stronger target: replace `√T_k` by a multiple of `(log T_k)²`, using
the Riemann–von Mangoldt count. Arbitrarily slowly growing `L_k` remains open.

Continuous depth target: for `α≥0` and `r>0`, lower bounds
`f(u)≥-K exp(αu)` on arbitrarily late windows `|u-T|≤r√T`
force every zeta zero to satisfy `Re ρ≤1/2+α`.

## Mechanism to prove

For a quartet exponent `a+iγ`, put `h=π/|γ|` and

`Q_(a,h)(w) = (cosh(hw)+cosh(ha))/(1+cosh(ha))`.

This is the Laplace transform of a symmetric probability measure on
`{-h,0,h}`. It annihilates `±a±iγ`. For real `s`,
`Q_(a,h)(s) ≤ exp(s²h²/2)`. Products therefore have a Gaussian moment
bound governed by `Σh²`, independently of the number of deleted zeros.
High-ordinate factors preserve every fixed low exponent, and differ from
one by `O(h²)` there. Square summability gives a nonzero limiting multiplier
at a specified exponent, exact deletion of the tail, and arbitrarily small
remaining square cost. This infinite passage is formalized for absolutely
convergent exponential traces in a strip.

Positive averaging transfers a local lower bound to the filtered trace.
The contribution of shifts outside radius `L` is bounded by
`C exp(T/2-cL²)` using the unconditional trace envelope. The retained
finite head has a positive-depth oscillation with bounded gaps. This
would exclude long windows with no negative excursion without requiring
the original configuration to attain its top.

Precisely, for shifted strip width `D=1/2+α`, put
`V₀=r²/(16(D+1))` and choose tail cost `V≤V₀`. With coefficient mass
`A=Σ|c_j|` and finite-head gap `B`, the interior half-window leakage
is at most `2A exp(DB+D²V₀-T)`. Pointwise convergence of the
positive averages suffices because this bound is uniform over prefixes.

For prime sampling, first propagate the bound using the corpus's
`x^(2/3)` prime gaps and the global derivative envelope. The resulting
error exponent is `1/6`.
Tail deletion should then exclude zeros deeper than that exponent;
the improved derivative envelope makes a second passage bounded.

## Gates

- [x] Existing finite positive annihilators, finite-head oscillation, and
  reciprocal-square summability located in the corpus.
- [x] Finite symmetric filter, exact zeros, uniform moment bound, and local
  Gaussian leakage: `ScaleLocality/PositiveTailFilters.lean`.
- [x] Nonzero product convergence at a retained exponent when every
  shift satisfies `|h| |w|≤1`; same module, direct Lean/axiom audit passed.
- [x] Nonzero multiplier convergence, exact tail deletion, dominated trace
  passage, and arbitrarily small tail cost: `PositiveTailIsolation.lean`.
- [x] Gaussian local lower bound survives infinite deletion; same module.
- [x] Cost `r²/(16(D+1))` gives `O(exp(-T))` leakage at square-root
  windows: `SquareRootWindowLeakage.lean`; Lean/axiom audit passed.
- [ ] Actual zeta tail isolation: `ZetaTailIsolation.lean`.
- [x] Finite-spectrum growing sign changes: `FiniteSpectrumOscillation.lean`;
  Lean/axiom audit passed, using the existing uniform sign theorem.
- [ ] Continuous depth criterion: `SquareRootWindowsDetectEveryDepth.lean`.
- [ ] Two-step prime-window criterion: `PrimeSquareRootWindows.lean`;
  audit all dependencies and final source.

## Scope

No bound on the actual prime trace is asserted. This is a sampling
mechanism, not an arithmetic producer for B130. No external novelty
claim; web search excluded by user.
