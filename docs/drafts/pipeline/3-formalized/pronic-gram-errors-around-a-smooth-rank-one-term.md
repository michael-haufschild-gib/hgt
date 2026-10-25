# Pronic Gram errors around a smooth rank-one term

- **ID:** pronic-gram-errors-around-a-smooth-rank-one-term
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** Smooth-power pronic energy has a bounded integral error, and a rank-one Gram approximation has an explicit three-pairing error bound.

For `0<ε<1/2`, let `β=1-2ε` and `h(n)=n^(1-ε)`. There is `D≥0`
such that, for every positive horizon,

`|‖h‖_T²-T^β/β|≤D`,

and `‖h‖_T≤sqrt(1+1/β) sqrt(T^β)`.
The bounded error comes from the checked complex power-sum estimate after
specializing to a real exponent. The norm majorant uses the finite reciprocal
power bound.

For arbitrary real coefficients `a,b` and real sequences `h,r,s`, the error
in the pronic pairing of `a h+r` and `b h+s`, after subtracting
`ab‖h‖_T²`, is at most

`|a|‖h‖_T‖s‖_T + |b|‖h‖_T‖r‖_T + ‖r‖_T‖s‖_T`.

The proof expands the three residual pairings and applies finite weighted
Cauchy–Schwarz. No summability or analytic estimate is assumed for these
arbitrary finite-horizon sequences.

## Lean audit

Module: [PronicGramErrorsAroundASmoothRankOneTerm.lean](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/PronicGramErrorsAroundASmoothRankOneTerm.lean).

- `exists_smooth_power_pronicEnergy_bounded_error`
- `pronicNorm_smooth_power_le`
- `abs_pronicGram_sub_rankOne_le`

Corrected scratch, producing, and final direct `lake --old env lean` checks
passed. All three transitive axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The BVI umbrella import is present;
the scratch file was removed. No limits were raised.

The complete uniform Vaughan matrix application is now checked; see
`uniform-vaughan-grams-follow-their-smooth-rank-one-term.md`. Further packet
and power-rate consequences remain under verification. This finite comparison
supplies no fixed zero-free strip; full Q-I remains open.
