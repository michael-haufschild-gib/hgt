# Relative Vaughan Grams and finite harmonic denominators

- **ID:** vaughan-relative-gram-and-harmonic-denominators
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Verification:** All ten public targets passed final direct Lean checks and transitive axiom audits, with only standard axioms.
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** Dividing the centered Gram by its actual harmonic amplitude gives a universal rank-one limit whenever its explicit factorial error vanishes; every positive cutoff schedule admits divergent horizons realizing that limit.

## Exact statement and purpose

The uniform Gram paper gives, for `0<ε<1/2`, `β=1-2ε`, and every natural `q`,

`|Gᶜ_ij(T;U,V)/T^β-(c_ε²/β)H_U²H_V² s_i s_j|≤C_(ε,q)/(log T)^q`.

Positive cutoffs make `H_UH_V` nonzero. Dividing by its square may reveal a
nonzero second normalization even when `UV→∞` makes the usual normalized
Gram vanish. The division must be controlled quantitatively; nonvanishing
alone does not suffice.

For positive `N`,

`|H_N|≥1/N!`.

Each summand has denominator dividing `N!`, so `N! H_N` is an integer;
the checked nonvanishing theorem makes its absolute value at least one.
This gives

`|Gᶜ_ij/(T^β H_U²H_V²)-(c_ε²/β)s_i s_j|
 ≤C_(ε,q)(U!V!)²/(log T)^q`.

Thus any positive cutoff schedule with `(U!V!)²/(log T)^q→0` for some fixed
`q` has the same nonzero relative Gram limit. This condition is a
statement about the chosen schedule, not an assumed analytic cancellation
estimate. The horizon realization below applies to every positive cutoff schedule.

## Source audit

The corpus search for rational harmonic lower bounds found the exact
terminal-prime valuation and nonvanishing theorem in
`FiniteMobiusHarmonicSumsNeverVanish.lean`, read in full. It found no existing
factorial lower bound or relative moving Vaughan Gram law. The factorial
divisibility, positivity, and cast APIs passed dedicated Lean scratch checks.
All three arithmetic lower-bound targets passed corrected producing and final
direct checks, with only standard transitive axioms.

The uniform absolute Gram estimate has passed its direct Lean checks and
transitive axiom audits. The relative law does not give a fixed
power saving at the square-root band and does not resolve Q-I.

## Proof mechanism

For any positive common multiple `D` of `1,...,N`,

`D H_N = Σ_(d≤N) μ(d)(D/d) ∈ ℤ`.

The checked positive-cutoff nonvanishing theorem makes this integer nonzero.
Consequently `1≤D|H_N|`, hence `|H_N|≥1/D`. The source theorem
`Nat.dvd_factorial` supplies every required divisibility for `D=N!`.
No estimate on the real cancellation of the finite sum is assumed.

At positive `U,V`, multiplying the two factorial lower bounds and squaring
gives

`H_U²H_V² ≥ 1/(U!V!)² > 0`.

Divide the uniform absolute Gram error by this positive amplitude. Its
reciprocal is at most `(U!V!)²`, proving the stated relative error estimate.
For any chosen schedule satisfying the stated ratio limit, the squeeze
theorem gives the universal relative matrix `(c_ε²/β)ssᵀ`.

There is also an unconditional realization for **every** positive pair of
cutoff schedules `U(n),V(n)`: choose an integer `H(n)≥n+1` with

`log H(n) ≥ (n+1)(U(n)!V(n)!)²`.

Such an integer exists because `log T→∞`. The factorial ratio is then at
most `1/(n+1)`, and `H(n)→∞`. The order-one uniform Gram estimate proves
the same relative limit. In particular, taking `U(n)=V(n)=n+1` realizes
zero at the original normalization and a nonzero rank-one matrix at the
actual harmonic-amplitude normalization along the same horizons.

The conclusion concerns the selectable horizon scale. It imposes no
estimate at the square-root cutoff relation `H≈UV`.

## Lean verification

The arithmetic module is
[FiniteMobiusHarmonicSumsHaveExplicitLowerBounds](../../../../formal/GaloisForLFunctions/RHTower/FiniteMobiusHarmonicSumsHaveExplicitLowerBounds.lean),
in namespace `RHTower`. The relative Gram module is
[VaughanGramsAtTheirActualHarmonicAmplitude](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VaughanGramsAtTheirActualHarmonicAmplitude.lean),
in namespace `GaloisForLFunctions.BezoutValuationIncidence`.

| Checked declaration | Exact conclusion |
| --- | --- |
| `exists_int_mul_sum_moebius_div` | A common multiple clears every harmonic denominator. |
| `one_div_le_abs_sum_moebius_div_of_common_multiple` | `|H_N|≥1/D` at positive cutoffs and positive common multiples. |
| `one_div_factorial_le_abs_sum_moebius_div` | The explicit arithmetic bound `|H_N|≥1/N!`. |
| `one_div_factorial_le_abs_deningerHarmonicPartial` | The same factorial bound in the Vaughan harmonic notation. |
| `pmVaughanSmoothAmplitude_pos_and_inv_le_factorial` | Positive amplitude and reciprocal bound `(U!V!)²`. |
| `exists_uniform_pmPronicVaughanCentredGram_relative_log_rate` | Uniform relative Gram error with explicit factorial cost. |
| `tendsto_pmPronicVaughanCentredGram_relative_of_factorial_log_rate` | The relative limit whenever the stated schedule ratio vanishes. |
| `exists_horizon_pmVaughan_factorial_log_rate` | Divergent horizons paying the factorial cost for any two cutoff schedules. |
| `exists_horizon_pmPronicVaughanCentredGram_relative_limit` | Relative-limit realization for every positive cutoff schedule. |
| `exists_horizon_vaughan_zero_and_relative_rank_one_limits` | Zero ordinary limit and rank-one relative limit along the same horizons. |

Both leaves passed direct `lake --old env lean` checks from `formal/`.
All ten `#print axioms` reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. The arithmetic dependency also passed its producing check;
the terminal relative module required no olean. Both umbrella imports are
present and the owned proof scratches were removed.

The corpus audit found fixed-cutoff and moving Gram laws, but no matching
relative harmonic-amplitude law or factorial horizon calibration. No external
novelty claim is made. No fixed-strip width or full Q-I conclusion follows.
