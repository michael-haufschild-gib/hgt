# Relative Vaughan Grams and finite harmonic denominators

- **ID:** vaughan-relative-gram-and-harmonic-denominators
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** q-i-selective-square-root-band.md
- **Statement:** Test a universal rank-one limit after dividing the centered Gram by its actual nonzero harmonic amplitude, with a quantitative cutoff condition from finite rational denominators.

## Candidate and purpose

The uniform Gram paper gives, for `0<ε<1/2`, `β=1-2ε`, and every natural `q`,

`|Gᶜ_ij(T;U,V)/T^β-(c_ε²/β)H_U²H_V² s_i s_j|≤C_(ε,q)/(log T)^q`.

Positive cutoffs make `H_UH_V` nonzero. Dividing by its square may reveal a
nonzero second normalization even when `UV→∞` makes the usual normalized
Gram vanish. The division must be controlled quantitatively; nonvanishing
alone does not suffice.

Candidate arithmetic bound: for positive `N`,

`|H_N|≥1/N!`.

Each summand has denominator dividing `N!`, so `N! H_N` is an integer;
the checked nonvanishing theorem would make its absolute value at least one.
This would give

`|Gᶜ_ij/(T^β H_U²H_V²)-(c_ε²/β)s_i s_j|
 ≤C_(ε,q)(U!V!)²/(log T)^q`.

Thus any positive cutoff schedule with `(U!V!)²/(log T)^q→0` for some fixed
`q` would have the same nonzero relative Gram limit. This condition is a
statement about the chosen schedule, not an assumed analytic cancellation
estimate. Its applicability to explicit divergent schedules still needs proof.

## Audit and status

The corpus search for rational harmonic lower bounds found the exact
terminal-prime valuation and nonvanishing theorem in
`FiniteMobiusHarmonicSumsNeverVanish.lean`, read in full. It found no existing
factorial lower bound or relative moving Vaughan Gram law. No mathlib name
or new Lean theorem has yet been verified for the denominator step.

The uniform absolute Gram estimate is dependency-closed on paper but still
under Lean verification. The proposed relative law does not give a fixed
power saving at the square-root band and does not resolve Q-I.

## Dependency-closed paper proof

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

Three arithmetic targets are drafted in `/tmp/QIHarmonicDenominatorTools.lean`
(integerization, common-multiple lower bound, factorial specialization).
They remain uncompiled. The relative Gram targets are not yet drafted;
their corpus novelty audit is pending. This card remains at stage one
until that audit is complete.
