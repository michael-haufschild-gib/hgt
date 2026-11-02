# Large prime spikes have a logarithmic defect gap

- **Stage:** 2-fully-proven; Lean check pending.
- **Type:** THEOREM (paper).
- **Wall:** Σ1e.
- **Statement:** For every finite family of primes `p>sqrt N`, `N≥2`, the pole-centered incidence packet has prime defect at least `(log N)/2` times its harmonic squared norm.

Put `A(n)=Σ_p b_p 1_(p|n)`, `H=H_N`, `T=Σ_(n≤N) A(n)/n`, and
`F(n)=A(n)−T/H`. The exact identities are

`D_N(F/sqrt n)=Σ_p (log p/p)H_floor(N/p)b_p²`,

`Σ_(n≤N) F(n)²/n=Σ_p H_floor(N/p)b_p²/p−T²/H`.

The first is the general prime-incidence harmonic diagonal: subtracting a
constant leaves every jump unchanged. The second follows by expanding the
weighted variance. Distinct prime supports are disjoint because `pq>N`.
Since `log p≥(log N)/2` and `T²/H≥0`, the claimed gap follows.
No upper cutoff on the selected primes is needed; primes above `N` have zero
incidence throughout the horizon.

For normalized Ramanujan coefficients `a_p`, take
`b_p=p a_p/sqrt(p−1)` and divide amplitudes by `sqrt(log N)`.
Write `d_p=[p/(p−1)]H_floor(N/p)` and
`t_p=H_floor(N/p)/sqrt(p−1)`. The centered Gram is

`[diag(d_p)−t tᵀ/H_N]/log N`,

and the defect matrix is `diag(d_p log p)/log N`.
Thus pole centering reduces the norm without changing the diagonal defect.

## Lean

`CompletedArithmeticForms/LargePrimeIncidencePacketsHaveALogarithmicDefectGap.lean`:
`centered_largePrime_incidence_mass_eq`, `largePrime_incidence_defect_gap`.
Source check and transitive axiom audits are pending.

The general diagonal is already checked in
`PrimeIncidenceDefectsHaveAnExactHarmonicDiagonal.lean`:
`jumpEnergy_prime_incidence_eq_harmonic_diagonal`.
The corpus's earlier conductor-gap estimates require a below-square-root
frame; this finite gap uses disjoint divisibility supports directly.

## Unproved extension

For primes at most `N`, the diagonal-minus-rank-one Gram suggests interlacing
of the centered defect eigenvalues with the ordered values `log p`.
This remains a separate conjecture, not part of the proved gap.
