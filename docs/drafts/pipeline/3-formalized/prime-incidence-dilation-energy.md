# Exact finite-horizon dilation energy of prime-incidence packets

- **ID:** Q6-DILATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0311/fable.md`, §7
- **Lean:** `ArithmeticCouplingTheory/ReceivingCharges/PrimeIncidenceDilationEnergy.lean`

For a finite set of primes `P`, real coefficients `b_p`, and every horizon `N`, let
`F_b(n)=Σ_(p∈P)b_p(1_(p|n)−1/p)` and `H_M=Σ_(1≤n≤M)1/n`. Then

`J_N(F_b)=Σ_(p∈P)b_p²(log p/p)H_(⌊N/p⌋)`.

Constant subtraction preserves `J_N`. More generally, the integer divisibility comb `1_(d|n)` has energy `(log d/d)H_(⌊N/d⌋)` for every `d≥1`.

Proof. A Mangoldt-supported dilation changes only one prime incidence coordinate. Its squared jump therefore equals the jump with coefficients `b_p²`. For a single divisibility indicator, the binary increment equals its square. Grouping dilation pairs by their target gives `Σ_(d|n≤N)log n/n`; grouping by their source gives `Σ_(d|n≤N)ψ₁(⌊N/n⌋)/n`. After `n=dr`, the cofactor terms cancel by `Σ_(r≤M)ψ₁(⌊M/r⌋)/r=Σ_(r≤M)log r/r`. The remaining term is `(log d/d)H_(⌊N/d⌋)`.

Declarations: `jumpEnergy_sub_const`, `jumpEnergy_divisibilityIndicator`, `vonMangoldt_incidence_jump_square`, `jumpEnergy_incidencePacket_diagonal`.

The prime-packet identity is equivalent to
`CompletedArithmeticForms.jumpEnergy_prime_incidence_eq_harmonic_diagonal`;
the integer-comb statement also allows composite `d`.

Individual `lake --old env lean` check passed; transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. Imported by the `ArithmeticCouplingTheory` umbrella.

The identity evaluates the dilation term only. Joint cancellation with the shell, Gamma and pole terms in Q6 remains open.
