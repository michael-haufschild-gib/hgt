# The divisor jet reads an exact adjunction-energy gap

- **ID:** SSH-RAMANUJAN-DIVISOR-JET-ADJUNCTION-GAP
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Q1/O1, finite divisor-graph diagonalization.

## Statement

For `m≥1`, `n≥0`, put `q=m/gcd(m,n)` and
`λ(d)=log d+tameDifferent(d)`. The identity is

`J_m(n)=c_m(n)[λ(m)−λ(q)]`.

## Paper proof

Let `C_s(m,n)=Σ_(d|m,d|n)μ(m/d)d^s` and `Φ_s(m)=C_s(m,0)`.
With `g=gcd(m,n)`, Möbius reindexing gives

`C_s(m,n)=μ(q)g^s∏_(p|g,p∤q)(1−p^(−s))`.

The finite Euler product for `Φ_s` then gives the cross-multiplied identity
`C_s(m,n)Φ_s(q)=μ(q)Φ_s(m)` for every real `s`.
At `s=1`, `C_1=c`, `C'_1=J`, `Φ_1=φ`, and `Φ'_1=φλ`.
Differentiate the finite identity and cancel the positive `φ(q)`.

The corpus already contains real-power Jordan totients, the ordinary
Möbius/totient quotient, and the conductor-multiple jet value. The new
identity is the exact jet value at every lag, needed for finite divisor
reciprocity. It does not supply the full Weil agreement-shell identity.

- [x] Existing Jordan, quotient and conductor-multiple identities located.
- [x] Generalized finite quotient and differentiation formalized.
- [x] Direct Lean check, axiom audit and umbrella import.

## Lean

`SuccessorShellArithmetic/Conductor/RamanujanJetAdjunctionGap.lean`:
`ramanujanPowerDivisor_eq_product`, `ramanujanPowerDivisor_mul_quotient`,
`hasDerivAt_ramanujanPowerDivisor_one`,
`ramanujanLogDivisorJet_eq_adjunction_gap`.
Final direct check passed without diagnostics. Every audited endpoint
depends only on `propext`, `Classical.choice`, `Quot.sound`.
