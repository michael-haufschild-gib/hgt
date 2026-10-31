# The divisor jet has a finite ground-state square completion

- **ID:** SSH-DIVISOR-JET-GROUND-STATE-SQUARES
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Q1/O1, signed conductor coupling of the downward divisor source.

## Statement

For `M≥1`, put

`E_M(f)=Σ_(m|M)Σ_(k|m)Λ(m/k)φ(k)(f(m)−f(k))²`.

The exact identity is

`E_M(f)=Σ_(m|M)φ(m)[log(M/m)+tameDifferent(m)]f(m)²`
`        −2Σ_(m|M)Σ_(k|m)Λ(m/k)φ(k)f(m)f(k)`.

Thus this completed conductor form is nonnegative. It vanishes exactly
when `f` is constant on the divisors of `M`.

Writing `F(n)=Σ_(m|M)f(m)c_m(n)` and
`JF(n)=Σ_(m|M)f(m)J_m(n)`, conductor orthogonality identifies the
same form with

`Σ_(m|M)φ(m)[log M+log m+tameDifferent(m)]f(m)²`
`  −(2/M)Σ_(n<M)F(n)JF(n)`.

## Paper proof

Expand every edge square. Incoming mass is
`Σ_(k|m)Λ(m/k)φ(k)=φ(m)tameDifferent(m)`.
For fixed `k|M`, outgoing mass is
`φ(k)Σ_(d|M/k)Λ(d)=φ(k)log(M/k)`.
These give the first identity. Every edge weight is nonnegative.
If the energy is zero, each prime edge from `m` to `m/p` has positive
weight. Induction on `m` connects every divisor to `1`, proving the
kernel statement. Conversely a constant profile kills every edge.

The conductor expansion of `J_m` and complete-period orthogonality give
the second identity. In the kernel, the packet itself is the divisibility
comb `F(n)=f(1)M·1_(M|n)`.

## Corpus boundary

Existing Haar prime-source and theta Doob energies already use positive
divisor-edge squares. The finite sieve already has adjunction-energy
eigenvectors. This identity identifies the exact totient-weighted
completion of the logarithmic divisor jet. It does not identify the
full agreement-shell block or control its finite-horizon remainder.

- [x] Exact conductor expansion and incoming totient convolution identified.
- [x] Existing divisor-square and finite-sieve constructions checked.
- [x] Square identity, kernel classification and packet bridge formalized.
- [x] Direct Lean checks, transitive axiom audit and umbrella import.

## Lean

`SuccessorShellArithmetic/Conductor/DivisorJetGroundState.lean`:
`divisorJetEnergy_eq`, `divisorJetEnergy_nonneg`,
`divisorJetEnergy_eq_zero_iff`, `divisorJetEnergy_eq_period_pairing`,
`divisorRamanujanPacket_eq_comb_of_energy_zero`.
Final direct check passed; every audited theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`.
