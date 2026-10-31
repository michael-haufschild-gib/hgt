# Autocorrelation smoothing preserves the divisor-jet square completion

- **ID:** SSH-AUTOCORRELATION-DIVISOR-JET
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q1/O1, additive smoothing of the finite conductor coupling.

## Statement

For a finite real sequence `a`, define its compressed autocorrelation weight

`b_k=(1/φ(k))Σ_(i,j) a_i a_j c_k(|i−j|)`.

Complete-period Ramanujan correlation identifies this with
`(1/(kφ(k)))Σ_(t<k)(Σ_i a_i c_k(t+i))²`, hence `b_k≥0`.
For `M≥1`, `F_b(n)=Σ_(k|M)b_k f_k c_k(n)` and
`JF(n)=Σ_(m|M)f_m J_m(n)`, the exact identity is

`Σ_(m|M)Σ_(k|m)Λ(m/k)φ(k)b_k(f_m−f_k)²`
`=Σ_(m|M)[φ(m)b_m(log M+log m)+Σ_(k|m)Λ(m/k)φ(k)b_k]f_m²`
` −(2/M)Σ_(n<M)F_b(n)JF(n)`.

Equivalently the last pairing is `Σ_(n<M)(T_a F)(n)(T_a JF)(n)`,
where `(T_a H)(n)=Σ_i a_i H(n+i)`: both physical packets carry the
literal finite source smoothing.

The incoming charge also equals
`Σ_(i,j)a_i a_j c_m(|i−j|)[tameDifferent(m)−λ_(m/gcd(m,|i−j|))]`,
where `λ_d=log d+tameDifferent(d)`.

## Proof

Primitive Fourier expansion gives
`Σ_(i,j)a_i a_j c_k(|i−j|)=Σ_(ζ primitive k)|Σ_i a_iζ^i|²`.
Shifted orthogonality gives `Σ_(n<M)c_k(n+i)c_l(n+j)=δ_kl M c_k(|i−j|)`.
Expanding both smoothed packets therefore gives the weighted period pairing.

Expand each edge square. Dirichlet associativity and `Σ_(r|M/k)Λ(r)=log(M/k)`
give its outgoing diagonal charge. The expansion
`J_m=log(m)c_m+Σ_(k|m)Λ(m/k)c_k` gives the cross pairing.
Finally `J_m(h)=c_m(h)(λ_m−λ_(m/gcd(m,h)))` identifies the incoming charge.
All edge weights are nonnegative, proving both energy and lag-kernel positivity.

## Lean status

`SuccessorShellArithmetic/Conductor/RamanujanAutocorrelationWeights.lean`:
primitive Fourier squares, nonnegative source weights, shifted orthogonality,
period square masses and the smoothed conductor Gram.

`SuccessorShellArithmetic/Conductor/SmoothedDivisorJet.lean`:
`weightedDivisorJetEnergy_eq_source_pairing`,
`weightedDivisorJetEnergy_autocorrelation_nonneg`,
`sum_divisor_autocorrelationWeight_eq_adjunction_charge`, and
`sum_adjunction_lag_charge_nonneg`.

Both direct leaf audits passed. All thirteen capstone axiom checks contain
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports are wired.

## Boundary

This is a finite periodic identity. Identification with the variable-width,
finite-horizon Weil kernel and payment of its boundary terms remain open.

