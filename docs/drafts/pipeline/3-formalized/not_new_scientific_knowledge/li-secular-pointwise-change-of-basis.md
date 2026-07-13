# Li/secular pointwise change of basis

- **ID:** li-secular-pointwise-change-of-basis
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean certificate split from `../2-fully-proven/lean-claim-review-row-010-pk-li-secular-change-of-basis.md`)
- **Owner:** Leaner
- **Lean file:** `formal/GaloisForLFunctions/RHTower/SecularMoments.lean`

## Statement

For any commutative ring `R`, element `x : R`, and natural numbers `n` and `k > 0`, the Li summand
`1 - (1 - x)^n` and the secular monomial `x^k` are related by the two triangular integer binomial transforms:

```lean
theorem li_secular_pointwise (R : Type*) [CommRing R] (x : R) (n : ℕ) :
    1 - (1 - x) ^ n
      = ∑ j ∈ Finset.range n, (n.choose (j + 1) : R) * (-1) ^ j * x ^ (j + 1)

theorem secular_li_pointwise_inv (R : Type*) [CommRing R] (x : R) (k : ℕ) (hk : 0 < k) :
    x ^ k = ∑ m ∈ Finset.range k, (-1) ^ m * (k.choose (m + 1) : R) *
      (1 - (1 - x) ^ (m + 1))
```

This is the pointwise algebra behind the Li coefficient / secular moment triangular change of basis, with
`x = 1 / rho` before summing over zeros. It does not formalize the analytic Voros closed form for `P_k`, the
infinite zero sums, Li positivity, RH, or DSS.

## Paper Proof

For the forward identity, expand `(1 - x)^n` by the binomial theorem:

> `(1 - x)^n = sum_{i=0}^n binom(n,i) (-1)^i x^i`.

Subtracting from `1` cancels the `i=0` term and leaves

> `1 - (1 - x)^n = sum_{i=1}^n binom(n,i) (-1)^{i+1} x^i`.

Reindexing `i = j + 1` gives the Lean statement.

For the inverse identity, apply the binomial theorem to `x = 1 - (1 - x)` and use the finite alternating
binomial identity `sum_{i=0}^k (-1)^i binom(k,i)=0` for `k > 0`. Separating the constant term and reindexing
the nonzero powers yields

> `x^k = sum_{n=1}^k (-1)^{n+1} binom(k,n) (1 - (1 - x)^n)`,

which is the Lean statement with `n = m + 1`.

## Gates

- [x] 0 -> 1 in-progress: pointwise Li/secular binomial identities isolated from row #10 §B.
- [x] 1 -> 2 fully-proven: paper proof above by the binomial theorem and alternating binomial sum.
- [x] 2 -> 3 formalized: Lean theorems `li_secular_pointwise` and `secular_li_pointwise_inv` in
  `formal/GaloisForLFunctions/RHTower/SecularMoments.lean`; scratch `#check` and `#print axioms` passed; both are
  audited in `scripts/check_axioms.sh`.
- [ ] 3 -> 4 publication-ready: include as the finite algebra certificate for the Li/secular coordinate change.

## Log

- 2026-06-19 — Leaner split the exact §B triangular integer change-of-basis from row #10. The parent
  claim-review ticket remains in `2-fully-proven` because its §A analytic Voros closed form is not Lean-backed.
