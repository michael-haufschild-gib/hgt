# Hodge survival Fredholm colligation and index--flux law

- **ID:** `ULF-PHSF-001`
- **Stage:** 3-formalized core theorem
- **Paper:**
  `../2-fully-proven/universal-law-field/restricted-grassmannian-formation-geometry/hodge-survival-fredholm-colligation-index-flux-law.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/PrimeHodgeHistorySurvivalFredholmColligation.lean`
- **Status:** unconditional pre-divisor dynamics and conservation; completion intertwiner remains
  open.

## Certified mechanism

Exact tails `m_n` force survival ratio `r_n=m_(n+1)/m_n=(2n+3)/(2n+9)` and hazard
`h_n=1-r_n=6/(2n+9)`. Lean constructs the weighted shift
`C e_n=sqrt(r_n)e_(n+1)`, its positive exit defect `D2=I-C*C`, and bounded canonical left inverse
`B`, then proves

```text
B C = I,
(B-C*)C = D2,
sum_(j<N) E_j + R_N = I,
ind C = -1.
```

Here `E_j` has multiplier `w_(k+j)/m_k` and `R_N` has multiplier `m_(k+N)/m_k`; hence the finite
operator telescope records every exit without a hidden recurrent remainder.

The initial-state readout of `E_n` is exactly `w_n`. A separate theorem proves the full prime-fibre
marginal of the pre-divisor integral nuclear operator `T` at history `n` is the same `w_n`.
The capstone identifies, without hypotheses,

```text
-ind C = sum_n w_n = Tr Phi = Tr T = 1.
```

Thus `T` is a prime-mixed nuclear exit record of one forced Fredholm evolution, not a trace-one
operator attached after the fact.

`primeHodgeHistorySurvivalFredholmColligation_closed` bundles finite record completeness,
duality--adjunction fracture, index, timewise prime-fibre ownership, and total conservation in one
hypothesis-free theorem.

## Exact open edge

Not proved: literal integer/Poisson self-duality supplies a record-complete, anomaly-subtracted
theta completion intertwining `(C,D2,B,T)` and exhausting the completed relation horizon. That
theorem would forbid a rank-one strict-right residual horizon and close RH after reflection.

Not Lean-certified here: strong convergence of `C^N`, `||C^N||=1`, compactness of `C-S`, and the
square-root observability formulation. The formal capstone does not depend on them.
