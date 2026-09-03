# Prime--Hodge history integral--nuclear defect

- **ID:** `ULF-PHIN-001`
- **Stage:** 3-formalized
- **Paper:**
  `../2-fully-proven/universal-law-field/restricted-grassmannian-formation-geometry/prime-hodge-history-integral-nuclear-defect.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeHodgeHistoryIntegralNuclearDefect.lean`
- **Status:** unconditional pre-divisor object construction; RH selection transport remains open.

## Certified object

Lean constructs one operator `primeHodgeHistoryIntegralNuclearDefectT` on
`ell2(Nat x Nat.Primes)`. Its kernel is

```text
1_(n=k) w_n K_1(p,q),
w_n = 630/((2n+3)(2n+5)(2n+7)(2n+9)),
```

where `K_1` is the normalized literal Stokes cofinal prime kernel. No zero, divisor, ordinate, or
RH hypothesis occurs in its definition.

`primeHodgeHistoryIntegralNuclearDefect_closed` proves simultaneously, without hypotheses:

- positivity and Schatten-one nuclearity;
- operator trace and trace norm equal `1`;
- every same-history `(p,q)` matrix entry is nonzero;
- total history flux is `1`;
- every shifted history marginal is exactly
  `m_n = 105/((2n+3)(2n+5)(2n+7))`.

Finite principal blocks are proved positive before the infinite operator is formed. Thus prime
mixing survives literally; it is not removed by diagonalization or inferred from a symbolic
tensor product.

## Exact boundary

Not proved: anomaly-subtracted theta/Poisson completion is a positive unital, trace-preserving,
grade-flux-preserving map carrying this pre-divisor source defect to the divisor relation-horizon
defect. Also not in this module: the analytic all-order identification of `m_n` with the wall
commutator energy from `ULF-DHNJ-001`. Completion transport remains the source-to-selection edge
required for the RH contradiction.
