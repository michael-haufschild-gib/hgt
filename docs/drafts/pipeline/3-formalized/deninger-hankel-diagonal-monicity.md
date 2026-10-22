# Integral diagonal monicity of finite maximal Hankel minors

- **ID:** `deninger-hankel-diagonal-monicity`
- **Stage:** 3-formalized
- **Type:** THEOREM / literature infrastructure
- **Route:** L — rational-Witt source foundation
- **Scientific status:** `[LITERATURE-ALIGNED] [FULLY FORMALIZED] [NOT AN RH PROOF]`
- **Sources:** Conca, *Straightening law and powers of determinantal ideals of Hankel
  matrices* (1998); Nam, *The determinantal ideals of extended Hankel matrices* (2010),
  Corollary 3.9.

## Statement

Fix a finite generic Hankel matrix over `ℤ`, consecutive rows `0,...,n-1`, and strictly
increasing selected columns `c`.  In the Leibniz expansion of its maximal minor, the identity
permutation contributes the diagonal exponent

```text
Σ_j e_(j+c_j).
```

Every nonidentity permutation contributes a strictly smaller exponent in lex order.  Since all
terms have total degree `n`, the same strict comparison holds in the degree-lex order used by
Nam.  The diagonal coefficient is exactly `1`; hence every canonical maximal minor is monic over
`ℤ` for both orders.

Repeated anti-diagonal indices in nonidentity terms are represented by their full multiplicity.
No genericity, field, domain, reducedness, or characteristic premise is hidden in the theorem.

## Proof mechanism

For a nonidentity permutation `σ`, take the first moved column `k`.  Every earlier column is
fixed.  Bijectivity forces `σ(j) ≥ k` for all `j ≥ k`; strict column growth then puts every such
permuted Hankel index strictly after the diagonal index `k+c_k`.  Thus all exponents agree before
that index, while the permuted exponent is `0` and the diagonal exponent is `1` there.

The determinant is then expanded symbolically.  Each Leibniz product is proved equal to the
monomial whose exponent is the sum of the relevant `Finsupp.single` values.  Support containment,
the exact diagonal coefficient, and the monomial-order degree definition yield monicity.

## Lean realization

- `RHTower/Deninger/DeningerHankelDiagonalMonicity.lean`
  - `hankelPermutationExponent_lt_diagonal`;
  - `hankelPermutationExponent_degLex_lt_diagonal`;
  - `finiteHankel_detTerm_eq_monomial`;
  - `finiteHankelMaximalMinor_coeff_diagonal`;
  - `finiteHankelMaximalMinor_monic`;
  - `finiteHankelMaximalMinor_degLex_monic`;
  - `finiteHankelMaximalMinorSet_degLex_monic`.

Direct foreground check and exact module build pass.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  Module is wired into `RHTower.lean`.

## Frontier impact

This closes integral monicity, one of two inputs required by the already-formalized
`IntegralMonicGroebnerTransfer`.  It does **not** assert that maximal Hankel minors form a
Gröbner basis and does not assert finite Hankel primeness.  Those Conca--Nam statements remain
the open hard input on the parent saturation card.

## Gates

- [x] 0 → 1: exact literature statement and relevant order isolated
- [x] 1 → 2: complete symbolic proof, including repeated-index terms
- [x] 2 → 3: unconditional Lean proof, targeted build, umbrella wiring, axiom audit
- [ ] 3 → 4: standalone publication not pursued

