# Every finite Weil family has an explicit index horizon test

- **ID:** every-finite-weil-family-has-an-explicit-index-horizon-test
- **Stage:** 3-formalized
- **Statement:** For every finite smooth compact real Weil family, its negative
  eigenvectors and spectral gap determine finite inequalities ensuring that the
  actual Euler–Maclaurin atomic synthesis retains its entire negative index.

## Proof

Let `A` be the family's full Weil Gram matrix, `r` its negative index,
and `S` its negative eigenvectors. Then `S*AS=diag(c)` with every `cᵢ≤−δ`
for some `δ>0`. At rank zero the assertion is automatic.

At horizon `N blockSize(R)`, width `1/k` and quadrature order `m`, the proved
synthesis gives common sup error `e=emErr(M,φ,m,k,N)` and Lipschitz error
`L=emLip(M,φ,k,N)`, supported in radius `R+1`. Two-sided full Weil motion
and polarization give each Gram error the literal budget `Bᵢⱼ` defined by
`weilGramEntryBudget`. The common source translation leaves the Gram matrix
unchanged.

Compression bounds its `(i,j)` error by
`Σₐᵦ |Sₐᵢ| Bₐᵦ |Sᵦⱼ|`. If every such quantity is at most
`δ/(2(r²+1))`, its quadratic error is strictly less than `δ‖x‖∞²`.
The negative diagonal has margin `δ‖x‖∞²`, so all `r` directions survive.
The synthesized Gram is a compression of the actual atomic matrix; therefore
the latter has negative index at least `r`.

All approximation bounds come from the actual smooth profiles and source
derivatives. The test applies at each finite horizon; it asserts no bound on
the size of an unknown negative witness solely from its dimension.

## Lean

`EffectiveArithmeticHodgeTheory/FiniteWeilFamiliesHaveExplicitIndexHorizonTests.lean`:
`le_index_of_compressed_entry_test`, `exists_complete_negative_compression`,
`exists_emWeil_index_horizon_test`, and `exists_emWeil_index_horizon_certificate`.
Direct `lake --old env lean` check passed. All four transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella wired.
