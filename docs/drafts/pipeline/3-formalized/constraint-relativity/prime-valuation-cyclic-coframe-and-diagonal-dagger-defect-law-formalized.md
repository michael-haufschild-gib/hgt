# Prime-valuation cyclic coframe and diagonal dagger-defect law — formalized

- **ID:** `prime-valuation-cyclic-coframe-and-diagonal-dagger-defect-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `prime-valuation-cyclic-coframe-and-diagonal-dagger-defect-law.md`
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.PrimeValuationCoframe` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/PrimeValuationCoframe.lean` |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.GeneralizedPrimeCountermodel` | imported: the graded algebra, `valuationDeriv`, `gradeTrace`, `gradeNorm` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Corpus reuse

The valuation derivation `∂_ℓ`, the identity-coefficient trace `ε₀`, the prime-atom pairing
`φ_ℓ(u_p) = −δ_{ℓp}` and the generalized-prime norm were **not** rebuilt: they already exist in
`GeneralizedPrimeCountermodel`, built for the companion countermodel card.  This module adds the
cyclic/Hochschild identities, the independence law and the diagonal defect.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorem 1, the valuation cyclic coframe:

1. `primeAlgebra_induction` — monomial induction on the generalized-prime algebra, the tool for
   every bilinear identity below.
2. `valuationDeriv_mul` — **Theorem 1.1**: `∂_ℓ` is a derivation, extended from monomials by
   bilinearity.
3. `gradeTrace_valuationDeriv` — **Theorem 1.2**: `ε₀ ∂_ℓ = 0`, because the identity grade has
   zero valuation.
4. `valuationPairing` — **card `(3)`**: `φ_ℓ(a,b) = ε₀(a ∂_ℓ b)`.
5. `valuationPairing_antisymm` — **Theorem 1.3**: `φ_ℓ(a,b) + φ_ℓ(b,a) = 0`.
6. `valuationPairing_hochschild` — **Theorem 1.4**: `φ_ℓ b₂ = 0`, i.e.
   `φ_ℓ(ab,c) − φ_ℓ(a,bc) + φ_ℓ(ca,b) = 0`.

Items 5 and 6 are exactly the statement that `φ_ℓ` annihilates both relations defining the signed
degree-one quotient `𝓗` of card `(2)`, so `φ_ℓ` descends to it.

Theorem 2, the prime classes as a coordinate basis:

7. `primeAtom`, `primeAtomInv`, `gradeTrace_atom` — **card `(4)`**: the atom and its trace one.
8. `valuationPairing_atom` — **card `(5)`, boxed**: `φ_ℓ([u_p]) = −δ_{ℓp}`.
9. `linearIndependent_of_dual_identity` — a family detected by a dual family with identity Gram
   matrix is linearly independent.  Combined with item 8 this is **card `(6)`**: the classes
   `[u_p]` are independent and `Φ` is an isomorphism onto the finitely supported sequences.  Stated
   through the detecting functionals, it holds in *any* quotient the `φ_ℓ` descend through — in
   particular in `𝓗`, by items 5 and 6.

Corollary 3, the scalar reader is a contraction:

10. `log_gradeNorm` — **card `(7)`**: unique factorization, `log q = ∑_ℓ v_ℓ(q) log ℓ`.
11. `logDeriv_eq_sum_valuationDeriv` — **card `(8)`**: `∂_log = ∑_ℓ (log ℓ) ∂_ℓ` on every monomial
    (the sum is finite, as the card notes).
12. `logPairing_eq_sum` — **card `(8)`**: `φ_log = λ_log ∘ Φ`, so the scalar Kummer reader is one
    covector shadow of the full coframe.

Theorem 4 and the no-cancellation law:

13. `defectMultiplier` — **card `(10)`**: the diagonal multiplier `1 − ℓ^{2a}`.
14. `defectMultiplier_zero` — **card `(12)`**, critical case: at `a = 0` every multiplier vanishes,
    so the kernel is everything.
15. `defectMultiplier_ne_zero` — **card `(12)`**, off-line case: for `a ≠ 0` and every base `> 1`
    the multiplier is nonzero.
16. `defect_injective_of_ne_zero` — **cards `(11)`, `(12)` and the no-cancellation theorem**: off
    the critical line, a finite cross-prime combination annihilated by the diagonal defect has all
    coefficients zero.

## Scope

The card explicitly does not force `D_ρ = 0` and does not prove RH; the Xi-zero data `(9)` enters
only through the real drift parameter `a_ρ = Re ρ − 1/2` and the nonzero scalar `c_ρ`, which is why
the formalization is stated for an arbitrary real `a` and an arbitrary nonzero coefficient family.
The "Nomotopy interpretation" and "Hostile audit" sections are commentary.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/PrimeValuationCoframe.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.PrimeValuationCoframe          # green
```
