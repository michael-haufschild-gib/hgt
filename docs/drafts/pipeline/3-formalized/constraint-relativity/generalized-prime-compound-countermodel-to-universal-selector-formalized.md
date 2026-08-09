# Generalized-prime compound countermodel to universal selector — formalized

- **ID:** `generalized-prime-compound-countermodel-to-universal-selector-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `generalized-prime-compound-countermodel-to-universal-selector.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.GeneralizedPrimeCountermodel` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/GeneralizedPrimeCountermodel.lean` |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.QuadraticLawHorizon` | supplies card items 6–8 (the quadratic observer factor) |

Both wired into `GaloisForLFunctions.HTGeometry`.

## Trap recorded

In this mathlib `AddMonoidAlgebra R M` is a **structure** with field `coeff : M →₀ R`, not a
type synonym for `M →₀ R`.  `Finsupp.single`, `Finsupp.lsum` and `Finsupp.lapply` therefore do not
typecheck against it.  The group-algebra layer is built through the explicit coefficient
equivalence `coeffLinearEquiv : PrimeAlgebra ι ≃ₗ[ℂ] (PrimeGrades ι →₀ ℂ)` together with
`AddMonoidAlgebra.single` and `AddMonoidAlgebra.single_mul_single`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

The group algebra, card `(1)`–`(5)`:

1. `PrimeGrades ι = ι →₀ ℤ`, `PrimeAlgebra ι = AddMonoidAlgebra ℂ (PrimeGrades ι)` — **card `(1)`**,
   the free abelian grade group and its complex group algebra, at an arbitrary index set.
2. `coeffLinearEquiv`, `coeffLinearEquiv_single` — the coefficient equivalence.
3. `gradeNorm`, `gradeNorm_zero`, `gradeNorm_pos`, `gradeNorm_add` — **card `(2)`**, the
   generalized-prime norm `|g| = ∏ P_i^{g_i}` and its multiplicativity in the grade.
4. `radialChar`, `radialChar_single`, `radialChar_mul_single` — **card `(2)`**, the radial character
   `Γ_c(U_g) = |g|^c U_g`, multiplicative on the monomial basis, i.e. an algebra automorphism.
5. `primeDagger`, `primeDagger_single`, `primeDagger_primeDagger_single`, `primeDagger_mul_single` —
   **card `(2)`**, `U_g^† = U_{−g}`: conjugate-linear, involutive, grade-reversing.
6. `valuationDeriv`, `valuationDeriv_single` — **card `(3)`**, `∂_j(U_g) = v_j(g) U_g`.
7. `valuationDeriv_single_mul` — **card `(3)`**, the Leibniz rule: `∂_j` is a derivation, from
   additivity of valuations.
8. `gradeTrace`, `gradeTrace_single` — **card `(3)`**, the identity-coefficient trace `τ`.
9. `primeAtom_grade` — **card `(4)`**, the prime/inverse-prime atom has total grade `0`.
10. `gradeTrace_primeAtom` — **card `(5)`, first identity**: `τ(u_i) = 1`.
11. `valuationPairing_primeAtom` — **card `(5)`, second identity**: `φ_j(u_i) = −δ_{ij}`.
12. `gradeNorm_primeAtom`, `radialChar_primeAtom` — **card `(5)`, third identity**:
    `Γ_c^{⊗2} u_i = u_i`, since `|e_i|^c · |−e_i|^c = 1` for every real drift `c`.

The reciprocal two-leg system, card `(6)`–`(8a)`:

13. `stokesForm`, `legTransport` — **card `(6)`**, `J` and `T_{i,c} = diag(P^c, P^{−c})`.
14. `legTransport_stokes` — **card `(7)`**: `T^{*} J T = J` for every real `c`, so the indefinite
    Stokes form is preserved at every drift.
15. `radialDefect_ne_zero` — **card `(8)`**: `1 − P^{2c} ≠ 0` whenever `P > 1` and `c ≠ 0`.
16. `scalarPortDefect`, `scalarPortDefect_ne_zero` — **card `(8a)`**: the contracted scalar-port
    defect `R_c` is a nonzero functional on the prime span, hence of rank one.
17. `coframeDefect`, `coframeDefect_injective` — the hostile-audit item 4: the *uncontracted*
    vector coframe defect `u_i ↦ (1 − P_i^{2c}) e_i` is diagonal and injective, not rank one.

The quadratic observer factor, card `(9)` and theorem items 6–8, is `QuadraticLawHorizon`:
`lawObserver`/`fibre_split` (punctured quadratic descent), `tor_one_eq_top` and
`hiddenDecoder_recovers` (Tor/Bockstein recovery at the collision), and `conditioning_law` with
`decoder_norm_tendsto_atTop` (the inverse-square-root discriminant conditioning).

## Independence conclusion, formally

Items 1–17 hold **for every real `c`**, with `c` a free parameter of the construction, while item 15
shows the radial defect is nonzero for every `c ≠ 0`.  Hence the conjunction of the eight listed
organ identities is consistent with nonzero drift, and no theorem using only that conjunction can
force `c = 0`.  This is a countermodel statement about the generalized-prime system, not about the
rational adeles; the card's hostile-audit boundary is unchanged.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/GeneralizedPrimeCountermodel.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.GeneralizedPrimeCountermodel          # green
```
