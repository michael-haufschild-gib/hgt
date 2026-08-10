# Identity-sector radial-gauge blindness and cross-grade selection law — formalized

- **ID:** `identity-sector-radial-gauge-blindness-and-cross-grade-selection-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `identity-sector-radial-gauge-blindness-and-cross-grade-selection-law.md`
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.IdentitySectorRadialBlindness` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/IdentitySectorRadialBlindness.lean` |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.GeneralizedPrimeCountermodel` | imported: supplies the two-leg Stokes identity `(17)` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Corpus reuse

The two-leg reciprocal transport `(16)`–`(17)` was **not** rebuilt: `legTransport`, `stokesForm`
and `legTransport_stokes` already exist in `GeneralizedPrimeCountermodel`, and this module imports
them.  The adelic product formula `(18)` reuses mathlib's `Height.AdmissibleAbsValues`, which is
instantiated for every number field, `ℚ` included.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`, over an arbitrary abelian
grading group `ι` and an arbitrary `ℂ`-algebra `A` with `GradedAlgebra 𝒜` — the generality of
card `(1)`.

Theorem 1, the total-grade gauge law:

1. `gradeComponent`, `gradeComponent_of_mem`, `gradeComponent_of_mem_ne` — the homogeneous
   components, as `ℂ`-linear maps.
2. `gradeDiag` — **card `(3)`**: the diagonal endomorphism `Γ_f(a_g) = f(g) a_g` of a multiplier.
3. `gradeDiag_of_mem`, `gradeComponent_gradeDiag` — `Γ_f` is diagonal and preserves every
   component.
4. `gradeDiag_mul`, `gradeDiag_one` — **Theorem 1.1**: a *character* multiplier gives an algebra
   endomorphism.
5. `gradeDiag_comp`, `gradeDiag_one_multiplier` — composition multiplies multipliers.
6. `gradeGaugeHom`, `gradeGauge` — **Theorem 1.1**: `Γ_χ` is an algebra *automorphism*
   `A ≃ₐ[ℂ] A`, with inverse `Γ_{χ⁻¹}` built from `χ(−i)`.
7. `totalGrade` — **card `(4)`**: the total grade of a homogeneous cyclic chain.
8. `totalGrade_face`, `totalGrade_lastFace`, `totalGrade_degeneracy`, `totalGrade_rotate` —
   **Theorem 1.3**: every Hochschild face, the wrap-around last face, every degeneracy and cyclic
   rotation preserve the total grade; the last two use commutativity of the grading group.
9. `prod_multiplier_eq` — **Theorem 1.2, equation `(5)`**: `Γ_χ^{⊗(n+1)}` acts on a homogeneous
   chain by `χ` of the total grade.
10. `prod_multiplier_eq_one` — **Theorem 1.4**: the total-grade-zero cyclic sector is pointwise
    fixed by the whole gauge family.
11. `prod_multiplier_primeAtom` — **Corollary 2, equation `(10)`**: `Γ_c^{⊗2} u_p = u_p` for every
    real `c`, because `e_i + (−e_i) = 0`.

Theorem 3, the logarithmic detector is still equivariant:

12. `gradeDiag_leibniz` — **equation `(11)`**: an *additive* multiplier gives a derivation `∂_L`.
13. `gradeDiag_commute` — **equation `(12)`, first half**: `∂_L Γ_χ = Γ_χ ∂_L`.
14. `identityTrace`, `identityTrace_gradeDiag` — the identity-coefficient trace and its gauge
    invariance, from `χ(0) = 1`.
15. `kummerCocycle`, `kummerCocycle_gradeDiag` — **equation `(12)`, second half**: the Kummer
    one-cocycle `φ_L(a,b) = τ(a ∂_L b)` is invariant under the whole radial family.

Theorems 4 and 5, cross-grade lines:

16. `radialMultiplier`, `radialMultiplier_zero`, `radialMultiplier_add` — **equation `(7)`**: the
    radial character `χ_c(g) = |g|^c`.
17. `rpow_eq_rpow_iff` — for distinct positive grades, `a^c = b^c` iff `c = 0`.
18. `radial_line_invariant_iff` — **Theorem 4, equation `(13)`**: the line spanned by a sum of two
    nonzero homogeneous vectors of distinct absolute grade is `Γ_c`-invariant iff `c = 0`.
18b. `gradeComponent_sum`, `radial_finite_invariant_iff`, `radial_finite_invariant_eq_zero` —
    the card's **"more generally"** after Theorem 4: the radial stabilizer of a finite
    nonhomogeneous vector is the intersection of the equal-character conditions `ν i ^ c = ν j ^ c`
    across its grade support, and two distinct positive absolute grades in the support already
    force `c = 0`.  Item 18 is the two-summand case.
19. `radial_line_transport` — **Theorem 5, equation `(15)`**: `Γ_c L_λ = L_{λ(ν_j/ν_i)^c}`.
20. `radial_parameter_transitive` — **Theorem 5**: the radial family is transitive on the positive
    parameters, so trivial stabilizer does not select a member: the family is a gauge slice.

The countermodel:

21. `reciprocal_stokes_blind` — **equations `(16)`–`(17)`**: `T_c^* J T_c = J` at every drift.
22. `adelic_product_blind` — **equation `(18)`**: the adelic product formula raised to any real
    power is one, for any field carrying an admissible family of absolute values.

## Scope

Equation `(19)`, the physical residue `Res(D_{n,ρ}u_p) = (δ_n(ρ) − 1) c_ρ`, is formalized in
`ConstraintRelativity/ForgetfulTower.lean`, which owns the same equation as its card `(9)`:
`sourceScalar_cycleTransport_eq_zero_iff` shows the residue vanishes exactly on the critical line,
and `legCarrier_cycleTransport_eq_zero_iff` says the carrier degenerates there and nowhere else.
It is not rebuilt here.

The card's remaining reading of `(19)`, the seven conjecture/failure loops and the
Nomotopy consequence are commentary on this theorem chain, not separate theorems; the card itself
states that it "does not construct missing relation and does not prove RH".  Nothing there is
formalized.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/IdentitySectorRadialBlindness.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.IdentitySectorRadialBlindness          # green
```
