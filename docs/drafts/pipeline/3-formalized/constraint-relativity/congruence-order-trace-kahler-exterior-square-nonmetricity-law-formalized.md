# Congruence-order trace--Kähler exterior-square discrepancy law — formalized

- **ID:** `congruence-order-trace-kahler-exterior-square-nonmetricity-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `congruence-order-trace-kahler-exterior-square-nonmetricity-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module (namespace `HTGeometry.ConstraintRelativity`) | Path under `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/` |
|---|---|
| `CongruenceOrderExteriorSquare` | `CongruenceOrderExteriorSquare.lean` |
| `CongruenceOrderTraceDual` | `CongruenceOrderTraceDual.lean` |
| `CongruenceOrderHorizon` | `CongruenceOrderHorizon.lean` |
| `CongruenceOrderSoldering` | `CongruenceOrderSoldering.lean` |
| `CongruenceOrderResidueHom` | `CongruenceOrderResidueHom.lean` |
| `CongruenceOrderKaehlerDifferent` | `CongruenceOrderKaehlerDifferent.lean` |
| `CongruenceOrderFirstOrder` | `CongruenceOrderFirstOrder.lean` |

All seven are wired into `GaloisForLFunctions.HTGeometry`.

## Setting

`R` is a commutative domain, `a : R` is nonzero, and `N = m + 1` sheets are used.  The card's
standing hypotheses appear as the typeclass assumptions `[Invertible (2 : R)]`,
`[Invertible ((m : R) + 1)]` (that is `N`), `[Invertible ((m : R) - 1)]` (that is `N − 2`), the
inequality `2 ≤ m` (that is `N ≥ 3`), and — only where the card measures lengths —
`(Ideal.span {a}).IsMaximal`, which is what makes `k = R ⧸ (a)` the residue field.  The total
quotient algebra is any fraction field `K` of `R`.  No other hypothesis is used anywhere.

The order itself is `congruenceOrder a N = {v : Fin N → R | ∀ i j, a ∣ v i − v j}`, and its
presentation `A = MvPolynomial (Fin m) R ⧸ congruenceIdeal a m` is the ring over which the
cotangent module and the trace-law defect are compared.

## Formal theorem chain

1. `observerDefectEquiv` — **card `(3)`**: `O/A ≅ k^m`.
2. `congruencePresentation` — **card `(15)`**: `A ≅ R[x₁,…,x_m]/(xᵢ² − a xᵢ, xᵢxⱼ)`;
   `congruenceCoordEquiv` gives the free `R`-basis `1, x₁, …, x_m`.
3. `kaehlerModelEquiv` — the cotangent module is the cokernel of the differentiated relations,
   `Ω[A⁄R] ≃ₗ[A] (Aᵐ ⧸ kaehlerRelations)`.
4. `kaehlerCongruenceEquiv` — **card `(5)`, boxed**:
   `Ω[A⁄R] ≃ₗ[R] (Fin m → R ⧸ (a²)) × (pairIndex m → R ⧸ (a))`, the diagonal sector carrying the
   `dxᵢ` and the antisymmetric sector carrying `xⱼdxᵢ = −xᵢdxⱼ`.
5. `mem_traceDual_iff`, `traceDual_eq_map` — **card `(9)`**: `A♯ = a⁻¹·{z : a ∣ ∑ zᵢ}`.
6. `traceDefectEquiv` — **card `(4)`, boxed**: `L = A♯/A ≅ (R/a²)^m`; the integral form is
   `scaledTraceDefectEquiv`.  The proof needs no Smith machinery: the map
   `z ↦ (zᵢ − N⁻¹∑ⱼ zⱼ) mod a²` is surjective on the rescaled dual with kernel the rescaled order,
   because `N − m = 1` forces the last coordinate into the same class as the others.
7. `card_pairIndex` — **card `(7)`, boxed**: the antisymmetric sector has rank `binom (N−1) 2`.
8. `horizonExteriorSquareEquiv` — **card `(6)`, boxed**:
   `Ω/aΩ ≃ₗ[k] C × ⋀[k]^2 C` with `C = k^m`; `kaehlerFibreEquiv` is the `R`-linear half.
9. `length_cotangentModel`, `length_traceDefectModel` — **card `(27)`**: lengths `2m + binom m 2`
   and `2m`; `length_cotangentModel_eq_length_traceDefect_add` — **card `(28)`, boxed**.
10. `traceDefectModelEquiv_congruenceX_smul` — **card `(26b)`**: the action of the source
    generators on `L` in coordinates; `maximalIdealA_smul_eq` — **card `(26b)`**: `𝔪_A·L = a·L`.
11. `soldering_range_le` — **card `(26e)`, boxed**: every `φ : Ω[A⁄R] →ₗ[A] L` has image inside
    `a·L`.  This is where `N` and `N − 2` being units enters, exactly as in the card.
12. `soldering_head_eq_zero` — **card `(26g)`, boxed**: the tangent-head reduction of every such
    `φ` is identically zero.
13. `maximalIdealA_smul_aMulA` (`𝔪_A·aL = 0`), `soldering_annihilates_maximalIdeal` (every `φ`
    kills `𝔪_A·Ω`, hence factors through the closed cotangent fibre), `aMulTraceDefectEquiv`
    (`aL ≅ k^m`) and `solderingHomMatrixEquiv` — **card `(26f)`, boxed**:
    `Hom_A(Ω[A⁄R], L) ≅ Mat_{m×m}(k)`.
14. `mem_dedekindDifferent_iff` — **card `(26k)`, boxed**: `𝔇_D = a²·O`.  The hypothesis `N ≥ 3`
    is used exactly where the card uses it: a third coordinate of `d·bᵢ` vanishes.
15. `kaehlerFittingIdeal`, `prod_sqCoeff_mem_fitting` (**card `(26o)`**),
    `mixed_mem_fitting` (**card `(26n)`**), `kaehlerFittingIdeal_eq` — **card `(26l)`, boxed**:
    `𝔇_K = Fitt₀^A Ω[A⁄R] = aᵐ·O`.
16. `residueEquiv` — `A/𝔪_A ≅ k`; `maximalIdealSq_smul_kaehler`,
    `maximalIdealSq_smul_traceDefect` — **card `(26j1)`**: `𝔪²Ω = 0` and `𝔪²L = 0`, so both
    modules factor through the square-zero thickening `A/𝔪²`.
17. `headReduction`, `headReduction_eq_zero` — **card `(26j2)`**: the reduction of a source-linear
    comparison to the closed fibres is identically zero.
18. `kaehlerHeadEquiv` (`Ω/𝔪Ω ≅ (A/𝔪)^m`), `traceDefectHeadEquiv'` (`L/𝔪L ≅ k^m`),
    `homHeadEquiv`, `solderingObstructionEquiv` — **card `(26j3)`, boxed**:
    `𝒩₀ = coker(26j2) ≅ Mat_{m×m}(k)`.
19. `headMap_eq_zero_of_lifts` — the card's consequence, and the concrete sharp model of
    `source-soldering-transport-defect-cocycle-and-law-symbol`: only the zero head map lifts, so
    every nonzero tangent soldering has a nonzero first-order obstruction.

## Infrastructure built here (absent from mathlib)

- **Zeroth Fitting ideal.**  mathlib has no Fitting-ideal theory at all.  `kaehlerFittingIdeal` is
  the ideal generated by the maximal minors of the canonical relation matrix, together with the
  two bounds `kaehlerFittingIdeal_le_sheetPow` and `sheetPow_le_kaehlerFittingIdeal`.
- **`sheetPow a m n`** — the ideal `aⁿ·O` of the congruence order, with `mul_mem_sheetPow`,
  `prod_mem_sheetPow` and `det_mem_sheetPow` (a determinant of entries in `a·O` lies in `aᵐ·O`).
- **`aMul a M` = `a·M`** with `aMul_eq_smul_top`, `aMul_prod`, `aMul_pi`, `map_aMul`,
  `prodFibreEquiv`, `piFibreEquiv`, `sqFibreEquiv` (`(R/a²)/a(R/a²) ≅ R/a`), `linFibreEquiv`.
- **`quotientScalarsEquiv`** — an `R`-linear equivalence of `R ⧸ I`-modules whose `R`-action
  factors through `R ⧸ I` is `R ⧸ I`-linear.
- **`submodulePiEquiv`** — `↥(Submodule.pi univ p) ≃ₗ ∀ i, ↥(p i)`.
- **`pairIndexEquivPowersetCard`**, `exteriorSquareModel` — the antisymmetric index set is the set
  of two-element subsets, and `(pairIndex m → k) ≃ₗ[k] ⋀[k]^2 (Fin m → k)`.
- **`congruencePiAlgebra`** — the sheet algebra `R^N` as an algebra over the presented congruence
  order, with `scaledDualA`, `scaledOrderA` and the resulting `A`-module `traceDefect a m`.

## Scope

Everything the card boxes is formalized, including the first-infinitesimal items `(26j1)`–`(26j3)`.
The card's own disclaimers are respected: no comparison map `L → Ω_{A/R}` is constructed anywhere
(the `Λ²C` summand appears only inside the closed-fibre decomposition (6)), no connection or
curvature tensor is built, and no RH statement is touched.  The exceptional case `N = 2` that the
card excludes from `(26l)` is excluded here by `2 ≤ m`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/CongruenceOrderExteriorSquare.lean     # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/CongruenceOrderTraceDual.lean          # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/CongruenceOrderHorizon.lean            # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/CongruenceOrderSoldering.lean          # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/CongruenceOrderResidueHom.lean         # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/CongruenceOrderKaehlerDifferent.lean   # clean
lake build GaloisForLFunctions.HTGeometry                                                                # green
```
