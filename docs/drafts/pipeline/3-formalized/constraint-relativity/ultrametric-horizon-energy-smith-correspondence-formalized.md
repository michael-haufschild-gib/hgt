# Ultrametric horizon energy–Smith correspondence — formalized

- **ID:** `ultrametric-horizon-energy-smith-correspondence-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `ultrametric-horizon-energy-smith-correspondence.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.AlternantVandermondeDivisibility` | `formal/GaloisForLFunctions/HTGeometry/AlternantVandermondeDivisibility.lean` |
| `GaloisForLFunctions.HTGeometry.DVRFiniteSpan` | `formal/GaloisForLFunctions/HTGeometry/DVRFiniteSpan.lean` |
| `GaloisForLFunctions.HTGeometry.DeterminantalIdeal` | `formal/GaloisForLFunctions/HTGeometry/DeterminantalIdeal.lean` |
| `GaloisForLFunctions.HTGeometry.SmithNormalFormDVR` | `formal/GaloisForLFunctions/HTGeometry/SmithNormalFormDVR.lean` |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.UltrametricHorizonEnergySmith` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/UltrametricHorizonEnergySmith.lean` |

All five are wired into `GaloisForLFunctions.HTGeometry`.

## Corpus reuse

`vandermondeProd`, `det_vandermonde_eq_vandermondeProd`, `vandermondeProd_ne_zero`,
`vandermondeProd_comp` come from `HTGeometry/VandermondeSign.lean` and were **not** rebuilt.  From
mathlib: `Matrix.vandermonde`, `Matrix.det_vandermonde`, `Matrix.detRowAlternating`,
`MultilinearMap.map_sum`, `IsDiscreteValuationRing.addVal` with `addVal_le_iff_dvd`, `addVal_def`,
`eq_unit_mul_pow_irreducible`, `Tuple.sort`, `Submodule.quotientPi`, `Submodule.Quotient.equiv`,
`Polynomial.derivative_prod_finset`.

## New infrastructure

mathlib has no Schur polynomials, no alternants, no determinantal ideals, no Fitting ideals and no
Smith normal form.  Built here, all general-purpose:

- **Alternant divisibility.**  `vandermondeProd_dvd_det_eval`: for any points `v` and any
  polynomials `p`, `∏_{i<j}(v j − v i)` divides `det((p j).eval (v i))`; hence
  `vandermondeProd_dvd_det_pow`, the classical statement that the Vandermonde product divides every
  alternant.  Proof: subtract the top row, factor `v i − v 0` out of each remaining row using the
  divided difference `dividedDifference`, and expand along the top row to recurse.  Schur
  polynomials are never needed.  Supporting: `prod_Ioi_zero_eq_prod_succ`,
  `prod_Ioi_succ_eq_prod_Ioi`, `vandermondeProd_succ`, `dividedDifference_spec`, `eval_sub_eval`.
- **Finite spans in a DVR.**  `exists_dvd_of_finset`, `exists_span_finset_eq_span_singleton`,
  `exists_span_singleton_eq_span_pow`, `addVal_of_isUnit`, `addVal_eq_of_associated`,
  `addVal_eq_of_span_eq`, `addVal_prod`.
- **Determinantal ideals.**  `detIdeal`, `minor_mem_detIdeal`, `detIdeal_le`,
  `detIdeal_mul_le_right`, `detIdeal_transpose`, `detIdeal_mul_le_left`, `detIdeal_unit_mul`,
  `detIdeal_mul_unit`, `detIdeal_equiv`.  Equivalence invariance is proved by expanding a minor of
  a product with `MultilinearMap.map_sum` on `Matrix.detRowAlternating`; Cauchy–Binet is not
  needed.  Also `val_le_val_of_strictMono`.
- **Smith normal form over a DVR.**  `exists_smithNormalForm`: every square matrix satisfies
  `U M V = diagonal d` with `IsUnit U.det`, `IsUnit V.det` and `d i ∣ d j` for `i ≤ j`.  The
  algorithm is carried by the corner extension `blockPivot`/`blockOne` (`det_blockPivot`,
  `blockOne_mul_blockPivot`, `blockPivot_mul_blockOne`, `blockPivot_diagonal`) and the elementary
  clearing matrices `clearCol`, `clearRow` (`det_clearCol`, `det_clearRow`, `clearCol_mul_zero`,
  `clearCol_mul_succ`, `mul_clearRow_zero`, `mul_clearRow_succ`, `eq_blockPivot`,
  `dvd_entries_mul_left/right`, `isUnit_det_rowPerm`, `isUnit_det_colPerm`).
- **Determinantal divisors and the barcode.**  `prod_castLE_dvd_prod`, `detIdeal_diagonal_chain`,
  `exists_smith_detIdeal`, `range_diagonal_mulVecLin`, `range_mulVecLin_eq_top`,
  `exists_cokernel_equiv_pi`.

## Formal theorem chain

Card declarations live in namespace `HTGeometry.ConstraintRelativity`; the infrastructure lives in
`GaloisForLFunctions.HTGeometry`.

1. `collisionEnergy` — **card `(5)`**: `E(I) = ∑_{α<β} v(x_{Iβ} − x_{Iα})`, with
   `collisionEnergy_eq_addVal` identifying it with the valuation of the Vandermonde product of the
   configuration.
2. `injMaps`, `minCollisionEnergy` — **card `(6)`**: `d_k = min_{|I|=k} E(I)`, as a `Finset.inf`
   over the injective selections (so `k > N` gives `⊤`, and no nonemptiness side condition is
   carried).
3. `minorSet`, `determinantalIdeal`, `determinantalIdeal_eq_detIdeal` — the object of card `(7)`.
4. `submatrix_vandermonde_eq`, `vandermondeProd_dvd_minor`, `minCollisionEnergy_le_addVal_minor` —
   **card `(12)`**: every minor is divisible by the Vandermonde product of the rows it uses, hence
   has valuation at least `d_k`; non-injective selections give a vanishing minor.
5. `minor_firstColumns`, `injMaps_nonempty`,
   `exists_determinantalIdeal_eq_span_vandermondeProd` — the minimum is attained by the first `k`
   columns of an energy-minimizing row selection.
6. `exists_determinantalIdeal_eq_span_pow` — **card `(7)`, boxed**: `D_k(V) = (a^{d_k})`.
7. `collisionEnergy_comp_perm`, `exists_strictMono_collisionEnergy` — energy is a function of the
   configuration, not of its listing, so every configuration may be taken increasing.
8. `addVal_det_vandermonde`, `minCollisionEnergy_self` — **card `(14)`**: `ord_a det J = d_N`.
9. `sheetDiscriminant`, `addVal_sheetDiscriminant`, `span_sheetDiscriminant_eq_sq` — **card `(14)`,
   `(15)`**: `ord_a Disc(P) = 2 d_N` and `(Disc) = (det J)²`.
10. `vandermonde_mulVec_injective` — **Corollary 2**: the observer is injective.
11. `span_det_eq_span_vandermondeProd` — **card `(15)`, first identity**: the zeroth Fitting ideal
    of the cokernel, i.e. the determinant ideal of the presentation, is generated by the
    orientation.
12. `prod_Iio_eq_vandermondeProd`, `prod_offDiag_eq`, `span_prod_offDiag`,
    `derivative_sheetPoly_eval`, `det_of_intertwine`, `span_det_intertwine_eq_discriminant`,
    `addVal_det_intertwine` — **card `(15)`, boxed, cotangent half**.  `Ω_{A/R} ≅ A/(P')`
    (`MonogenicKaehler.kaehlerEquivMonogenic`, already in the corpus) is presented over `R` by
    multiplication by `P'(α)` on the free module `A`; any matrix `W` of that operator satisfies
    `V W = diag(P'(x_i)) V`, so `det W = ∏_i P'(x_i) = ∏_i ∏_{j≠i}(x_i − x_j)`, which generates
    `(Disc(P)) = (det J)²` and has valuation `2 d_N`.  `derivative_sheetPoly_eval` supplies
    `P'(x_i) = ∏_{j≠i}(x_i − x_j)`.  The determinant identity is obtained by cancelling `det V`,
    not by developing norms or resultants.
13. `exists_sheetBarcode` — **cards `(8)`, `(9)`, `(13)`**: there is an invariant-factor chain `d`
    with `d_k = ∑_{α<k} v(d_α)` for every `k ≤ N`, and the cokernel of the observer is
    `∏_i R/(d i)` — over a finite index this product is the direct sum of card `(13)`.
14. `minCollisionEnergy_succ` — **card `(9)`, boxed**: `s_k = d_k − d_{k−1}`, the Smith spectrum is
    the discrete derivative of the minimum-energy profile.
15. `addVal_invariantFactor_mono` — **card `(26)`**: the exponents increase, i.e. the energy profile
    is convex.
16. `SeparatedProfile`, `collisionEnergy_of_separated` — **card `(23)`**.
17. `minCollisionEnergy_of_separated` — **card `(18)`, boxed, `d_k` half**:
    `d_k = ∑_{i<k−1}(k−1−i) r_i`, the minimum being attained on the shallowest `k` sheets, since a
    strictly monotone selection never moves an index down (`val_le_val_of_strictMono`).
18. `minCollisionEnergy_succ_of_separated` — **cards `(18)` `s_k` half, `(19)`, `(21)`, `(22)`**:
    `s_k = ∑_{i<k} r_i`.  Cards `(21)` and `(22)` are the instances at `k = N−1` and `k = N`: the
    maximal observer depth is `r_1 + … + r_{N−1}`, and the bar appended by one further deepest
    sheet is the accumulated history of the earlier sheets, independent of the new order.
19. `span_sheets_eq_span_pow` — **card `(20)`**: the underived ideal of the sheets is `(a^{r_1})`.

Card `(24)` (`r_i = r` gives `s_k = (k−1)r`) is the constant-profile instance of item 18.

## Scope

The card's "Hostile novelty boundary", "Conjecture/failure loops" and "Predictions" sections are
commentary; items 1–19 are every displayed equation.  The card states plainly that it does not
choose a horizon and does not imply RH, and nothing of that kind is formalized.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/UltrametricHorizonEnergySmith.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.UltrametricHorizonEnergySmith          # green
```

`#print axioms` on `vandermondeProd_dvd_det_eval`, `exists_smithNormalForm`, `detIdeal_equiv`,
`detIdeal_diagonal_chain`, `exists_smith_detIdeal`, `exists_cokernel_equiv_pi`,
`exists_determinantalIdeal_eq_span_pow`, `exists_sheetBarcode`, `minCollisionEnergy_succ`,
`addVal_invariantFactor_mono`, `minCollisionEnergy_of_separated`,
`minCollisionEnergy_succ_of_separated`, `span_sheets_eq_span_pow`, `addVal_sheetDiscriminant`,
`span_det_intertwine_eq_discriminant`, `addVal_det_intertwine` and
`vandermonde_mulVec_injective` returns only `[propext, Classical.choice, Quot.sound]`.
