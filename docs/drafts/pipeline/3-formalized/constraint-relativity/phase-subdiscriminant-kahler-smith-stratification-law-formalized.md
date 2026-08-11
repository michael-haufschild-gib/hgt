# Phase-subdiscriminant Kähler–Smith stratification law — formalized

- **ID:** `phase-subdiscriminant-kahler-smith-stratification-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `phase-subdiscriminant-kahler-smith-stratification-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.PhaseSubdiscriminantKaehlerSmith` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/PhaseSubdiscriminantKaehlerSmith.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Corpus reuse

Nothing below was rebuilt.

- The whole DVR/Smith layer of `ultrametric-horizon-energy-smith-correspondence-formalized.md`:
  `SmithNormalFormDVR` (`exists_smithNormalForm`, `detIdeal_diagonal_chain`,
  `cokernel_equiv_pi_of_diagonal`), `DeterminantalIdeal` (`detIdeal`, `detIdeal_unit_mul`,
  `detIdeal_le`, `minor_mem_detIdeal`, `val_le_val_of_strictMono`), `DVRFiniteSpan`.
- `HTGeometry/VandermondeSign.lean`: `vandermondeProd`, `det_vandermonde_eq_vandermondeProd`.
- `HTGeometry/KroneckerWeylDensity.lean`: `expChar` and **Kronecker's approximation theorem**
  `kronecker_approx` — card `(22f)` is corpus-owned.
- `Core.lean`: `linearIndependent_log_primes`.
- `ConstraintRelativity/MonogenicKaehler.lean`: `kaehlerEquivMonogenic`, `Ω[A⁄R] ≅ A/(f′(α))`,
  which is what licenses calling `A/(P′)A` the cotangent defect.
- From mathlib: `Matrix.vandermonde`, `Matrix.detRowAlternating`, `Matrix.PosDef.det_pos`,
  `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`, `Polynomial.derivative_prod_finset`,
  `Submodule.quotientPi`, `Complex.isPrimitiveRoot_exp`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Setup and the observer staircase:

1. `contactSheets`, `vandermonde_contactSheets` — card `(3)` and the factorisation
   `V(f) = V(u)·diag(1, c, …, c^{N−1})`.
2. `isUnit_det_vandermonde_of_separated` — card `(2)`: distinct residues make `V(u)` invertible
   over `R`.
3. `contactScaling_chain`, `contact_cokernel_equiv` — **card `(8)` boxed**: `C ≅ ∏_j R/(c^j)`.
4. `detIdeal_contact` — every determinantal ideal of the observer is `(c^{k(k−1)/2})`.

Lemma 2, the southwest-moment identity:

5. `residuePoly`, `cofactorPoly`, `linear_mul_cofactorPoly`, `coeff_cofactorPoly_succ`,
   `coeff_cofactorPoly` — the synthetic-division law for the cofactor coefficients.
6. `cofactorMatrix`, `vandermonde_mul_cofactorMatrix` — `V(u)·E = diag(Q′(u_i))`, hence `E = V⁻¹D`
   **without division**.
7. `moment`, `momentMatrix`, `phaseSubdiscriminant` — cards `(6)`, `(7)`.
8. `residueMult`, `vandermonde_mul_residueMult` — the multiplication matrix `B = E·V(u)`.
9. `southwestRows`, `coeffTriangle`, `det_coeffTriangle`, `submatrix_residueMult_southwest`,
   `det_submatrix_residueMult_southwest` — **card `(11)` boxed**: the southwest `k × k` minor of
   `B` is exactly `H_k`.  The card's trace functional `(12)`–`(13)` is replaced by `B = E·V`, which
   makes the top row of `B` the moment row by inspection and the remaining southwest rows a unit
   lower-triangular combination of moment rows.

The contact scaling and the all-Fitting square law:

10. `contactScale_apply`, `det_submatrix_contactScale` — **cards `(16)`, `(17)`**.
11. `sum_le_sum_of_injective`, `pow_dvd_det_submatrix_contactScale`, `det_southwest_contactScale`,
    `detIdeal_contactScale` — **card `(18)` boxed**.
12. `mul_diagonal_const`, `vandermonde_contactSheets_mul_contactScale` — **card `(16)`**: the
    contact-scaled residue multiplication matrix is intertwined with multiplication by the sheet
    values of `P′ = c^{N−1}Q′`, so it presents `Ω`.
13. `detIdeal_contactScale_eq_sq` — **card `(15)` boxed**: `Fitt(Ω) = Fitt(C)²` at every height.
14. `coeffEval`, `coeffPoly`, `exists_coeffEval_ne_zero`, `posDef_momentMatrix`,
    `phaseSubdiscriminant_pos` — **card `(14)` real chamber**: distinct real residues make the
    Hankel moment matrix positive definite, so `H_k > 0` for all `k ≤ N`.  Proved by root counting,
    not by Cauchy–Binet.

Total length and the phase jump:

15. `momentMatrix_top`, `phaseSubdiscriminant_top`, `isUnit_phaseSubdiscriminant_top`,
    `detIdeal_contactScale_top`, `sum_val_fin` — **card `(20)` boxed**: `H_N = (∏_{i<j}(u_j−u_i))²`
    is a unit for separated residues, so the top determinantal ideal is `(c^{N(N−1)})` whatever the
    phase.
16. `exists_perm_of_sum_eq`, `detIdeal_contactScale_le`, `detIdeal_contactScale_le_generic`,
    `detIdeal_contactScale_lt_of_wall` — **card `(19)` boxed**: the southwest/first minor is the
    unique minor at the lowest `c`-exponent, so on a wall the `k`-th determinantal ideal drops
    strictly below its generic value while, by `(8)` and `(20)`, the observer barcode and the total
    length do not move.

The self-dual sandwich:

17. `observerLattice`, `differentDiag`, `range_differentDiag_le` — **card `(11a)`**: `R^N ⊆ A^♯`.
18. `differentDiag_injective`, `ker_differentComp` — the sub of the sandwich is `C = R^N/A`.
19. `mapQ_id_surjective`, `ker_mapQ_id`, `differentSub`, `differentMid`, `differentSub_le`,
    `sandwich_exact` — **card `(11b)` boxed**: `0 → C → Ω → C† → 0`.

The successor sequence:

20. `belowPoly`, `successorGap`, `eval_belowPoly_castSucc`, `eval_belowPoly_eq`,
    `exists_shift_mulVec`, `succProj`, `succProj_range_le`, `successorMap`,
    `successorMap_surjective`, `lastLine`, `eq_single_last`, `range_lastLine_eq_ker`,
    `mulVec_eq_coeffEval`, `coeffEval_belowPoly`, `ker_lastLine` — **card `(24)` boxed**:
    `0 → R/(P_N(x_q)) → C_{N+1} → C_N → 0`.

Walls and the three-node classification:

21. `phaseSubdiscriminant_two`, `cubeRootTriple`, `phaseSubdiscriminant_cubeRootTriple`,
    `squareQuadruple`, `phaseSubdiscriminant_squareQuadruple` — **cards `(21)`, `(22)`, `(22a)`**.
22. `phaseSubdiscriminant_two_triple`, `phaseSubdiscriminant_two_centered`,
    `esymm_two_centered_eq_zero`, `cube_eq_of_centered`, `cube_centered_eq_of_wall`,
    `phaseSubdiscriminant_equilateral` — **the wall is exactly the affine equilateral locus**:
    `H_2 = 3∑μ_i²` on the barycentred nodes, so on the wall every centred node has the same cube,
    and conversely every `m + sω^i` lies on the wall.  This is the card's `z_i = m + sω^i` written
    without choosing a cube root.
23. `residueMult_eq_of_intertwine`, `cubeRootTriple_pow_three`,
    `cofactorPoly_eval_cubeRootTriple`, `residueMult_cubeRootTriple`, `detIdeal_two_generic`,
    `detIdeal_two_le_of_triple_wall`, `detIdeal_two_cubeRootTriple` — **cards `(22b)`, `(22c)`
    boxed**: off the wall the second determinantal ideal is `(c²)` (type `R/(c²) ⊕ R/(c⁴)`); at the
    equianharmonic wall it is exactly `(c³)` (balanced type `R/(c³) ⊕ R/(c³)`).

The fixed-radius criterion and the prime phase wall:

24. `exists_sq_add_sq_and_mul`, `exists_primitiveCubeRoot`, `cubeRoot_re_im`, `normSq_cubeRoot`,
    `conj_cubeRoot`, `sum_re_sq_cubeRoot`, `sum_re_cubeRoot_eq_zero`, `normSq_equilateral`,
    `rotationOfDefect`, `two_re_rotationOfDefect`, `wall_radii_forward`,
    `wall_radii_criterion` — **card `(22d)` boxed**: positive radii admit phases putting the nodes
    on the wall exactly when `(∑ρ²)² ≥ 2∑ρ⁴`.
25. `criterion_of_ordered`, `primeTripleIdx`, `primeLogRadius`,
    `linearIndependent_primeLogRadius`, `primeTriple_criterion`, `exists_primeWall`,
    `norm_phaseSubdiscriminant_sub_le`, `primeOrbit_approaches_wall` — **cards `(22f)`, `(22g)`,
    `(22h)` boxed**: the triple `(101, 103, 107)` satisfies the criterion (via `107³ < 101⁴`), the
    prime log frequencies are rationally independent, and the one-clock orbit therefore comes
    arbitrarily close to the balanced wall — `inf_t |H_2((log p_i)e^{it log p_i})| = 0`.

Card `(5)` (`Ω ≅ A/(P′)dT`) is `MonogenicKaehler.kaehlerEquivMonogenic`, already in the corpus.

## Scope

The card states plainly that `H_k = 0` is phase stratification and not an RH criterion, that no
black-hole or Brown–Susskind observable is derived, and that whether the one-clock orbit *exactly*
hits a wall is open; `primeOrbit_approaches_wall` proves only the approach, matching `(22h)`.  The
"Hostile novelty boundary", "Conjecture/failure loops" and "Predictions" sections are commentary.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/PhaseSubdiscriminantKaehlerSmith.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.PhaseSubdiscriminantKaehlerSmith          # green
```

`#print axioms` on `contact_cokernel_equiv`, `detIdeal_contact`,
`det_submatrix_residueMult_southwest`, `detIdeal_contactScale`, `detIdeal_contactScale_eq_sq`,
`phaseSubdiscriminant_pos`, `detIdeal_contactScale_top`, `detIdeal_contactScale_lt_of_wall`,
`detIdeal_two_generic`, `detIdeal_two_cubeRootTriple`, `sandwich_exact`, `ker_differentComp`,
`ker_lastLine`, `successorMap_surjective`, `range_lastLine_eq_ker`, `wall_radii_criterion`,
`cube_centered_eq_of_wall`, `primeTriple_criterion` and `primeOrbit_approaches_wall` returns only
`[propext, Classical.choice, Quot.sound]`.
