# Pagewise Hodge formation and stable-organ selection — Lean certification

- **ID:** ULF-LHSM-5
- **Paper card:** `pagewise-hodge-formation-properness-and-stable-organ-selection-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ConstitutivePagewiseFormationSelection`
  (finite diagonal normal form), `GaloisForLFunctions.HTGeometry.PagewiseHodgeFlag`
  (§1–§2), `GaloisForLFunctions.HTGeometry.PagewiseHodgeFormation` (§3–§7),
  `GaloisForLFunctions.HTGeometry.OperatorAbsoluteValueBetween` (mathlib gap)
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## New mathlib gap closed

`ContinuousLinearMap.absMap (T : K →L[ℂ] C) : K →L[ℂ] K` is the absolute value `|T| = √(T†T)`
of an operator **between two different Hilbert spaces** — mathlib and the corpus only had the
endomorphism case (`ContinuousLinearMap.absOp`).  Certified: `absMap_nonneg`,
`isSelfAdjoint_absMap`, `absMap_mul_self`, `absMap_comp_self`, `norm_absMap_apply`
(`‖|T| x‖ = ‖T x‖`), `ker_absMap`.  Positivity of `T†T` in the Loewner order comes from
`ContinuousLinearMap.le_def` plus `isPositive_adjoint_comp_self`.

## §1–§2: the Hodge flag (`PagewiseHodgeFlag`)

A realization is a family `d : ℕ → (K →L C)`; the flags are generated from it:

| Card | Lean |
|---|---|
| `K_{r+1} = ker d_r` | `kerFlag d (r+1) = kerFlag d r ⊓ ker (d r)` |
| `C_{r+1} = C_r ∩ (ran d_r)^⊥` | `cokerFlag d (r+1) = cokerFlag d r ⊓ (deathImage d r)ᗮ` |
| `L_r⁻ = ran d_r` | `deathImage d r = map (d r) (kerFlag d r)` |
| `L_r⁺ = K_r ∩ K_{r+1}^⊥` | `deathPos d r` |

* `isClosed_kerFlag`, `isClosed_cokerFlag`, `isClosed_deathPos` with the matching
  `CompleteSpace` instances; `kerFlag_antitone`, `kerFlag_le`, `cokerFlag_antitone`,
  `cokerFlag_le`;
* `deathPos_sup_kerFlag` and `deathImage_sup_cokerFlag` — the pagewise orthogonal splits
  `K_r = L_r⁺ ⊕ K_{r+1}`, `C_r = L_r⁻ ⊕ C_{r+1}`;
* `cokerFlag_inf_orthogonal` — `(PHF.6)`: `C_r ∩ C_{r+1}^⊥ = ran d_r`;
* `inner_deathPos_eq_zero`, `inner_deathPos_kerFlag_eq_zero`, `inner_deathImage_eq_zero`,
  `inner_deathImage_cokerFlag_eq_zero` — pairwise orthogonality of all layers;
* `sup_deathPos_sup_kerFlag`, `sup_deathImage_sup_cokerFlag` — **Theorem 2.1 `(PHF.9)`**;
* `exists_death_decomposition`, `norm_sq_death_decomposition`,
  `exists_deathImage_decomposition`, `norm_sq_deathImage_decomposition` — **`(PHF.11)`**, the
  exact conservation identity;
* `map_deathPos`, `deathMap`, `deathMap_injective`, `deathMap_surjective`, `deathEquiv` —
  `(PHF.7)`, the page bijection `d̂_r : L_r⁺ ≅ L_r⁻` (open mapping theorem);
* `exists_pos_deathGap` — **`(PHF.8)`**, the positive reduced minimum modulus `γ_r > 0`;
* `deathPosEquivKerQuot`, `deathImageEquivCokerQuot` — **Corollary 2.2 `(PHF.12)`**:
  `K_r/K_{r+1} ≅ L_r⁺ ≅ L_r⁻ ≅ C_r/C_{r+1}`.

## §3–§4: formation and properness (`PagewiseHodgeFormation`)

* `mem_kerFlag_iff`, `mem_cokerFlag_iff` — the stable sector is exactly the common orthogonal
  complement of the death layers;
* `pageCompression d r = d_r ∘ P_r⁺` with `ker_pageCompression = (L_r⁺)ᗮ` and
  `range_pageCompression = L_r⁻`;
* `pageResponseK d r = |d̂_r|` and `pageResponseC d r = |d̂_r*|` — literally the card's
  `(PHF.13)`–`(PHF.14)` polar blocks, via `absMap`; `norm_pageResponseK_apply`,
  `norm_pageResponseC_apply`, `ker_pageResponseK`, `ker_pageResponseC`,
  `range_pageResponseK_le`, `range_pageResponseC_le`;
* `formationK`, `formationC` — the assembled `𝒜` of `(PHF.15)`, block-diagonal across the two
  sides;
* `norm_sq_formationK`, `norm_sq_formationC` — **`(PHF.17)`**, pagewise energy splitting
  (through the reusable `norm_sq_sum_pairwise_orthogonal`);
* `ker_formationK = kerFlag d m`, `ker_formationC = cokerFlag d m` — **Theorem 3.1 `(PHF.16)`**;
* `starProjection_deathPos_sum`, `exists_uniform_deathGap`,
  `formationK_hasTransverseLowerBound`, `isClosed_range_formationK` — **Theorem 4.1 `(PHF.18)`**:
  the least page gap is a global lower bound on `E_∞^⊥`, hence closed range (using the corpus's
  `hasTransverseLowerBound_iff_isClosed_range`);
* `norm_formationK_of_mem_deathPos` and `not_isClosed_range_of_escape` — **`(PHF.19)`**, the
  converse: a unit escape sequence on successively later death layers along which the response
  tends to zero forbids closed range.

## §5–§6: selection

* `completedFormation A B` with `norm_sq_completedFormation`;
* `ker_completedFormation` — **`(PHF.22)`**: the completed kernel is the intersection of the two
  kernels, so injectivity of the completed formation is injectivity of the terminal response on
  the stable sector;
* `norm_sq_starProjection_add` and `completedFormation_lower_bound` — **`(PHF.23)`–`(PHF.24)`**:
  `‖𝒜_B x‖ ≥ min(γ, β)‖x‖`;
* `ker_factored_response` — **Theorem 5.2 `(PHF.25)`–`(PHF.26)`**: a response factored through
  the old formation is blind exactly where the old formation is, so adjoining it cannot shrink
  the common kernel;
* `bddAbove_norm_orbit_iff` — **Corollary 6.1 `(PHF.27)`–`(PHF.28)`**: bounded formation work
  along a dilation orbit `a > 1` forces the vector into the kernel.

## §7: functional-equation neutrality

* `map_orthogonal_of_isometryEquiv` — a linear isometry equivalence commutes with orthogonal
  complements;
* `kerFlag_map_of_intertwine`, `deathImage_map_of_intertwine`, `deathPos_map_of_intertwine` —
  **`(PHF.29)`–`(PHF.30)`**: a unitary intertwiner transports the whole flag and every death
  layer;
* `norm_intertwine` — the page gaps `γ_r` are preserved.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/OperatorAbsoluteValueBetween.lean
lake env lean GaloisForLFunctions/HTGeometry/PagewiseHodgeFlag.lean
lake env lean GaloisForLFunctions/HTGeometry/PagewiseHodgeFormation.lean
```

All three elaborate with no errors and no warnings.  `#print axioms` on all 92 public
declarations of the three modules reports only `propext`, `Classical.choice`, `Quot.sound`.
All three are imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`, which is imported
by `GaloisForLFunctions.HTGeometry`.

## Card Lean requirements (§10)

1. diagonal Hodge normal form — `ConstitutivePagewiseFormationSelection` plus the abstract
   `pageResponseK`/`pageResponseC` polar blocks;
2. exact kernel = stable coordinates — `ker_formationK`, `ker_formationC`;
3. least page/terminal gain lower bound — `formationK_hasTransverseLowerBound`,
   `completedFormation_lower_bound`;
4. vanishing of every factored response on the stable block — `ker_factored_response`;
5. separating terminal block gives injectivity — `ker_completedFormation`;
6. phase conjugacy preserves gains and selection — `diagMin_phase_mul` and the abstract
   `kerFlag_map_of_intertwine` / `norm_intertwine`.

The card's "may be formalized after" items — the abstract orthogonal-flag construction and the
countable closed-range equivalence — are now both certified.

## Still open (not a proved theorem)

Sharp boundary 7 of the card: no arithmetic history and no terminal response `B` are constructed.
The card states this as the remaining RH construction burden, not as a theorem.
