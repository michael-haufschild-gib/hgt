# Ramification anchor--defect incidence interchange and Bianchi law — formalized

- **ID:** `cfr-ramification-anchor-defect-incidence-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `ramification-anchor-defect-incidence-interchange-and-bianchi-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.AnchorDefectIncidence` | new |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Theorem 1.1 — the incidence current, card `(AI.1)`–`(AI.5)`:

1. `anchorSet`, `defectSet` — card `(AI.1)`.
2. `anchorSet_disjoint_defectSet` — anchors and defects are disjoint when `q ∣ M`.
3. `bipartiteCurrent` — the normalised complete bipartite current `(AI.3)`; `bipartiteCurrent_nonneg`
   and `bipartiteCurrent_eq_zero_of_empty` cover the convention `J = 0` on an empty defect set.
4. `sum_bipartiteCurrent` — total oriented mass one, hence edge `ℓ¹` norm one (the current is
   nonnegative).
5. `sum_sq_bipartiteCurrent` — the squared `ℓ²` norm `1/(|H||D|)`.
6. `edgeBoundary`, `edgeBoundary_bipartiteCurrent` — the boxed boundary formula `(AI.5)`:
   `∂J = u_D - u_H` on coloured vertices.
7. `defectSet_eq_empty_iff` — the boxed equivalence `(AI.4)`: the current vanishes exactly when
   every aperture exponent is a multiple of `q`, i.e. when the integer is a `q`-th power on the
   aperture.

Theorem 2.1 — the exact interchange defect, card `(AI.6)`–`(AI.12)`:

8. `defectSet_mul_eq_union`, `defectSet_disjoint_sdiff` — the boxed split `(AI.7)`
   `D_{sr} = O_s ⊔ L_{s,r}`.
9. `bipartiteCurrent_union` — the convex decomposition
   `J_{H,O⊔L} = (d/(d+ℓ)) J_{H,O} + (ℓ/(d+ℓ)) J_{H,L}`.
10. `interchange_defect` — the boxed formula `(AI.9)`:
    `Ω = (ℓ/(d+ℓ))(J_{H,L} - J_{H,O})`.
11. `sum_abs_interchange_defect` — the boxed `ℓ¹` norm `2ℓ/(d+ℓ)` of `(AI.10)`.
12. `sum_interchange_defect` — zero net edge mass.
13. `edgeBoundary_sub` together with items 6 and 10 gives the boxed boundary `(AI.12)`.

Corollary 2.2 — the unconditional nonzero witness, card `(AI.13)`/`(AI.14)`:

14. `factorization_three_primes` — the exponent vector of `p₀^a p₁^b p₂^c`.
15. `witness_layers` — for `N = p₀^{srm} p₁^s p₂` and `m, r, s ≥ 2` the anchor set is `{p₀}`, the
    outer layer is `{p₂}` and the latent-inner layer is `{p₁}`; combined with item 10 this is the
    boxed `Ω = ½([p₀,p₁] - [p₀,p₂]) ≠ 0`.

Theorem 3.1 — the exact Bianchi identity, card `(AI.15)`:

16. `interchange_bianchi` — for any transport that is additive and composes strictly
    (`T_t T_s = T_{ts}`), the boxed three-stage identity
    `Ω_{m;t,sr} + T_t Ω_{m;s,r} = Ω_{m;ts,r} + Ω_{rm;t,s}` holds; both sides expand to the same
    four-term expression.

Section 4 — ordered-flag strictification, card `(AI.16)`/`(AI.17)`:

17. `product_union` — the boxed rectangle split `(AI.16)`:
    `H × O ⊔ H × L = H × D_{sr}`.
18. `defectSet_mono`, `chain_dvd`, `failureLayer` — the ordered first-failure layers `(AI.17)`.
19. `failureLayer_disjoint` — the layers are pairwise disjoint.
20. `defectSet_eq_union_failureLayers` — their union with the base layer is the full
    product-defect set, so ordered flags compose strictly by refinement and concatenation.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/AnchorDefectIncidence.lean  # clean
#print axioms  ⇒  propext, Classical.choice, Quot.sound
```
