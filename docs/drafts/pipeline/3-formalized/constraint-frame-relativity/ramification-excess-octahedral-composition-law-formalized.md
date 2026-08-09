# Ramification marked split-defect composition and inherited-observer blindness — formalized

- **ID:** `cfr-ramification-excess-octahedral-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `ramification-excess-octahedral-composition-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellExcessSupport` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellSplitDefectStreams` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellExcessModules` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellRamificationPower` | shared |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellExcessDirichlet` | shared |

All wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Theorem 1.1 — inherited/excess reconstruction, card `(RE.3a)`–`(RE.7)`:

1. `shellSupport`, `powerImageSupport`, `excessSupport` — the three supports; `excessSupport` is
   literally card `(RE.3a)`.
2. `shellSupport_mul_eq_union`, `powerImageSupport_disjoint_excessSupport`,
   `powerImageSupport_eq_image` — the disjoint partition `A_{rm} = P_r(A_m) ⊔ X_{m,r}`.
3. `shellSplitEquiv` — the resulting bijection of index types.
4. `shellCoeffEquiv` — the boxed isomorphism `(R,Q) : V_{rm} ≅ V_m ⊕ E_{m,r}` of card `(RE.7)`.
5. `shellJ`, `shellR`, `shellQ`, `shellJ_single`, `shellR_apply` — the three maps, with
   `J e_k = e_{k^r}` and `(R y)(k) = y(k^r)`.
6. `shellR_comp_shellJ`, `shellJ_injective`, `shellQ_surjective`,
   `range_shellJ_eq_ker_shellQ` — the split short exact sequence `(RE.5)`/`(RE.6)`.
7. `excess_witness` (shared module) — for `r ≥ 2` the excess is nonzero, witnessed by `2^{rm}·3`.

Theorem 2.1 — canonical excess partition, card `(RE.8)`–`(RE.11)`:

8. `isRPow_of_isRPow_mul`, `isRPow_mul_iff_of_pow` — the two composition facts for perfect powers.
9. `excessSupport_mul_eq_union`, `excessSupport_disjoint_image` — the boxed partition `(RE.8)`.
10. `excessSplitEquiv`, `excessCoeffEquiv` — the boxed split sequence `(RE.9)`/`(RE.10)`.
11. `shellIncl_comp_coe`, `shellR_comp_apply` — card `(RE.11)`: the composed retraction returns the
    unique `sr`-th root, and zero otherwise.

Theorem 2.2 — bounded-stream split-defect functor, card `(RE.11a)`–`(RE.11j)`:

12. `rroot`, `pow_rroot`, `rroot_pow` — the `r`-th root partial inverse.
13. `extendPow`, `restrictPow` — the operators `V_r`, `R_r` of `(RE.11a)`.
14. `restrictPow_extendPow` (`R_r V_r = 1`), `extendPow_extendPow` (`V_s V_r = V_{sr}`),
    `restrictPow_restrictPow` (`R_r R_s = R_{sr}`), `extendPow_add`, `extendPow_sub`.
15. `shellStream`, `shellDefect`, `shellDefect_eq_excessStream` — the distinguished kernel point
    `c_{m,r} = a_{rm} - V_r a_m` of `(RE.11d)`, identified with the excess stream.
16. `restrictPow_shellDefect` — `c_{m,r} ∈ K_r`.
17. `shellDefect_cocycle` — the boxed composition law `(RE.11e)`.
18. `ker_split` — the canonical splitting `(RE.11f)`.
19. `shellTransport`, `shellTransport_shellStream`, `shellTransport_comp` — the affine transport
    `(RE.11i)` and its strict functoriality `(RE.11g)`/`(RE.11h)`.
20. `shellTransport_conjugate` — the hostile classification `(RE.11j)`: depth-dependent translation
    conjugates the affine transport to the linear `V_r`, so the cocycle is a coboundary.

Corollary 3.1 — crossed analytic cocycle, card `(RE.12)`/`(RE.13)`:

21. `lSeries_extendPow` — `∑ (V_s f)(N) N^{-z} = ∑ f(k) k^{-sz}`.
22. `norm_extendPow_le`, `norm_excessStream_le_one`, `lSeriesSummable_extendPow_excessStream` —
    the absolute convergence used in the reindexing.
23. `lSeries_shellDefect_cocycle` — the boxed identity
    `C_{m,sr}(z) = C_{m,r}(sz) + C_{rm,s}(z)` on `re z > 1`.

Theorem 4.1 — inherited-observer blindness, card `(RE.14)`–`(RE.16a)`:

24. `powerDiagonal_factors` — card `(RE.15)`: the power-diagonal coordinate `k^{rm}` is the
    `R_r`-image of the lower coordinate `k^m`.
25. `powerDiagonal_blind` — card `(RE.16)`: a stream supported off the `r`-th powers is invisible.
26. `shellDefect_isRPow_zero`, `shellDefect_witness` — card `(RE.16a)`: the single coordinate
    `2^{rm}·3` distinguishes `a_{rm}` from `V_r a_m`.
27. `excessSupport_not_prime_pow` — two prime species are necessary: every element of the excess
    support has at least two distinct prime factors.
28. `factors_through_shellR_iff` — the universal criterion of the final paragraph of Section 4:
    a linear observer factors through `R_{m,r}` exactly when it annihilates the excess.

Section 5 — route-independent exactness, card `(RE.17)`:

29. `quotient_cofiber_equiv` — `(C/A)/(B/A) ≅ C/B` for submodules `A ≤ B ≤ C`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/ShellExcessSupport.lean       # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/ShellSplitDefectStreams.lean  # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/ShellExcessModules.lean       # clean
#print axioms  ⇒  propext, Classical.choice, Quot.sound
```
