# Helson coefficient-faithful Fredholm crossing response law — Lean certificate

- **ID:** `cmr-helson-coefficient-fredholm-crossing-response-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `helson-coefficient-fredholm-crossing-response-law.md` (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/SimpleEigenvalueAffineBranch.lean` — **new reusable
  infrastructure**: the first-order perturbation theorem for a simple isolated eigenvalue of a
  compact self-adjoint operator on a Hilbert space (namespace `HTGeometry`);
- `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/HelsonDivisorResponse.lean` —
  the divisor weight, the Helson entries, the divisor-convolution covector and the normalized
  Mellin layer;
- `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/HelsonFredholmWall.lean` — the
  trace-class realization, the eigenvalue response, the Fredholm wall and the crossing form.

All are imported by `GaloisForLFunctions.HTGeometry`.  The Schatten-one carrier is the corpus
module `HTGeometry/SchattenOneBanach.lean` (`SchattenOneOperator`, `rankOneSchattenOne`,
`norm_rankOneSchattenOne`, `schattenOneCoeCLM`), which is reused rather than rebuilt.

## New infrastructure

**`HTGeometry.IsSimpleEigenpair`** and **`HTGeometry.exists_eigenBranch`**.  For a compact
self-adjoint `A` on a complex Hilbert space with a simple nonzero eigenvalue `μ` and unit
eigenvector `u`, the affine family `A + tB` has a local eigenvalue branch through `μ` with

  `μ̇(0) = ⟪u, B u⟫`.

The proof is Riesz-projection-free.  Mathlib's Fredholm alternative
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`) applied to the restriction of `A` to `uᗮ`
makes `μ - A` invertible there; splitting `H = ℂu ⊕ uᗮ` turns the eigenvalue equation into a
contraction fixed-point problem for the `uᗮ`-component `w(t)`, with `‖w(t)‖ = O(|t|)`.  The
eigenvalue is then the *explicit* scalar `μ + t⟪u, B(u + w(t))⟫`, whose derivative at `0` follows
from continuity of `w` alone (`hasDerivAt_iff_tendsto_slope`).  Neither mathlib nor the corpus had
this theorem.

## Formal statement chain

### §2 — the Helson trace-class realization

1. `divisorWeight`, **`divisorWeight_eq_card_divisors`** — `(HFR.1)`: the divisor weight `d(n)` as
   the cardinality of the divisor antidiagonal, equal to the ordinary divisor count.
2. `HelsonSummable` — `(HFR.1)`: the space `ℓ¹_d`.
3. `helsonEntry`, **`helsonEntry_one_left`**, **`helsonEntry_conj_symm`**,
   **`sum_norm_helsonEntry_fibre`** — `(HFR.2)`, `(HFR.4)`, `(HFR.5)` at the level of entries.
4. `HelsonSpace`, `helsonBasis`, `norm_helsonBasis`, `inner_helsonBasis_left`,
   `inner_helsonBasis_right`, `helsonBasis_coe` — the chart `ℓ²` and its coordinate vectors.
5. `helsonBlockOp` — `(HFR.5)`: the divisor block as a finite sum of rank ones in the Schatten-one
   carrier; **`norm_helsonBlockOp_le`** bounds its trace norm by `d(n)|a_n|`.
6. `helsonOperator`, `summable_helsonBlockOp`, `helsonBlockCLM`, `helsonCLM` — `(HFR.2)`,
   `(HFR.5)`: the Helson operator as an absolutely trace-norm convergent sum of the blocks.
7. **`norm_helsonOperator_le`** — Theorem 2.1 (1), `(HFR.3)`: `‖K_a‖₁ ≤ ∑ d(n)|a_n|`.
8. **`isCompactOperator_helsonOperator`** — the realization is compact.
9. `coe_helsonOperator`, **`inner_helsonBlockOp_apply`**, `entryCLM`,
   **`inner_helsonOperator_apply`** — the quadratic form of the realization, atom by atom.
10. **`inner_helsonOperator_basis`** — Theorem 2.1 (2), `(HFR.4)`: `⟪e_j, K_a e_k⟫ = a_{jk}`; in
    particular `a_n = ⟪e_1, K_a e_n⟫`.
11. `sum_divisorsAntidiagonal_swap`, `isSelfAdjoint_helsonBlockOp`,
    **`isSelfAdjoint_helsonOperator`** — Theorem 2.1 (3): a real stream gives a self-adjoint
    realization.  Each block is self-adjoint by the swap symmetry of the divisor antidiagonal, and
    self-adjointness passes to the trace-norm limit because it is a closed condition.

### §3 — the divisor-convolution response

12. `divisorConv` — `(HFR.6)`: `W_u(n) = ∑_{jk=n} conj(u_j) u_k`.
13. `tsum_normSq_lpTwo`, `summable_normSq_lpTwo`, `sum_divisors_normSq_le`,
    **`norm_divisorConv_le`** — Lemma 3.1: `|W_u(n)| ≤ ‖u‖²`, by Cauchy–Schwarz over the divisor
    antidiagonal and the divisor involution.
14. **`divisorConv_least_sq`** — `W_u(m²) = |u_m|²` for the least active index `m`: every other
    factorization of `m²` uses an index below `m`.
15. **`inner_helsonCLM_self`** — `(HFR.7)`: `⟪u, K_h u⟫ = ∑ h_n W_u(n)`.
16. `helsonBlockOp_add`, `helsonBlockOp_smul`, `helsonSummable_smul`, `helsonOperator_add`,
    `helsonOperator_smul`, **`helsonCLM_affine`** — `K_{a+th} = K_a + t K_h`.
17. **`helson_eigenBranch`** — Theorem 3.2, `(HFR.7)`: at a simple nonzero eigenvalue of `K_a` the
    eigenvalue branch of `K_{a+th}` is differentiable at `0` with derivative `∑ h_n W_u(n)`.  The
    series converges absolutely by Lemma 3.1 and `∑|h_n| ≤ ∑ d(n)|h_n|`.

### §4 — the Fredholm wall and crossing orientation

18. `inner_helsonBasis_zero_helsonCLM`, `eigenvector_coord_zero` — the zeroth chart coordinate is
    annihilated, so every eigenvector for a nonzero eigenvalue is supported in positive indices.
19. **`helson_wall_iff`** — Theorem 4.1 (2): `τ ≠ 0` lies in the spectrum of `K_a` exactly when it
    is an eigenvalue.  This is the Fredholm alternative for the compact `K_a`, and it is the
    content of `Δ_τ(a) = 0 ↔ τ ∈ spec K_a`.
20. **`helson_index_zero`** — Theorem 4.1 (1): `τ - K_a` is Fredholm of index zero — injectivity on
    the chart already forces `τ` into the resolvent set.
21. `crossingForm`, **`crossingForm_eq_neg_inner`** — `(HFR.9)`, `(HFR.9a)`:
    `Γ_{a,τ}(h) = -∑ h_n W_u(n) = -⟪u, K_h u⟫`.
22. **`hasDerivAt_wallGap`** — Theorem 4.1 (3): the wall gap `Ω(t) = τ - μ(t)` has derivative
    exactly `Γ_{a,τ}(h)`.  A path with velocity `h` is therefore transverse exactly when
    `Γ_{a,τ}(h) ≠ 0`, and its oriented crossing sign is the sign of `Γ_{a,τ}(h)`.
23. `norm_crossing_term_le`, `summable_norm_crossing`, **`norm_crossingForm_le`** —
    Theorem 4.1 (4): `|Γ_{a,τ}(h)| ≤ ‖h‖_{1,d}`, so the covector is continuous.
24. **`exists_crossingForm_ne_zero`** — Theorem 4.1 (4): the covector is nonzero — the atom at
    `m²`, for `m` the least active index of the eigenvector, detects it.

### §5 — normalized Mellin coefficients

25. `mellinWeightedNorm`, `mellinMass`, **`mellinWeightedNorm_eq`** — `(HFR.10a)`: the isometric
    identification `X_σ ≅ ℓ¹_d` by `x ↦ (x_n n^{-σ})`.
26. **`norm_mellinMass_le`** — `(HFR.10a)`: `|Z(x)| ≤ ‖x‖_{X_σ}`, so the total mass is continuous
    and `{Z > 0}` is open.
27. `mellinNormalized`, **`mellinNormalized_smul`** — `(HFR.10)` and Corollary 5.1's projective
    invariance `p(λc) = p(c)`.
28. `mellinExchangeSeed`, **`hasDerivAt_mellinNormalized`** — `(HFR.11)`: the exchange tangent is
    the coordinatewise derivative of the normalization along an additive-mass direction.
29. **`projective_wall_response`** — Corollary 5.1, `(HFR.12)`: the wall gap responds to a source
    intervention through the normalized exchange tangent,
    `DΩ_c[h] = -∑ Dp_c[h]_n W_u(n)`.
30. **`mellinExchangeSeed_self`** — Corollary 5.1: the radial direction lies in the kernel of the
    exchange tangent, hence of the projective response.

### §6 — exact limitations and countermodels

31. **`helson_block_not_posSemidef`** — countermodel 1: coefficient positivity does not imply
    operator positivity; the stream supported at `2` gives the reflection block `[[0,1],[1,0]]`.
32. **`eigenvalue_mem_spectrum`** — countermodel 2: any eigenvalue manufactures a wall, so the
    threshold can be fitted.
33. **`divisorConv_ne_of_ne`** — countermodel 3: distinct eigenlines give distinct response
    covectors, so the eigenbranch can be fitted.
34. **`not_helsonSummable_one`** — countermodel 4: strong summability is a real restriction; the
    constant stream has coefficient-faithful entries but is not divisor summable.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/SimpleEigenvalueAffineBranch.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/HelsonDivisorResponse.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/HelsonFredholmWall.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.HelsonFredholmWall
```

Green with no warnings.  `#print axioms` on `HTGeometry.exists_eigenBranch`,
`norm_helsonBlockOp_le`, `norm_helsonOperator_le`, `isCompactOperator_helsonOperator`,
`inner_helsonBlockOp_apply`, `inner_helsonOperator_apply`, `inner_helsonOperator_basis`,
`isSelfAdjoint_helsonOperator`, `inner_helsonCLM_self`, `helsonCLM_affine`, `helson_eigenBranch`,
`helson_wall_iff`, `helson_index_zero`, `crossingForm_eq_neg_inner`, `hasDerivAt_wallGap`,
`norm_crossingForm_le`, `exists_crossingForm_ne_zero`, `eigenvalue_mem_spectrum`,
`not_helsonSummable_one`, `divisorConv_ne_of_ne`, `projective_wall_response` and
`mellinExchangeSeed_self` — together with the eleven declarations of
`HelsonDivisorResponse.lean` — reports only `propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

The chart is `ℓ²(ℕ)` rather than `ℓ²(ℕ_{≥1})`.  The extra coordinate is inert: every divisor
antidiagonal consists of positive pairs, so the zeroth row and column of `K_a` vanish
(`inner_helsonBasis_zero_helsonCLM`), and every eigenvector for a nonzero eigenvalue has vanishing
zeroth coordinate (`eigenvector_coord_zero`).  This is proved, not assumed, and it is what makes
the least-active-index argument of Theorem 4.1 (4) available.

**The Fredholm determinant `det_F(I - τ⁻¹K_a)` is not constructed.**  Mathlib has no Fredholm
determinant, and the card's own §9 flags it as needing a separate analytic plan.  Its role in
Theorem 4.1 is to detect the wall, and that role is formalized in the Fredholm-alternative form
`helson_wall_iff`: for `τ ≠ 0`, `τ ∈ spec K_a` exactly when `τ` is an eigenvalue, which is exactly
the condition `Δ_τ(a) = 0` names.  Items 1, 3 and 4 of Theorem 4.1 never use the determinant
itself, only this condition and the eigenvalue branch, and they are formalized in full.

Theorem 4.1 (4)'s last sentence packages the crossing datum as a `C¹` codimension-one hypersurface
through the Banach implicit-function theorem.  What is formalized is the substance that packaging
records: the wall gap is differentiable along every admitted direction with differential the
continuous, nonzero covector `Γ_{a,τ}` (`hasDerivAt_wallGap`, `norm_crossingForm_le`,
`exists_crossingForm_ne_zero`), so a path with velocity `h` is transverse exactly when
`Γ_{a,τ}(h) ≠ 0` and its oriented crossing sign is `sign Γ_{a,τ}(h)`.  Assembling those into a
hypersurface chart additionally needs Fréchet `C¹`-dependence of the eigenvalue on the whole
`ℓ¹_d`-neighbourhood, which the one-parameter perturbation theorem does not by itself supply.

§7's route-independent consequence and §8's literature boundary are programme statements and claim
no further theorem; §6's items 5 and 6 are explicit deferrals to the companion rank law and to an
open local-Stokes comparison.
