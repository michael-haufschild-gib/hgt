# Schur corner ratio and order-k off-line dominance for the reciprocal slice

- **ID:** WD-SCR-20261010
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** WD loop `1-in-progress/wd-goal-loop-2026-10-09.md`, rows 17b–18
- **Statement:** For x₁ ≥ x₂ ≥ … ≥ x_N ≥ 0 and every skew shape λ/μ and r ≥ 1:
  `r · s_{λ/μ}(x) ≥ x_r · Σ_{i ≤ r} s_{(λ − e_i)/μ}(x)` (with x_r = 0 for r > N, and invalid shapes
  contributing 0). In particular `s_{(λ−e_r)/μ}(x) ≤ (r/x_r) s_{λ/μ}(x)`.

## Goal
Order-k version of the reciprocal off-line dominance law: reciprocal TP_k of the slice at height t
holds when the off-line zeros are sparse relative to the k-th nearest critical zero. In Toeplitz
form, a column decrement of a minor of a geometric-product sequence costs at most `r/x_r`. This is
the input missing for order-k dominance (row 18 of the loop).

## Toeplitz form
For `a` = coefficients of `∏_s 1/(1 − x_s u)`, a minor `M(i, j) = det(a_{j_c − i_r})` (i, j strictly
increasing, `m` columns), and `1 ≤ r ≤ m`:
`r · M(i, j) ≥ x_r · Σ_{c ≥ m − r, j_c ≥ 1} M(i, j − e_c)`.
Column `c` corresponds to row `m − c` of λ.

## Proof (complete)
**Branching.** `M_{x ∪ {y}}(i, j) = Σ_{l ∈ Int(j)} y^{|j| − |l|} M_x(i, l)`, where
`Int(j) = {l : l_c ≤ j_c, j_{c−1} < l_c}`. Proof: write `b = a ∗ geo(y)`, so
`b_n = a_n + y b_{n−1}`, and expand the columns from last to first. Column c of b at j_c equals
`Σ_{t < j_c − j_{c−1}} y^t a(j_c − t) + y^{j_c − j_{c−1}} b(j_{c−1})`; the last term repeats column
c−1, which is still a b-column, so it vanishes in the determinant.

**Pairs.** RHS terms are pairs `(c, κ)` with `c ≥ m − r` and `κ ∈ Int(j − e_c)`, weight
`y^{|j| − 1 − |κ|} M_{x'}(i, κ)`.
- *Good:* `κ + e_c ∈ Int(j)`. Map to the slot `(ν = κ + e_c, label c)`.
- *Bad:* `c + 1 < m` and `κ_{c+1} = j_c`. Map to `(ν = κ + e_{c+1}, label c+1)`, and
  `κ + e_{c+1} ∈ Int(j)`.
- These are the only cases.
- The map is injective. A good pair at c' and a bad pair at c'−1 with the same κ would need both
  `κ_{c'} > j_{c'−1}` and `κ_{c'} = j_{c'−1}`.

**Induction on N (number of variables).**
- `r > N`: `x_r = 0`, and minors are ≥ 0 (PF∞).
- `N > r`: peel the smallest variable y. Charge each pair to its slot and apply (S_r) for ν in the
  remaining N−1 variables, where x_r is unchanged.
- `N = r`: peel the largest variable x₁.
  - Pairs with `c > m − r`, and bad pairs with `c = m − r`, have labels in `[m−r+1, m−1]`. These
    are covered by (S_{r−1}) in the other r−1 variables, whose (r−1)-th largest is x_r.
  - Good pairs with `c = m − r` are charged to the slot `l = κ` (κ ∈ Int(j)), at cost
    `x_r/x₁ ≤ 1`, at most once per κ.
  - Each slot therefore receives at most `(r − 1) + 1 = r` times its LHS term.

Equality cases: x = (1^r) with λ = (1^r), (2,1,1), (2,2,1).

## Consequences
1. Iterated decrements: for `l ≤ j` coordinatewise with `|j − l| = d` and m ≤ k,
   `M(i, l) ≤ (k/x_k)^d M(i, j)`.
2. Order-k off-line dominance: if the off-line spectral masses `Σ_off |w|` (w = (z − t)^{−2}) are at
   most `η_k x_k(t)`, then reciprocal TP_k holds at t. Here x_k(t) = (k-th critical distance)^{−2}
   and η_k depends on k only. Proof: Cauchy–Binet `p[i,j] = Σ_{l ≤ j} a[i,l] b[l,j]` with
   `|b[l,j]| ≤ m!(2W)^{|j−l|}`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: paper proof above
- [x] 2 → 3  formalized (corner ratio): `HTGeometry.cornerRatio_geomProdSeq`, `cornerRatio_single`; branching `toeplitzMinor_cauchyConv_geometric`. Dominance law (consequence 2) formalized: `RHTower.pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_sparse` (η_k = 1/(25k³)), with the perturbation law `HTGeometry.toeplitzMinor_cauchyConv_ge_of_perturbation`.

## Log
- 2026-10-10 — created; paper proof by double induction with the good/bad slot injection.
- 2026-10-10 — corner ratio formalized (`ToeplitzGeometricBranching`, `SchurCornerRatio`), standard axioms.
- 2026-10-10 — perturbation law and Ξ order-k off-line dominance formalized (`ToeplitzPerturbationCornerRatio`, `XiReciprocalSliceOrderKDominance`).
- 2026-10-10 — near-double laws: reciprocal slice PF_k with displacement weight δ²/|z−t|⁴ (`XiReciprocalSliceNearDoubleDominance`), and direct slice c_{2j}(t) > 0 from D²Σ_off δ²/|z−t|⁴ ≤ 1/(3j) via the elementary corner ratio (`XiSliceCoeffNearDoublePositivity`, `ElementaryProductPairPerturbation`).
- 2026-10-10 — moved to 3-formalized. Follow-ups: cone + near-double exposed law (`xiSliceCoeff_re_pos_of_exposed_nearDouble`) and the per-zero obstruction (`XiSliceExposedShadowingObstruction`).
