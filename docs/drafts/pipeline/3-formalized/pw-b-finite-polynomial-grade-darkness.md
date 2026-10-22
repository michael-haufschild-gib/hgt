# PW-B finite-polynomial grade darkness

- **ID:** PW-B-P1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · PW-B
- **Statement:** Every fixed degree bound `d` admits an explicit nonzero symmetric finite-support rank-one PSD PW grade kernel annihilating all degree-`d` polynomial reporters; order `2d+1` is sharp.

## Goal

Determine whether bounded polynomial nonlinearization repairs the literal PW-B cross-grade observability defect.

## Gates

- [x] 0 → 1 in-progress: source-pure exact PW grade law and corpus forward-difference mechanism
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: Lean module, targeted build green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone paper package

## Theorem package

Let `n = 2d+1` and `w_k = (-1)^(n-k) * choose n k`. The literal imaginary PW Borel holonomy is the evaluation of a real polynomial in grade of degree at most two. Therefore, for every `P : ℝ[X]` with `natDegree P ≤ d`,

`sum_{k=0}^n w_k P(Im H_s(k)) = 0`

for every `s : ℂ`. The matrix `K_ij = w_i w_j` has finite support, is symmetric and nonzero (`K_nn = 1`), and every finite principal quadratic form is a square. It annihilates every separable degree-bounded energy and every nested bivariate polynomial reporter whose outer-variable degree is at most `d`.

The boundary is exact. At order `2d`, the monomial reporter satisfies

`sum_{k=0}^{2d} (-1)^(2d-k) choose(2d,k) Im(H_s(k))^d = (2d)! (4 wall(s))^d`.

At `s = 1/4 + i`, `wall(s)=1`, so this value is nonzero. Hence `2d+1` is the first universally dark alternating-binomial order.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekFinitePolynomialGradeNoGo`
- Main theorems:
  - `schwarzschildParikhWilczekPolynomialGradeDarkWeight_annihilates`
  - `schwarzschildParikhWilczekPolynomialGradeDarkMatrix_finiteQuadraticForm_nonneg`
  - `schwarzschildParikhWilczekBivariatePolynomialCrossGradeEnergy_zero`
  - `schwarzschildParikhWilczekPolynomialGradeDarkOrder_sharp`
  - `schwarzschildParikhWilczekPolynomialGradeDarkOrder_minimal_witness`
- Verification: direct `lake env lean` PASS; targeted `lake build` PASS.
- Axioms: only `[propext, Classical.choice, Quot.sound]` on all main theorems.
- Umbrella: imported by `GaloisForLFunctions.RHTower`.

## Novelty audit — 2026-08-28

Corpus search found the exact quadratic PW grade law, the earlier affine three-moment dark sector, and a reusable forward-difference theorem, but no finite-polynomial PW obstruction or exact minimal-order theorem. External searches checked:

- Parikh--Wilczek, *Hawking Radiation as Tunneling* (2000), `https://arxiv.org/abs/hep-th/9907001`.
- Kuwakino--Wen, *n-partite information in Hawking radiation* (2015), `https://arxiv.org/abs/1412.0802`.
- Roy--Rahat, *Tunneling across the quantum horizon does not resolve the information paradox* (2014), `https://arxiv.org/abs/1406.3635`.
- Ming, *Multipartite Correlations in Parikh--Wilczek Non-Thermal Spectrum* (2024), `https://doi.org/10.3390/e26080680`.

These sources study nonthermality and low-/multipartite correlations. Searches for `finite difference`, `alternating binomial`, bounded polynomial grade reporters, and exact dark order found no matching theorem. Novelty claim is therefore internal-corpus exact and externally search-audited, not an assertion that absence from all literature is decidable.

## Log

- 2026-08-28 — `[PROVED HERE]` Derived degree-doubling obstruction, nonzero PSD outer-product kernel, full bivariate darkness, and exact sharp order.
- 2026-08-28 — Formalized, targeted build passed, standard-axiom audit passed, umbrella wired.
