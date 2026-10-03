# W₃ coefficient anatomy and the low-coefficient cost law (2026-10-03)

## Computed
- The 8 most visible W₃ directions (`T = 160`, `N = 834`). Statistics:
  - multiplicativity correlation on coprime pairs;
  - ℓ² mass by n-range and by Ω(n);
  - residues mod 2, 3, 4;
  - correlation with d₃ and μ.
- The maximal low-n mass `max ‖e_{≤n0}‖²` over unit `e` with FE defect ≤ τ, from the SVD of the defect matrix, for d = 3 (`T_c = 80`; `N = 187, 369`) and d = 4 (`T_c = 60, 100`; `N` up to 2032).

## Results
- **Generic arithmetic:**
  - multiplicativity correlation ≈ 0;
  - Ω-mass equal to the base frequencies;
  - residues uniform within noise;
  - |corr| with d₃ and μ below 0.06.
- **Support:** all visible mass lies in `30 < n ≤ 300`.
- **Max low-n mass (d = 3, τ = 1e-8):** n≤2 ~1e-16; n≤5 ~1e-13; n≤10 ~1e-6; n≤20 0.14–0.38; n≤30 0.56–0.71.
- **Max low-n mass (d = 4, τ = 1e-8):** n≤5 ~1e-9–1e-13; n≤10 ~1e-3–1e-10; n≤20 0.02–0.38.

## Interpretation
- W elements are not arithmetic objects (no hidden Euler structure).
- The functional equation makes low coefficients super-exponentially expensive to change: a finite-horizon Hamburger law. It is the coefficient-space image of the onset height (~45) of W's visibility.
- Any element of `V_3` with moderate coefficients agrees with ζ³ for `n ≲ 10`. This is consistent with, and weaker than, the certified producer pinning, which applies even to unbounded coefficients.
- **Window dependence (d = 3, τ = 1e-8, mult 4).** At `T_c = 140` the low-n mass falls further (n≤10: 1.2e-13; n≤20: 2.9e-4).
  - The ℓ²-cost of nonzero low coefficients grows with the FE window. W elements with nonzero low coefficients exist only with non-square-summable coefficients (allowed: polynomial growth).
  - So the cost law depends on the norm; it is not an intrinsic horizon.
