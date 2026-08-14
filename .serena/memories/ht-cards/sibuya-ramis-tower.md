# Card 3 (irrational-power canonical products) — the Sibuya–Ramis tower

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/ht/irrational-power-canonical-products-hypertranscendental-by-gevrey-slope-rigidity.md`

**Everything on this card is formal EXCEPT one construction: the Newton–Ramis factorization
`L = M ∘ N` at an irrational cut.**

## Formal (all wired, all axiom-clean `[propext, Classical.choice, Quot.sound]`)

- `(1)`, `(8)`–`(12)`: exact Gevrey order `s` of the zeta tail, unconditional for irrational `s>0`.
- `(4)`–`(6)`: Barnes/Mellin derivative-compatible expansion, at EVERY genus.
- §4 DA transfer; `(14) ⟹ (15)`; §5 Newton-slope rationality.
- Linear Maillet (crude + Newton form); the Maillet order is rational.
- **Nonlinear Maillet, UNCONDITIONAL** — `NonlinearMailletUnconditional.exists_isGevreySeries_of_annihilator`:
  every formal power series annihilated by a nonzero analytic differential polynomial is Gevrey of
  a finite ℕ order.  No nondegeneracy hypothesis.
- **The operator ring and the irrational leading vertex** (new layer):
  `EulerShiftOperatorAlgebra`, `NewtonIrrationalLevelVertex`, `NewtonLevelComposition`,
  `NewtonIrrationalPositiveVertex`.

Module chain (all wired into `HTGeometry.lean`):
`GevreyBanachNorm`, `GevreyWeightedNorm`, `MvPolynomialTaylorFamily`, `GevreyJetMonomial`,
`NonlinearMailletAux`, `NonlinearMailletShift`, `NonlinearMailletGevrey` (thin `v = 0` corollary),
`NonlinearMailletUnconditional`, `EulerShiftOperatorAlgebra`, `NewtonIrrationalLevelVertex`,
`NewtonLevelComposition`, `NewtonIrrationalPositiveVertex`.

## Key mechanisms (do not re-derive)

- `GevreyWeightBound w C A r F` := `‖f_n‖(n+1)^w ≤ C A^n (n!)^r`, **integral** `r`.  Submultiplicative
  at every weight `a ≥ 2`; `θ` costs exactly ONE unit of weight; a product of two series divisible
  by `t^M` **gains** `M·r` units (`GevreyWeightBound.mul_of_dvd`).
- The Taylor family `defect = ∑_{|α|≥2} (coeff in base point) L^α` must be produced along
  `MvPolynomial.as_sum` (monomials), NOT `MvPolynomial.induction_on`.
- At a positive leading shift `v`: choose **`A` first, then `ε := c/(3(K+1)(c+1)A^v)`**.
- Nondegeneracy discharge: minimal-total-degree annihilator, `totalDegree_pderiv_lt`,
  `eq_C_of_forall_pderiv_eq_zero`, `coeff_aeval_eulerJetVector_truncPowerSeries_eq`, `N := m + 2v`.
- `shiftOp Φ` / `shiftComp Ψ Φ` present the operator ring; `shiftOp_shiftComp` is composition.
  `weightedLevel r Φ μ = deg Φ_μ − rμ`; injective for irrational `r`; leading vertices are additive
  under composition (`coeff_shiftComp_leading`).
- `newtonBoundedBy_iff_weightedLevel_le`: the Newton condition at level `r` is `λ_r(μ) ≤ λ_r(0)`.
- `exists_positive_weightedLevel_of_irrational_exactOrder`: an irrational exact order forces the
  leading vertex to a POSITIVE shift (else the least Newton level is rational `< s` and Maillet
  there contradicts exactness).  This halves the remaining problem.

## Ruled out (do not retry)

A scalar-recursion proof of the sharp half.  With `u_n = f_n/(A^n(n!)^s)` bounded, irrationality
makes the dominant shift `μ*` unique and gives `|u_{n−μ*}| ≲ n^{−η}·neighbours`, but solving the
recursion for `f_{n−μ*}` involves `f` at indices ABOVE `n−μ*`, so it is not an induction; the a
priori order-`s` bound is too lossy there by `(n!)^δ`, and sup-based bootstraps only give
`e^{−η(log n)^2}`, far short of `(n!)^{−δ}`.

## The one remaining construction

`L = M ∘ N` at an irrational cut `s`, `N` Newton-bounded at level `s`, every slope of `M` above `s`.
Given it: `U := N F ∈ E_s` solves `M U = G` convergent, so by induction on the number of slopes
`gev(U) = 0`; then `N F` convergent and Maillet at the least Newton level of `N` (rational `< s`)
makes `F` Gevrey below its exact order — contradiction.
The construction is a Hensel-type recursion in the shift with a majorant convergence proof, inside
`shiftComp`; the ring, its `IsBoundedShiftFamily` estimates, and the multiplicativity of leading
vertices it must respect are already formal.
