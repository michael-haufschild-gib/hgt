# Card 3 (irrational-power canonical products) — the Sibuya–Ramis tower

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/ht/irrational-power-canonical-products-hypertranscendental-by-gevrey-slope-rigidity.md`

**Everything on this card is formal EXCEPT the sharp half of Sibuya–Ramis.**

## Formal (all wired, all axiom-clean `[propext, Classical.choice, Quot.sound]`)

- `(1)`, `(8)`–`(12)`: exact Gevrey order `s` of the zeta tail, unconditional for irrational `s>0`.
- `(4)`–`(6)`: Barnes/Mellin derivative-compatible expansion, at EVERY genus.
- §4 DA transfer; `(14) ⟹ (15)` asymptotic-to-formal; §5 Newton-slope rationality.
- Linear Maillet (crude + Newton form), rationality of the Maillet order.
- Linearization at a truncation, quadratic defect, its locality.
- **Nonlinear Maillet, UNCONDITIONAL** —
  `HTGeometry/NonlinearMailletUnconditional.lean`, `exists_isGevreySeries_of_annihilator`:
  every formal power series annihilated by a nonzero analytic differential polynomial is Gevrey of
  a finite ℕ order.  No nondegeneracy hypothesis.

Module chain built for it (all new, all wired into `HTGeometry.lean`):
`GevreyBanachNorm`, `GevreyWeightedNorm`, `MvPolynomialTaylorFamily`, `GevreyJetMonomial`,
`NonlinearMailletAux`, `NonlinearMailletShift` (general leading shift `v`),
`NonlinearMailletGevrey` (thin `v = 0` corollary), `NonlinearMailletUnconditional`.

Mechanisms, so they are not re-derived:
- `GevreyWeightBound w C A r F` := `‖f_n‖(n+1)^w ≤ C A^n (n!)^r`, **integral** `r` (natural powers,
  no rpow).  Submultiplicative at every weight `a ≥ 2` with constant `2^{a+2}`.
- `θ` costs exactly ONE unit of weight (`GevreyWeightBound.formalEulerOp`).
- **The gain**: a product of two series both divisible by `t^M` gains `M·r` units of weight
  (`GevreyWeightBound.mul_of_dvd`), from `i!j! ≤ M!(n−M)!` and `(n−M+1)^M (n−M)! ≤ n!`.
  This pays for the `m` units the jets cost; hence the hypothesis `m + 2v ≤ N`.
- The Taylor family `defect = ∑_{|α|≥2} (coeff in the base point) L^α` must be produced by the
  induction along `MvPolynomial.as_sum` (monomials), NOT `MvPolynomial.induction_on`: the
  hypothesis "all coefficients lie in the subsemiring `R₀`" is inherited by monomials but not by
  the summands of an arbitrary sum decomposition.
- Order of choices at shift `v > 0`: **`A` first, then `ε := c/(3(K+1)(c+1)A^v)`** — the defect
  constant `K` is `A`-independent, and every constraint on `A` is then free of `ε`.
- Nondegeneracy discharge: minimal-total-degree annihilator + `totalDegree_pderiv_lt` +
  `eq_C_of_forall_pderiv_eq_zero`; then `v` = order of vanishing of the linearization along `F`,
  `N := m + 2v`, and `coeff_aeval_eulerJetVector_truncPowerSeries_eq` transports the shift
  polynomials from the solution to the truncation up to level `N`.

## The one open item: the sharp half of Sibuya–Ramis

`gev(F) ∈ {0} ∪ {slope ratios}`, not merely `gev(F) ≤ r₀`.  An upper bound alone is compatible with
an irrational exact order, so this is unavoidable for the card.

**A scalar-recursion proof was attempted and does NOT close** (record so it is not retried):
with `u_n = f_n/(A^n(n!)^s)` bounded, irrationality of `s` makes the exponents
`e_μ = deg Φ_μ − deg Φ_0 − sμ` pairwise distinct, so the dominant shift `μ*` is UNIQUE and
`|u_{n−μ*}| ≲ n^{−e*}(|u_n| + n^{−η}·neighbours)`.  But solving the recursion for `f_{n−μ*}`
involves `f` at indices ABOVE `n−μ*` (the shifts `μ < μ*`), so it is not an induction; bounding
those by the a priori order-`s` Gevrey bound is too lossy by `(n!)^δ`.  Sup-based bootstraps only
give quasi-polynomial decay `e^{−η(log n)^2}`, far short of `(n!)^{−δ}`.

**Remaining construction: the Newton–Ramis factorization `L = M ∘ N` in `ℂ{t}[θ]`**, splitting the
slopes at a cut, plus induction on the number of slopes.  Presentation to use:
`L = ∑_μ t^μ Φ_μ(θ)` with `(t^a Ψ(θ))(t^b Φ(θ)) = t^{a+b} Ψ(θ+b) Φ(θ)`; the factorization is then a
Hensel-type recursion in `μ` with a majorant convergence proof.
