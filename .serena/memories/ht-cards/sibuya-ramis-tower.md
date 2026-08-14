# Card 3 (irrational-power canonical products) — the Sibuya–Ramis tower

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/ht/irrational-power-canonical-products-hypertranscendental-by-gevrey-slope-rigidity.md`

Everything on this card is formal EXCEPT the last two rows below.

## Formal (all wired, all axiom-clean)

- `(1)`, `(8)`–`(12)`: exact Gevrey order `s` of the zeta tail, unconditional for irrational `s>0`.
- `(4)`–`(6)`: Barnes/Mellin derivative-compatible expansion, at EVERY genus.
- §4 DA transfer; `(14) ⟹ (15)` asymptotic-to-formal; §5 Newton-slope rationality.
- Linear Maillet (crude + Newton form), rationality of the Maillet order.
- Linearization at a truncation, quadratic defect, its locality.
- **Nonlinear Maillet** — `HTGeometry/NonlinearMailletGevrey.lean`,
  `exists_isGevreySeries_of_isFormalEulerADESolution`: a formal solution of an analytic ADE whose
  linearization along `trunc_N F` has `Φ_0 ≠ 0`, and with `m ≤ N+1`, is Gevrey of a finite ℕ order.

Supporting modules built for it (all new, all wired):
`GevreyBanachNorm`, `GevreyWeightedNorm`, `MvPolynomialTaylorFamily`, `GevreyJetMonomial`,
`NonlinearMailletAux`.

Key mechanisms, so they are not re-derived:
- `GevreyWeightBound w C A r F` := `‖f_n‖(n+1)^w ≤ C A^n (n!)^r`, **integral** `r` (natural powers,
  no rpow).  Submultiplicative at every weight `a ≥ 2` with constant `2^{a+2}`.
- `θ` costs exactly ONE unit of weight (`GevreyWeightBound.eulerOp`).
- **The gain**: a product of two series both divisible by `t^M` gains `M·r` units of weight
  (`GevreyWeightBound.mul_of_dvd`), because `i!j! ≤ M!(n−M)!` and `(n−M+1)^M (n−M)! ≤ n!`.
  This is what pays for the `m` units the jets cost; hence the hypothesis `m ≤ N+1`.
- The Taylor family `defect = ∑_{|α|≥2} (coeff in the base point) L^α` must be produced by the
  induction along `MvPolynomial.as_sum` (monomials), NOT `MvPolynomial.induction_on`: the
  hypothesis "all coefficients lie in the subsemiring `R₀`" is inherited by monomials but not by
  the summands of an arbitrary sum decomposition.
- Order of choices in the main proof: `ε` first (defect constant is `A`-independent), `A` second.

## Open — exactly two items

### 1. Discharge the nondegeneracy hypothesis `Φ_0 ≠ 0`
Route: choose `P` minimal (order, then degree) among nonzero annihilators, so some
`aeval (jets F) (∂_j P) ≠ 0`; let `v` be the common vanishing order of the linearization along `F`;
for `N ≥ v` the linearization at `trunc_N F` has the same `v`.  Then `L = t^v L'` and the equation
divides by `t^v`.  The cost is `A^v` in the defect estimate; it is repaid by the vanishing order
`N+1−v` of the value at the truncation, and the two constraints on `(ε, A)` are compatible exactly
when `N + 1 > 2v`.  Also take `N ≥ N₀` so that the finitely many initial coefficients of `H` vanish
and the base-case term of `A` is zero.

### 2. The sharp half of Sibuya–Ramis
`gev(F) ∈ {0} ∪ {slope ratios}`, not merely `gev(F) ≤ r₀`.  An upper bound alone is compatible with
an irrational exact order, so this is unavoidable for the card.
Analysis done: the naive bootstrap fails only on the finitely many "bad" shifts `μ` with
`(deg Φ_μ − deg Φ_0)/μ > r`, i.e. on the top part of the Newton polygon; the a-priori bound at level
`r` does not help there.  The classical remedy is the **Newton–Ramis factorization**
`L = M ∘ N` in `ℂ{t}[θ]` splitting the slopes at a cut, plus induction on the number of slopes.
In the shift-polynomial presentation `L = ∑_μ t^μ Φ_μ(θ)` with
`(t^a Ψ(θ))(t^b Φ(θ)) = t^{a+b} Ψ(θ+b) Φ(θ)`, so the factorization is a Hensel-type recursion in
`μ` with a majorant convergence proof.  That is the remaining mathlib-scale construction.
