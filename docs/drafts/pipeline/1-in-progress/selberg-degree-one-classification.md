# Selberg-class degree-one classification

- **ID:** selberg-degree-one
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** [Obstacles summary §2.1](../../../reports/review-0611/obstacles-summary.md), task A25
- **Statement:** every `F : RHTower.SelbergClass` of degree one is `L(s+iθ,χ)`, `χ` primitive mod the conductor `q ∈ ℕ`, `θ` the internal shift, and `θ=0` if `q=1`.

## Approach
1. Stirling on vertical lines with the exact constant: `Γ(a+iτ)/shape(a,τ) → √(2π)`, all real `a`.
2. Symbol: on a far-left line, `A(t)=Γ(s)·ω Q^{1-2s}∏Γ(λ(1-s)+μ̄)/Γ(λs+μ)` has `A(t) e^{πt/2} (q/2π)^{it} t^{iθ} → c ≠ 0`.
3. Boundary law: `f(z)=Σa(n)e^{-nz}`. Contour shift + FE: `lim_{y→0+} y^{1-iθ} f(y+iβ) = C ā(m) m^{-iθ}` at `β=2πm/q`, and `0` at every other `β>0`. Abelian lemma for `∫ r(t) t^{-iθ} e^{-t(ε+iτ)}`; Tannery over `n`.
4. `f(z+2πi)=f(z)` and `a(1)=1`: `q ∈ ℕ`, and `b(n)=a(n)n^{iθ}` has period `q`.
5. `b` multiplicative + periodic: character `χ₀` on units; `χ*` its primitive inducer.
6. `L(s+iθ,χ*)` is a class element; pole at `1-iθ` forces `θ=0` if `χ*` trivial.
7. `coeff_eq_of_finite_prime_discrepancy_arbitrary_gamma` closes; the boundary law for both presentations gives `q = cond χ*`.

The `ϑ<1/2` Euler condition is essential: `ζ(s)(1+p^{1-2s})` satisfies 1–5 with period `p²`.

## Lean
Folder `SelbergClass/DegreeOne/`.
