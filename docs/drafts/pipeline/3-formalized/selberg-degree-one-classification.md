# Selberg-class degree-one classification

- **ID:** selberg-degree-one
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Obstacles summary §2.1](../../../reports/review-0611/obstacles-summary.md), task A25
- **Statement:** if `F` is in the Selberg class with degree one, its conductor `q` is a positive integer and `F(s) = L(s+iθ,χ)` for a primitive character `χ` mod `q`, with `θ` the internal shift, and `θ = 0` if `q = 1`. Conversely all such functions are in the class.

## Lean
Folder `formal/GaloisForLFunctions/SelbergClass/DegreeOne/`.

| Step | Module | Declaration |
|---|---|---|
| Stirling with constant | `VerticalStirling` | `tendsto_Gamma_div_stirlingShape` |
| Symbol | `ArchimedeanSymbol` | `exists_tendsto_symbol` |
| Left-line expansion | `LeftLineExpansion` | `ordinaryExponentialSeries_eq_left` |
| Abelian limit | `AbelianBoundaryLimit` | `tendsto_abelIntegral_resonant`, `tendsto_abelIntegral_off` |
| Approach to the axis | `BoundaryPath` | `tendsto_div_gapAngle`, `tendsto_path_resonant`, `tendsto_path_off` |
| Boundary law | `BoundaryLaw` | `exists_boundary_law` |
| Integer conductor, periodicity (extended class) | `PeriodicCoefficients` | `exists_conductor_eq_nat`, `twistedCoeff_add_conductor` |
| Multiplicativity, character | `CoefficientCharacter` | `coeff_mul_of_coprime`, `exists_dirichletCharacter_of_periodic` |
| Euler logarithm of `L(s+iθ,χ)` | `DirichletEulerLog` | `exp_lSeries_dirichletLogCoeff` |
| `L(s+iθ,χ)` in the class | `DirichletElement` | `exists_selberg_dirichlet` |
| Classification | `Classification` | `degreeOne_classification`, `shift_eq_zero_of_zeta_agreement` |

## Proof
Put `f(z) = Σ a(n) e^{-nz}`, `q` the conductor, `θ` the internal shift.

1. **Symbol.** On `s = σ+it`, Stirling on each Gamma factor gives `Γ(s) Q^{1-2s} ∏ Γ(λⱼ(1-s)+μ̄ⱼ)/Γ(λⱼs+μⱼ) ~ c e^{-πt/2} (q/2π)^{-it} t^{-iθ}`, `c ≠ 0`. The `t log t` phases and all powers of `t` cancel because `2Σλⱼ = 1`.
2. **Expansion.** On `Re z > 0`, `f(z)` is a regular part plus `(1/2π)∫ z^{-u} Γ(u) F(u) dt` on a far-left line. This is a contour shift at real `z`, extended by holomorphy in `z`.
3. **Boundary law.** High on the line the functional equation expands `F(u)` over `ā(n) n^{u-1}`. The `n`-th integral is a Laplace transform of a slowly varying function at `ε + iτₙ`, with `ε = π/2 - arg z`, `τₙ = log(|z|q/2πn)`. Along `z = y+iβ`, `y/ε → β`. If `β = 2πm/q` then `τₘ/ε → 0` and the term has a limit; every other term is `o(1/y)`; Tannery gives `y^{1-iθ} f(y+2πim/q) → C ā(m) m^{-iθ}`, `C ≠ 0`, and limit `0` off the lattice.
4. **Periodicity.** `f(z+2πi) = f(z)` preserves the law. A nonzero strength at `2πm₀/q` must reappear on the lattice at `2πm₀/q + 2π`, so `q ∈ ℕ`. Comparing strengths at `m` and `m+q` shows `b(n) = a(n) n^{iθ}` has period `q`. This holds in the extended class.
5. **Character.** `a` is multiplicative, by induction on the convolution `a(N) log N = Σ_{d∣N} a(N/d) c(d)` with `c` supported on prime powers. A periodic multiplicative `b` with `b(1) = 1` is a character `χ₀` on reduced residues (CRT gives coprime representatives). Let `χ` be its primitive inducer. For `p ∤ q`, `a(p^k) = x^k` with `x = χ(p) p^{-iθ}`, hence Euler log `x^k/k`.
6. **Shift.** If `χ` is trivial, `F(s) = ζ(s+iθ) e^{D(s)}` on `Re s > 1`, with `D` the Dirichlet series of a discrepancy supported on the primes of `q`. By `ϑ < 1/2`, `D` is holomorphic past `Re s = 1/2`. So `F` has a pole at `1-iθ`; since poles occur only at `s = 1`, `θ = 0`.
7. **Rigidity.** `L(s+iθ,χ)` is then a class element, built from the functional equation of `χ` and order-one growth of the completed function. `F` and it differ at finitely many primes, so `coeff_eq_of_finite_prime_discrepancy_arbitrary_gamma` gives equal coefficients. The boundary law for both presentations gives `q ∣ cond χ`, so `q = cond χ`.

The condition `ϑ < 1/2` is essential at step 7: `ζ(s)(1+p^{1-2s})` satisfies steps 1–5 with period `p²` and is excluded only by it (`PositiveFiniteEuler.not_fullClass`).
