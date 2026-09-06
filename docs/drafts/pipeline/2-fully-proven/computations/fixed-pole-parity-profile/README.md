# Fixed-pole Weil criterion: exact parity energies on `0 < a ≤ 8` (guidance computation, 2026-09-06)

**Object.** The corpus's exact RH criterion `riemannHypothesis_iff_primeGammaPoleInequality`:
`RH ⟺ ∀a>0, |C(a)| ≤ A(a)` with (κ = −γ − log 2π, `X = e^{2a}`, `L(t) = −log(1−e^{−t})`)

- `A = κ·2sinh a − e^a + (1−2a)e^{−a} + B₁ − 2e^a E_M(2a) + 2e^{−a}ψ(X)`,
- `C = κ·2a + 2a² + (2sinh a)² + B₀ − T`, `T = Σ_{2≤n≤X} Λ(n)(1+1/n)(2a − log n)`,
- `B₀ = ∫_0^{2a} L`, `B₁ = (e^a/2)∫_0^{2a} e^{−t}L(2t)dt + e^{−a}∫_0^{2a} e^{t}(L(t) − L(2t)/2)dt`,
- `E_M(t) = Σ_{n≤e^t}Λ(n)/n − t`.

Even energy `A + C`, odd energy `A − C` (test vectors `2cosh(x/2)·1_{[−a,a]}`, `2sinh(x/2)·1_{[−a,a]}`).

**Method.** `fixed_pole_profile.py`: exact Mangoldt sieve to `e^{16}`, `B₀, B₁` by mpmath quadrature,
grid `a ∈ [0.01, 8]`. `fixed_pole_zero_check.py`: compares with the first 400 zeta zeros.

**Results** (`fixed_pole_profile.out`, `fixed_pole_zero_check.out`).
- No negative parity energy on the grid. `even + odd = 2A` exactly.
- `A(a)/e^a → 0.04619 = 2 + γ − log 4π` (0.04404 at `a=2`, 0.04619 at `a=8`).
- `C(a) = Σ_ρ X^ρ/ρ² + O(1)`: at `a = 8`, `C = −16.65` vs `−16.70` from 400 zeros; at `a = 6`,
  `−6.74` vs `−6.88`.
- Relative margins: `even/e^a ∈ [0.029, 0.063]`, `odd/e^a ∈ [0.030, 0.062]` for `2 ≤ a ≤ 8`,
  oscillating around the mean `0.0462` with amplitude of the same order; minimum of `even/e^a` on the
  grid `0.0289` at `a = 4.02`. As `a → 0` both energies vanish (`odd ≍ a³`), a normalisation effect.

**Interpretation.** `(A ± C)(a) = e^a Σ_{γ>0} 2(1 ± cos(2aγ − 2 arg ρ))/|ρ|² + O(a²)` under RH; the
criterion is the triangle inequality for the almost-periodic zero sum `Σ_ρ e^{2iaγ}/ρ²` against
`Σ_ρ|ρ|^{−2}`, with zero asymptotic margin. Any prime-side proof must reach the sharp constant
`Σ_ρ|ρ|^{−2} = 2 + γ − log 4π`. Nothing here is used in Lean.
