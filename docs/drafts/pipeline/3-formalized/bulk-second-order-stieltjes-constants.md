# The bulk entries are read by the Stieltjes constants

- **ID:** BSOS
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** AHD README §9 item 2 (limit of the bulk entries)
- **Statement:** for all conductors `e, e' ≥ 1`, with `R_e(n) = c_e(n)/(√φ(e)√n)`, `n ≤ N`, `P` the prime
  matrix and `ρ_e = γ + log e + τ(e)`: `⟨P R_e, R_{e'}⟩ − (log N − ρ_e)⟨R_e, R_{e'}⟩ → D(e, e')`, an explicit
  polynomial in `γ`, `γ₁` and `log d`, `d ∣ e e'`; `D(1,1) = 2γ₁ + γ²`, `D(p,p) = 2γ₁ + γ² + p log²p/(p−1)²`.

## Goal
The constant term of every bulk entry of the prime matrix on conductor packets, i.e. the `1/log N`
coefficient of `⟨P r_e, r_{e'}⟩ − (log N − ρ_e)⟨r_e, r_{e'}⟩` for the normalized packets `r = R/√log N`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_bulkPrimeResidual`

## Proof
Notation: `c_e(n) = Σ_{d∣(e,n)} μ(e/d) d`, `P(n,j) = U(n,j) + U(j,n)`, `U(n,j) = [n∣j, n≠j] Λ(j/n)/√(j/n)`,
`H_M = Σ_{i≤M} 1/i`, `ℓ_M = Σ_{i≤M} log i/i`.

1. **First Stieltjes constant** (`exists_tendsto_logHarmonic_sub`, `tendsto_logHarmonic_sub`). For `k ≥ 3`,
   `log t/t` is decreasing on `[k, k+1]`, so `log(k+1)/(k+1) ≤ (log²(k+1) − log²k)/2 ≤ log k/k`.
   Hence `ℓ_N − log²N/2` decreases and `ℓ_N − log²(N+1)/2` increases from `N = 3`, and the first is
   bounded below by the second: the limit `γ₁` exists.
2. **Divisor collapse** (`sum_divisors_dvd_vonMangoldt`, `sum_divisors_ramanujanLag_mul_vonMangoldt`). For
   `d ∣ j`, `n = d m` gives `Σ_{n∣j, d∣n} Λ(j/n) = Σ_{m∣j/d} Λ(m) = log(j/d)`; exchanging with the
   divisor sum of `c_e`: `(c_e ∗ Λ)(j) = Σ_{d∣(e,j)} μ(e/d) d (log j − log d)`.
3. **Prime pairing** (`sum_primeKernelUp_profiles`, `inner_fullPrimeMatrix_ramanujan`). For profiles
   `f(n)/√n`, `g(j)/√j`: `Σ_{n,j≤N} U(n,j)(g(j)/√j)(f(n)/√n) = Σ_{j≤N} g(j)(f∗Λ)(j)/j` (`√(j/n) = √j/√n`,
   `Λ(1) = 0`). So `⟨P R_e, R_{e'}⟩ = (A(e,e') + A(e',e))/√(φ(e)φ(e'))`,
   `A(a,b) = Σ_{j≤N} c_b(j)(c_a∗Λ)(j)/j`.
4. **Harmonic form** (`sum_Icc_dvd_dvd_log`, `conductorPrimePairing_eq`). Expanding `c_b` and step 2,
   `[t∣j][d∣j] = [L∣j]`, `L = lcm(d,t)`, `j = L i`, `dt = (d,t)L`:
   `A(a,b) = Σ_{d∣a} μ(a/d) Σ_{t∣b} μ(b/t) (d,t)((log L − log d) H_{⌊N/L⌋} + ℓ_{⌊N/L⌋})`.
5. **Asymptotics** (`tendsto_conductorPrimePairing_sub`). `H_{⌊N/L⌋} = log N − log L + γ + O(L/N)`
   (`abs_harmonicFloorError_le`); `ℓ_{⌊N/L⌋} − (log N − log L)²/2 → γ₁` (step 1 and
   `0 ≤ log(N/L) − log⌊N/L⌋ ≤ 1/⌊N/L⌋`, `abs_log_div_sq_sub_le`). So `A(a,b) − Φ_{a,b}(log N) → 0`,
   `Φ_{a,b}(x) = Σ_{d∣a,t∣b} μμ (d,t)((log L − log d)(x − log L + γ) + (x − log L)²/2 + γ₁)`, a quadratic in `x`.
6. **Gram entry** (`sum_ramanujanLagCoefficient_mul_div_eq`, CompletedArithmeticForms):
   `√(φφ')⟨R_e, R_{e'}⟩ = [e=e']φ(e)(log N + γ) − I(e,e') + O(1/N)`, `I` the orbit intersection.
7. **Only the constant survives** (`tendsto_bulkPrimeResidual_div_log`, `tendsto_of_sub_isQuadratic`).
   `u_N = ⟨P R_e, R_{e'}⟩ − (log N − ρ_e)⟨R_e, R_{e'}⟩ = log N ⟨P r_e − (log N − ρ_e) r_e, r_{e'}⟩` and the RAPT
   residual `‖P r_e − (log N − ρ_e) r_e‖ → 0`, `‖r_{e'}‖ → 1`: `u_N = o(log N)`. By steps 5–6,
   `u_N − Ψ(log N) → 0` with `Ψ` quadratic. If `u_N − (αx_N² + βx_N + c) → 0` and `u_N/x_N → 0`,
   `x_N → ∞`, then `α = β = 0` and `u_N → c`. Here `c = Ψ(0) = D(e,e') =
   (Φ_{e,e'}(0) + Φ_{e',e}(0) + ρ_e([e=e']φ(e)γ − I(e,e')))/√(φ(e)φ(e'))` (`bulkSecondOrder`).
8. **Prime conductor** (`bulkSecondOrder_prime`). Divisors `{1, p}`, `μ(p) = −1`, `φ(p) = p − 1`,
   `τ(p) = log p/(p−1)`, `I(p,p) = (p−2) log p`: `Φ_{p,p}(0) = (p−1)γ₁ − γ log p + p log²p/2` and
   `D(p,p) = 2γ₁ + γ² + p log²p/(p−1)²`. Pole: `D(1,1) = 2γ₁ + γ²` (`tendsto_poleResidualPairing`).

Normalized form: `log N (⟨P r_e, r_{e'}⟩ − (log N − ρ_e)⟨r_e, r_{e'}⟩) → D(e, e')`
(`tendsto_log_mul_bulkPrimeResidual`). Lean modules: `ArithmeticHodgeTheoryOfDegenerations/
TheBulkSecondOrderOfThePoleIsAStieltjesConstant`, `.../TheBulkEntriesAreReadByTheStieltjesConstants`.

## Log
- 2026-11-03 — proved and formalized.
