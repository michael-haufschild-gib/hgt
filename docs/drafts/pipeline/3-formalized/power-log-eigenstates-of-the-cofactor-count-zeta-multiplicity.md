# Power-log eigenstates of the renormalized cofactor count the multiplicity of ζ

- **ID:** adr-power-log-index
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `0 < ε < 1/2` and `1/2 ≤ Re s < 1 − ε`, the real and imaginary parts of
  `u_c(n) = Σ_{k≤K} c_k log^k n · n^s` both satisfy the renormalized inversion law
  (`v + D̃v` of bounded pronic energy, i.e. `D̃v ≈ −v`) iff `c_k = 0` for all `k ≥ ord_{s+ε} ζ`.
  The power-log eigenspace of `D̃` at exponent `s` has complex dimension exactly the multiplicity of
  the zero of `ζ` at `s + ε` (zero when `ζ(s+ε) ≠ 0`).

## Paper proof
1. **Log-power symbol law.** The error `E_n(s)` of the two-pole expansion
   (`the-renormalized-cofactor-acts-on-power-rows-by-zeta`) is holomorphic in `s` on
   `0 < Re s < 1 − ε` (finite sum of `x^s`, `ζ(s+ε)`, and the pole sum, a locally uniformly
   convergent series of `m^s cell_m`), and `|E_n(s)| ≤ K_s n^{(Re s − ε)/2}` with `K_s` continuous.
   On a closed disc of radius `r = min(Re s₀, 1−ε−Re s₀)/2` Cauchy's estimate gives
   `|∂^k E_n(s₀)| ≤ k! M r^{-k} n^{θ/2}`, `θ = Re s₀ + r − ε < 1`. The `k`-th derivative is
   `Σ_j j^{-ε} log^k⌊n/j⌋ ⌊n/j⌋^s − 𝓛_{s,k} n^{1−ε} − Σ_i C(k,i) ζ^{(i)}(s+ε) log^{k−i} n · n^s`
   (Leibniz; termwise differentiation of the pole sum gives the pole trace of the log-power row).
2. Hence `(I + D̃) Re u_c = Re Σ_d b_d log^d n · n^s` modulo admitted rows, with the Leibniz matrix
   `b_d = Σ_{k≥d} C(k,k−d) ζ^{(k−d)}(s+ε) c_k`.
3. **Block independence.** If `b ≠ 0` with top index `D`, then `|Σ_d b_d log^d n · n^s| ≥
   |b_D| log^D n · n^{Re s}/2` for large `n`, so `|·|²/(n(n+1)) ≥ |b_D|²/(8n)` and the energy diverges.
4. **Triangular inversion.** With `ζ^{(i)}(s+ε) = 0` for `i < m`, `ζ^{(m)}(s+ε) ≠ 0`:
   `b_{k−m} = C(k,m) ζ^{(m)} c_k + Σ_{k'>k}(…)c_{k'}`; downward induction gives `b = 0 ⇔ c_k = 0 ∀k ≥ m`.
5. The order is finite in the strip (`ξ` has finite order, equal to that of `ζ` there).

## Lean
`ArithmeticDefectRigidity/LogPowerRowsReadTheDerivativesOfZeta.lean`
(`exists_norm_iteratedDeriv_powerSymbolError_le`, `iteratedDeriv_powerSymbolError`,
`norm_logPowerCofactorSum_sub_le`) and
`ArithmeticDefectRigidity/PowerLogEigenstatesOfTheCofactorCountZetaMultiplicity.lean`
(`exists_pronicNorm_powerLogRow_symbol_le`, `powerLogRow_coeff_eq_zero_of_bounded`,
`leibnizCoeff_eq_zero_iff`, `powerLogRows_renormalizedInversion_iff`,
`powerLogRows_renormalizedInversion_iff_order`). Standard axioms only.

## Insight
The renormalized cofactor sees zero multiplicities exactly: a zero of order `m` at `ρ` produces the
Jordan chain `n^{ρ−ε}, n^{ρ−ε}log n, …, n^{ρ−ε}log^{m−1} n` of approximate `(−1)`-eigenrows. This is
the ADR operator-level index theorem (compare AOT open problem 5 for paid quotients, still open).
