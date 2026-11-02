# Fixed-scale prime-flip defects are uniformly bounded

- **ID:** fixed-scale-prime-flip-defects-are-bounded
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Γ12, finite-scale spectral identification.
- **Statement:** For every prime pattern `P` and fixed cutoff `T`, put `c_N=S_P(N)/H_N`, `δ_T=Π_(p∈P,p<T)(p−1)/(p+1)`, and let `S_T(Y),R_T(Y)` be the signed and ordinary rough harmonic sums. Then
  `Σ_(a≤N,T-smooth)[S_T(⌊N/a⌋)−(c_N/δ_T)R_T(⌊N/a⌋)]²/[a R_T(⌊N/a⌋)]≤K_(P,T)`
  for every `N≥1`. No density assumption is required.

Consequently, for `T≥1`, the smooth projection of `ω⃗_P−(c_N/δ_T)ω⃗_F`, where
`F={p∈P:p<T}`, has uniformly bounded squared norm. If `A_P(N)=o(log N)`,
the defect is `o(S_P(N)²/H_N)`.

## Proof

For any real completely multiplicative contraction `f`, harmonic interval
bounds give `|S(N)−S(⌊N/p⌋)|≤2+log(2p)`. The prime-peeling identity
`S_p(N)=S_(p+1)(N)+(f(p)/p)S_p(⌊N/p⌋)` therefore yields
`S_T(N)=H_f(T)S(N)+O_T(1)`, where `H_f(T)=Π_(p<T)(1−f(p)/p)`.
Induction needs no harmonic asymptotic or density hypothesis.

Apply this identity to `ω_P` and to the constant gauge. Since
`H_ω(T)δ_T=H_1(T)` and `|c_N|≤1`, the fibre error at `Y=⌊N/a⌋` is bounded by
`C_ω+C_1/δ_T+2|H_ω(T)|(2+log(2a))≤K_T(1+log a)`.
Every nonempty rough interval has harmonic mass at least one, so its squared
contribution is at most `K_T²(1+log a)²/a`.

The bound `(2+log a)²≤36√a` and the convergent finite-prime Euler product
`Σ_(a T-smooth)a^(−1/2)` bound the sum independently of `N`.
The smooth-fibre inner-product inequality gives the projected-vector bound.

At zero prime density, signed renewal gives `S_P(N)/(log N)^(1/2)→∞`, while
`H_N≤2log N` eventually. Hence `S_P(N)²/H_N→∞`, making every fixed bounded
defect negligible at that normalization.

## Lean

Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory`.

`FinitePrimeRemovalHasBoundedHarmonicError.lean`:

- `abs_gaugeHarmonicSum_sub_natDiv_le`
- `exists_abs_roughMean_sub_eulerHead_mul_le`

`TheFixedScaleDefectIsBounded.lean`:

- `exists_sum_smoothSet_log_sq_div_le`
- `exists_fixedScale_fibre_error_le_log`
- `exists_fixedScaleDefect_le_constant`
- `exists_fixedScale_projection_error_le_constant`
- `eventually_zeroDensity_fixedScaleDefect_le`

Both modules passed direct Lean checks. All seven audited declarations depend
only on `propext`, `Classical.choice`, and `Quot.sound`.
