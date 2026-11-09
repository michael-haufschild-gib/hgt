# Infinite rough currents at prime-head returns

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Euler–FE transport: simultaneous height escape, vanishing damping and head conditioning.

## Theorems

Let `R(t)=Σ_{s∈S}w_s s^(it)` be supported on integers smooth below `Y`.
For square-summable coefficients `a_n` supported on positive `Y`-rough
integers, set `D_T(t)=Σ_n a_n exp(−n²/T)n^(it)`.
The actual-height identity is

`T⁻¹∫₀ᵀ |R(t)|²|D_T(t)|²dt → (Σ_S|w_s|²)(Σ_n|a_n|²)`.

The same limit holds on the escaping window `[T,2T]`, with damping still
`1/T`; subtracting two fixed-damping brackets doubles only the error constant.

The damping and observation horizon change together. The entire rough series
is admitted, including the literal rough von Mangoldt coefficients
`a_n=Λ(n)n^(−σ)`, `σ>1/2`. Fixed finite rough polynomials do not settle this target.
For these coefficients, the limiting rough variance tends to zero as `Y→∞`.

## Proof mechanism

Smooth–rough unique factorization makes `(s,n)↦sn` injective. Apply the sharp
integer-frequency mean-value bound to finite restrictions, then pass through
the absolutely convergent Gaussian series. With
`W_j=Σ_S s^j|w_s|²` and `A_j(T)=Σ_n n^j|a_n|²exp(−2n²/T)`, the exact bracket is

`|∫₀ᵀ|R|²|D_T|²−T W₀ A₀(T)|≤104 W₁ A₁(T)`.

Gaussian damping gives `A₁(T)≤√T Σ_n|a_n|²`; dominated convergence gives
`A₀(T)→Σ_n|a_n|²`. Thus the off-diagonal error divided by `T` vanishes.
Prime-head conditioning costs its weighted mass `W₁`; it does not inflate
the limiting rough variance. The theorem retains explicit dependence on
the head so that subsequent growing-head schedules can be assessed.

## Arithmetic use and remaining gap

Apply to all rough von Mangoldt coefficients and to head probes concentrated
near prescribed prime phases. This supplies joint-scale tail control for a
recurrence receiver. Coupling it to the continued Euler current, and producing
same-depth zeros, remain separate obligations; no recurrence premise is assumed.

## Formalization

`TheHeadDoesNotChangeTheInfiniteRoughMean.lean` proves
`abs_integral_head_mul_infiniteRough_sub_diag_le`: the complete rough-current
bracket for absolutely summable coefficients with finite weighted square mass.
Its finite precursor and infinite theorem pass direct Lean checking; both
transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

`TheGaussianRoughMeanSurvivesVanishingDamping.lean` proves:

- `abs_integral_head_mul_gaussianRough_sub_diag_le`: the full bracket, with independent damping and observation horizons.
- `tendsto_head_gaussianRough_mean`: exact variance on `[0,T]`.
- `tendsto_dyadic_head_gaussianRough_mean`: exact variance on `[T,2T]`.
- `tendsto_dyadic_head_gaussianVonMangoldt_mean`: literal infinite arithmetic specialization for `σ>1/2`.
- `tendsto_roughVonMangoldt_squareMass_zero`: vanishing variance as the prime cutoff grows.

Both modules belong to `EulerFETransportTheory/`. Direct `lake --old env lean`
checks pass. All seven terminal transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
