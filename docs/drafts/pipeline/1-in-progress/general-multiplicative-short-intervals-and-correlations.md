# General multiplicative short intervals and averaged correlations

- **Stage:** 1-in-progress
- **Source:** review-0911 §11.4.

## Targets

For real multiplicative `f` with `|f|≤1`, uniformly in `f`, compare the
length-`h` average at almost every integer start in `[X,2X]` with the
length-`X` average, for every `h→∞`, `h≤X`.
[Matomäki–Radziwiłł, Theorem 1](https://arxiv.org/html/1501.04585)
gives the quantitative exceptional-set bound and permits `f` to vary with `X`.
For Liouville, also prove
`Σ_{h≤H}|Σ_{n≤X}λ(n)λ(n+h)|=o(HX)` for `H→∞`, `H≤X`.
The absolute values in this second target are essential.

## Existing exact boundary

`RHTower.Sieve.averagedMeanSquare_moebius_of_tendsto` proves the Möbius
mean square over multiplicative fibres for every diverging length bounded
by `√x`. Its final statement has no unresolved analytic premise.

`BezoutValuationIncidence.tendsto_sum_sq_moebius_window_div` transfers this
to ordinary integer windows for `H : ℕ→ℕ` with `H→∞`, monotonicity,
`H(2k)≤H(k)+1`, and `H(k)≤k`. It does not state the general multiplicative
comparison or the absolute correlation estimate.

## Prime-supported mean square

[Soundararajan, §7](https://arxiv.org/html/1606.08021#S7) uses the estimate

`∫_E |Σ_{p≤P}c_p p^{it}|² dt
 ≪ (P/log P + |E|P exp(−log P/(log(T+P))^(2/3+ε))) Σ_{p≤P}|c_p|²`,

for measurable `E⊂[−T,T]`. The diagonal `P/log P` is necessary; the
integer-support Halász–Montgomery estimate loses a logarithm.
A triangular majorant on primes up to `2P` gives the dual kernel
`Σ_{p≤2P}(2−p/P)p^{it}`. Its required bound has an integrable diagonal
`(P/log P)/(1+t²)` plus the uniform zero-free-region error.

The corpus has restricted-support duality in
`Sieve/HalaszMontgomerySupport`, and unconditional twisted-prime bounds in
`Sieve/VonMangoldtTwistPrimeEnvelope` and `VonMangoldtTwistScaledEnvelope`.
The smoothed prime-kernel estimate, its weighted duality transfer, and the
general-`f` short/long-average comparison still require proof. A wrapper
assuming the prime-kernel estimate would not discharge this task.

Unmodulated short-interval cancellation does not yield the absolute
Liouville correlation target; its additive Fourier input remains separate.
