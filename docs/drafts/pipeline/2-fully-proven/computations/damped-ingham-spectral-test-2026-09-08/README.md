# Damped Ingham spectral test (2026-09-08)

**Question.** The full isolation law (dichotomy card, sixth cycle) reduces to a "damped Ingham inequality": for
frequencies `μ_k` with gaps `≥ g`, decay rates `0 ≤ ν_k ≤ K`, and a window `ℓ' > 2π/g`, is
`λ_min(G) ≥ c₀ (ℓ' − 2π/g) e^{−2Kℓ'}` for the Gram matrix `G_jk = ∫_0^{ℓ'} e^{−(ν_j+ν_k)s} e^{i(μ_j−μ_k)s} ds`,
with `c₀` absolute (uniform in the number of terms `n`)? Reasoning could not decide the `n`-dependence.

**Method** (`damped_ingham.py`, mpmath at 60 digits, 16 cores). `g = 1`, `ℓ' ∈ {8, 12}`, `K ∈ {0, ½, 1, 1½, 2, 3}`,
`n ∈ {2,3,4,6,8,12,20}`; seven (μ, ν) patterns (arithmetic or random spaced frequencies; all-`K`, half, ladder, top-one,
uniform-random decay) and, for `n ≤ 8`, an adversarial random local search over gaps and decay rates.
Reported: `r(K) = log λ_min + 2Kℓ'` (bounded below iff the conjectured floor holds) and the adversarial minima.

**Results** (`damped_ingham_results.json`, `run.log`). `r(K) ≥ 1.6` in every case and `r` increases with `K`: the floor
`e^{−2Kℓ'}` is never approached. But the worst pattern is always uniform decay `ν_k ≡ K`, and there
`log λ_min` decreases about linearly in `n` at fixed `K`: at `K = 3`, `ℓ' = 8`: `−6.1, −9.4, −12.1, −16.1, −18.4, −27.3`
for `n = 2, 3, 4, 6, 8, 20` (slope `≈ −1.5` per term at `K/g = 3`, `≈ −0.3` at `K/g = ½`). Extrapolating, the floor
`e^{−2Kℓ'} = e^{−48}` is crossed near `n ≈ 35`. Adversarial searches converge to uniform decay with gaps at the minimum.

**Interpretation.** The conjecture is false as an `n`-uniform statement once the decay `K` exceeds the frequency gap `g`:
with weight `e^{−2Ks}` the effective window is `1/(2K) < 2π/g`, on which `n` exponentials are nearly linearly
dependent, so `λ_min ≍ e^{−c(K/g) n}`. For `K ≲ g` the loss per term is small. Consequence for the isolation
programme: the natural real-part band is of width `≍ D/log T` (decay spread at most the frequency gap), where the
single-band law extends with polynomial loss; across wider spreads, energy hiding at the Gram level is possible in
principle and is controlled only by the number of interacting zeros (`≍ log T/D` per unit height through the Lorentzian
weight), giving a loss `e^{−c·log T/D}` with `c` growing with the spread — polynomial only when the spread is
`O(D/log T)`. The full isolation law at fixed separation is therefore not reachable by Gram/Ingham-type bounds alone;
the ladder search's failure to find hiding is not explained by them. Nothing here enters any Lean proof.

**Correction (same day).** The extrapolation "the floor is crossed near `n ≈ 35`" is wrong. For uniform decay
`ν_k ≡ K` the floor holds trivially and uniformly in `n`: `G = ∫ e^{−2Ks} E E^*` with `e^{−2Ks} ≥ e^{−2Kℓ'}` pointwise, so
`λ_min(G) ≥ e^{−2Kℓ'} λ_min(G₀) ≥ e^{−2Kℓ'}(ℓ' − 2π/g)` by Ingham. The observed linear decrease in `n` must saturate above
that floor; the data are consistent with the conjecture (`r ≥ 1.6` everywhere, increasing in `K`). The adversarial
searches converging to uniform decay indicate that non-uniform decay is not worse (`n ≤ 8`). The right reading of
`r` increasing with `K` is that the true floor is polynomial in `K`, not exponential: on the half-line the damped Gram
matrix `[1/(λ_j + λ̄_k)]`, `λ_j = ν_j + iμ_j`, is the Gram matrix of the Cauchy kernels `1/(ν_j + i(t+μ_j))` in
`L²(ℝ)`; for `K ≲ g` these are concentrated on disjoint windows of width `2π/g` around `−μ_j`, each carrying mass
`≈ π|x_j|²/ν_j`, and the cross terms are a Hilbert-type sum controlled by the Montgomery–Vaughan inequality.
Conjecture (corrected): `λ_min(G) ≥ c(K/g) · min(ℓ', 1/K)` uniformly in `n` for `K ≤ c'g`.
