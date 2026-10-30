# The completed shell energy is the actual Ramanujan-mode energy at every overlap

- **ID:** completed-shell-energy-is-the-actual-mode-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q1 of `docs/reports/review-2910/obstacles-summary.md`; §2.5 item 2 ("on the pole vector
  the shell's prime terms collapse to the archimedean absolute value `log ℓ`");
  `3-formalized/completed-shell-energy-positive-fourier-integral.md`,
  `3-formalized/shells-repay-every-conductor.md`.
- **Statement (target):** For `φ ∈ C²` supported in `[0,1]`, `M = ∫φ² > 0`, every fixed `c > 0` and
  `m ≥ 1`, the actual complete Weil matrix at width `c/N` satisfies
  `⟨W x_m, x_m⟩ → completedConductorEnergy φ c m` for the normalized Ramanujan vectors `x_m`;
  first `m = 1`; then mixed entries; then the norm-quasimode form.

## Paper proof for the conductor-one energy

Write `w = c/N`, `g = φ_w`, `a_n = g(· − log n)`, `A(s) = ∫ g(u) g(u+s) du = w G(s/w)`,
`x_n = n^{−1/2}/√log N`. Entries are
`W_{nj} = [Arch(n,j) − Prime(n,j) + Pole(n,j)]/(wM)`, `Arch = 2θ′(0)∫a_n a_j + ∫_{y>0} levyMixed`.

**Exact all-width decomposition.** With `α = cq`, `s = |log j − log n|`,
`W = (log N + self(c) − γ + selfErr)·I − P + Center(α) − CrossErr^{sep} + PoleErr + Ov − NR`,
where `CrossErr^{sep}` is the cross error on separated pairs (`s > w`), `NR` the non-ratio prime
matrix, and `Ov(n,j) = Arch(n,j)/(wM) + (α/N) ω(s)` on overlapping pairs `0 < s ≤ w`.
On separated pairs this is the separated decomposition; on overlapping pairs the center kernel is
added back.

**Divisor collapse (exact).** For the pole vector,
`Σ_{n,j} x_n x_j Prime(n,j) = (2/log N) Σ_{n ≤ N} Σ_ℓ (nℓ)^{−1/2} Λ_N(ℓ) A(log(ℓ/n))`,
`Λ_N(ℓ) = Σ_{k∣ℓ, ℓ/k ≤ N} Λ(k)`, `= log ℓ` for `ℓ ≤ N`. The `ℓ = n` terms are the ratio form
`⟨P x, x⟩ wM`; the rest is `⟨NR x, x⟩ wM`.

**Overlap asymptotics.** For `0 < s ≤ w` the common window has width `≤ 2w`, and the mixed Robin
expansion gives `Arch(n,j)/(wM) = log(N/c) G(s/w)/M + O_φ(1)`; also `(α/N) ω(s) = O(1)`.
The weighted number of overlapping pairs is `O_c(1)`, and `log ℓ = log N + O_c(1)` on them.
Hence `⟨(Ov − NR) x, x⟩ = −(1/M) Σ_{n ≠ j, s ≤ w} (nj)^{−1/2} G(s/w) + o(1) → −2S(c)/M`
by Riemann sums (`Σ_n (n(n+h))^{−1/2} G(N log(1+h/n)/c) → ∫_{h/c}^1 G(u)/u du`).

**Separated part.** Reuse the prime, center, self and pole residuals at general `c`; prove the
separated cross error vanishes on the mode (bound `38w(∫|g|)²/((s−w)²∫g²)` for `s ≥ 2w`,
`O(1)` entries on the `O_c(1)`-mass band `w < s < 2w`).

Limit: `self(c) + γ − γ + α − 2S(c)/M = completedShellEnergy φ c`.

## Lean plan
1. `RAPT/TheCompleteWeilMatrixDecomposesAtEveryOverlap.lean` — exact decomposition.
2. `RAPT/ThePrimeFormCollapsesOnThePoleVector.lean` — divisor collapse.
3. `RAPT/TheOverlappingAtomsHaveALogarithmicPairing.lean` — overlap asymptotics.
4. `RAPT/TheSeparatedCrossErrorVanishesAtEveryOverlap.lean`.
5. `RAPT/TheShellRiemannSums.lean`, assembly `RAPT/TheConductorOneEnergyIsTheCompletedShellEnergy.lean`.

## Status
Formalized as the norm quasimode at every `c > 0` and every admissible profile:
`CACT.tendsto_completeWeilMatrix_ramanujan_quasimode_norm` (from
`RAPT.tendsto_completeWeilMatrix_ramanujan_residual_add_upward_norm` and
`RAPT.tendsto_sum_sq_upwardPrimeRow_sub_shellCorrection`); energies and mixed entries follow by
`RAPT.tendsto_inner_sum_quasimodes`.

## Log
- 2026-10-30 — plan written.
- 2026-10-30 — norm-quasimode residual reduced to the upward defect: `3-formalized/complete-weil-residual-is-the-upward-defect.md`. Upward ℓ² limit then proved (hgt-b0); quasimode complete.
