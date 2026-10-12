# The radical truncation has Weil energy e^{−Nyquist height}: exact doubly-exponential order

- **ID:** C607 (HCF ledger row 611)
- **Stage:** 3-formalized (MUST-1319)
- **Type:** THEOREM for Φχ_L (both halves in Lean). The ground-state constant c* is the [OPEN CORE].
- **Source:** HCF loop rows 602 (CANNOT-507), 605–609 (MUST-1302, MUST-1311); MUST-478.
- **Statement (provable half):** for all large `L`,
  `E(L)²/Y(L) ≤ Re W(Φχ_L, Φχ_L) ≤ K·E(L)²`, with `E(L) = e^{9L/2}e^{−πe^{2L}}` and
  `Y(L) = 2πe^{2L}`. So `log W(Φχ_L) = −2πe^{2L} + O(L) = −T_N(L) + O(L)`, where
  `T_N(L) = 2πe^{2L}` is the Nyquist height of level `L`. Both bounds are unconditional.
- **Conjecture (open core):** under RH, the even (pole-vanishing) Weil ground energy at half-width
  `A` satisfies `−log m(A) = c*·e^{2A}(1 + o(1))` for a finite constant `c* ≥ 2π`. Heuristic:
  Hermite edge profiles `(D + Y)^m Φ` with `m = κY`, κ small, already improve the constant, so
  `c* > 2π` is expected. Near-null ground states then carry a heat-Hankel (polynomial × Gaussian)
  structure at the edge `|u| ≈ A`, of width `1/√(2Y)` and degree `κY`: HCF reappears at its own
  conditioning floor.

## Goal
CANNOT-507 / MUST-478 bound the HCF/Weil margin by `e^{−πe^{2A−1}}` and `e^{−πe^{2A−1/2}}`. Those
proofs use a smeared radical test and only one tail factor. With a sharp-edge truncation and both
zero-side factors being tails, the true order of the canonical near-null energy is `e^{−2πe^{2A}}`.
That is the Nyquist height `T_N(A)` (MUST-1281: window K resolves zeros up to `T_N(2√K)`) appearing
as the conditioning exponent. The same number fixes resolution and conditioning.

## Approach (paper proof, upper half)
Let `T_R = Φ(χ_R − χ_L)` be the edge tail (MUST-1302). By the radical identity,
`W(Φχ_L) = lim_R W(T_R)` (module C). The explicit formula gives `W(T_R) = pole + arch − primes`.
The prime term is `≥ 0`, because `T_R ≥ 0` gives a nonnegative autocorrelation and `Λ ≥ 0`, so it
can be dropped.
- **Pole.** `pole ≤ 2(∫T e^{|u|/2})² ≤ 2(2C₀E e^{L/2}/(c − ½))²`, using the majorant
  `T ≤ C₀E e^{−c(|u|−L)}` with `c = Y − 9/2`.
- **Archimedean term.** `|γ(r)| ≤ C + |r|` (`abs_gammaBracket_le`) and
  `|r| ≤ λ/2 + r²/(2λ)`, together with Plancherel `∫|f̂|² = 2π∫|f|²` and
  `(f')^ = −ir f̂`, give `arch ≤ (C + λ/2)∫T² + (1/(2λ))∫T'²`.
- **Inputs.**
  - `∫T² ≤ C₀²E²/c`.
  - `|T'| ≤ C₀(Y + 4π + 2S₁(1+Y))·E·e^{−(c−2)(|u|−L)}`. This uses the sharp log-derivative
    `|Φ'| ≤ 2π(e^{2u}+2)Φ` and the cutoff derivative bounds `2S₁/η`.
  - Hence `∫T'² ≤ (eK)²E²/(c−2)`.
- **Conclusion.** With `λ = Y`: `W(T_R) ≤ K·E²` uniformly in `R`.

**Lower half.** This is MUST-1302's explicit form, `W(T_R) ≥ (ℓ/2 − 10)∫T² − (E²/Y)·120C₀²u(L)`
with `∫T² ≥ 400e^{−6}E²/Y`. That is `≥ E²/Y` for large `L`.

## Phase 4 verdict
SURVIVES (quantitative). The corpus has only one-sided super-exponential margins (MUST-478, CANNOT-507)
with weaker constants, and nothing two-sided. Significance is moderate: it fixes the exact order of the
canonical near-null energy. The constant question (`c*`) is the genuinely new open problem.

## Log
- 2026-10-12 — created.

## Lean
`RHTower.exists_twoSided_truncKernel_energy` and `RHTower.exists_truncKernel_rayleigh_le` in
`formal/GaloisForLFunctions/RHTower/RiemannKernelTruncationEnergyOrder.lean`, wired into
`RHTower.lean`; `#print axioms`: propext, Classical.choice, Quot.sound.

## Follow-up (C608, ledger row 612)
- `c* > 2π` on paper: even multipliers `(D² − Y²)^m`, `m = ⌊Y/14⌋`, give Rayleigh
  `≤ e^{−2π(1+1/24)e^{2A}}` (Cauchy–Laplace kernel on a circle of radius `1/5`).
- The one-sided `(D+Y)^m` heuristic above is wrong for even tests: it amplifies the left tail by `2^m`.
- Corpus already owns the near-radical family and its dimension `≍ e^{2a}`
  (`TruncatedRiemannKernelWeilEnergy`, `zeta_weil_near_radical_dimension`).
- 2026-10-12 — formalized; moved to 3-formalized.
