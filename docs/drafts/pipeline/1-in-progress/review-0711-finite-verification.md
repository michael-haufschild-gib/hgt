# Review-0711 §2.1 finite verification (A1–A8)

- **ID:** review-0711-finite-verification
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0711/obstacles-summary.md)
- **Statement:** Each task A1–A8 gets a complete unconditional Lean theorem, easiest first. No computations.
- **Predecessor:** [review-0611 card](review-0611-finite-verification.md) (height 67, rank ten, templates below `27/5`).

## Status

| Task | Status | Lean |
|---|---|---|
| A8 | done: dimension one is Tate-positive iff `A ≤ log 5` | `WindowTowerOfSpecZ/TheFirstTateDimensionEndsAtFive.lean`: `tateFunction_one_nonneg_iff_le_log_five` |
| A4 | done: rank 11 positive definite at every `0 < a ≤ ½`, from height 67 | `ThetaCuspSections/TheEleventhSectionFromHeightSixtySeven.lean`: `thetaCuspCenterMixedSignedHankel_eleven_posDef`; `TheSharpCurrentTail.lean`, `QuinticLegendreKernel.lean` |
| A2 | Hausdorff shift explicit from `e¹²`; `windowHeight` open | `SquareRootThreshold/EffectiveHorizons/HausdorffShiftsFromTheSharpMass.lean`: `scaledHausdorffMomentDifference_nonneg_of_sharp_shift_le` |
| A1 | blocked by the no-computation rule | — |
| A3 | blocked: needs certified Galerkin precision | — |
| A5 | blocked by the no-computation rule | — |
| A6 | blocked by the no-computation rule; CHT paused | — |
| A7 | no precise statement in the corpus | — |

## A8

At `k = 1`: `α² = 1/8`, `β² = 1/3`, `χ = 1/2`, `δ = 2/√5`. On `(log(9/2), log 5]` the late pivots are
`≥ 23/72` and `83/168`, and `9/64 ≤ (23/72)(83/168)`. Past `log 5` the pivots are `7/8, 83/168, 49/83,
64/147, 365/512`; the last is `49/83 − 2/√5 − 512/1095 < 0`. Antitonicity in `A` gives the horizon.

## A4

Rank 11 failed with the rank-ten constants by a factor `≈ 17`. The tail constant of the current was
the loss: `6.05·10⁹` against a true size `≲ 10²`.

- **Sharp strip bound.** On `Re z = u ≥ 0`, `e^{3u/2}‖Φₙ(z)‖ ≤ 2πe^{2u}(2πX² + 3X)e^{−0.53X}`,
  `X = n²e^{2u}`, is the derivative of `−(π/n²)Q(X)e^{−0.53X}`. So the shifted line integral is
  `≤ 2πQ(1)e^{−0.53}π²/6 ≤ 1000`, uniformly on `|a| ≤ 3/2` (`norm_XiC_le_wide`).
- **Cauchy radius `½`** on the wide strip: `|Ξ'| ≤ 2960`, `|Ξ''| ≤ 8762`, so
  `|current a b| ≤ 3.6·10⁷|a|e^{−(7/5)|b|}` (`abs_current_le_sharp`).
- **Quintic Legendre kernel** on `[1, 25]`: `J₅(s) ≤ 342 s¹⁰` for `s ≥ 361`.
- Tail `≤ 3.6·10⁷ · 2 · (342/12¹¹) · 66²⁰e^{−92.4} aE ≤ 10⁻⁵aE` against the core `6·10⁻⁵aE`.

Rank 12 needs a further factor `≈ 4900` (one more power `b²` at `b = 66`): the core floor on `[1, 5]`
is then the bottleneck, not the tail.

## A2

- **Hausdorff.** The atom estimates need `#{|γ| ≤ T} ≤ 0.33 T log T` and `#((6T/5, 7T/5]) ≥ 0.04 T log T`.
  The sharp mass gives both from `T = e¹²` (`band_card_ge_of_exp_twelve_le`), so the shift is
  `⌈20K⌉ + ⌈K H²⌉ + 1`, `K = 10(k+1) + 20`, `H = max(e¹², 42(k+1) + 44K)`, in place of
  `H ≥ xiMassHeight(1/500) ≥ e^{450}`.
- **`windowHeight` (open).** Its size comes from the symbol horizon `T₁ = 4e^{E+2π}`,
  `E = 10 + 68e^{a+2}`, and from Lagrange sampling at zeros of gap `48⁻⁴/(9a)`, which exist only at
  heights `≈ exp(10⁷)`. Any symbol-side argument needs `log(T₁/2π) ≳ 1 + 2Σ_{n ≤ e^{2a}} Λ(n)n^{−1/2}`
  (`≈ 6.9` at `a = 1`). The low-frequency part must then come from zeros, which sample the
  type-`2a` function `|f̂|²` only where their gap is below `π/(2a)`, i.e. above `≈ 2πe^{4a}`.
  A reasonable height needs a Plancherel–Pólya sampling theorem at the zeros with explicit
  frame constants.

## Blocked tasks

- **A1.** The worst-phase Hadamard budget is tight at `67` for band `3` on `Re s = 1`; wider bands
  lose more in the worst-phase polynomial than they gain on the left (`L = 3.5`: left `2.112`,
  worst phase `≈ −0.95`, arch at `75` is `1.248`). Past the Kronecker limit the phases
  `(γ log p)` at the actual heights are needed: Hardy-`Z` signs (`hardySEM`) or phase cells on a grid.
- **A3.** Odd unit window: Lean has `weilQuad F + (3203/320)(∫xF)² ≥ ‖F‖²/1000`. The two-moment
  lower form `firstFoldTwoMomentForm` is `M − K₁ℓ₁² − K₃ℓ₃²` with `M` pointwise: `V(u) =
  κ₀ − ½log(1 − u²)`, `κ₀ = 0.554924`, off the strip, and the blocks `[[V(u), w],[w, V(σu)]]`,
  `w = log 2/√2`, `σu = 2log 2 − u`, on `[2log 2 − 1, log 2]`. It is `≥ 0` iff the Gram matrix
  `Γᵢⱼ = ⟨M⁻¹pᵢ, pⱼ⟩` of `p₁ = u`, `p₃ = P₃` satisfies `Γ ⪯ diag(1/K₁, 1/K₃)`. Quadrature (Simpson off
  the strip, graded steps at the log singularity `σu → 1`): `Γ₁₁ ≈ 0.2294`, `Γ₃₃ ≈ 0.2324`,
  `Γ₁₃ ≈ −0.0442`; margins `1/K₁ − Γ₁₁ ≈ 0.0205`, `1/K₃ − Γ₃₃ ≈ 0.0851`, product `0.00174` against
  `Γ₁₃² ≈ 0.00195`. The form fails by `≈ 11%`; the unused Gamma reserve (`0.0044 E` beyond `E/64`)
  brings it to equality. So no certified quadrature of this form closes the window: a sharper lower
  form is needed first (harmonic gap above level 5 on modes `≥ 7`, higher lags), and its Gram entries
  then need `~0.5%` precision on log-singular integrands. A height-67 route fails too: zero positions
  below 67 are unknown without computation, so they cannot serve as samples.
  `log 2` and `½ log 5` lie far beyond the certified `0.362`.
- **A5.** Exactly, `U_r(b) = ∬_{y₁+y₂>r} e^{ib(y₁−y₂)/2}Φ(y₁)Φ(y₂)`, i.e. `½Ξ̂(b/2)²` plus
  `∫ (sin ωr/ω) Ξ̂(ω + b/2)Ξ̂(ω − b/2) dω/π` up to normalization. At `b = 2γ` the first term vanishes and
  for small `r` the sign is that of the autocorrelation of `Ξ` at lag `2γ`, of size `≈ 10⁻¹⁷` at `γ₄`;
  `U_r` is negative only within `≈ 10⁻⁸` of `2γ`, so a certificate needs a located zero. An explicit
  formula average `Σ_γ g(γ)²(Φ²)^(2γ)` at large height needs the asymptotics of the self-convolution
  of `Ξ` (a mean value of `Z(t+v)Z(t−v)`). At large `r` the kernel tends to `e^{−2πe^r cosh 2t}`, whose
  transform `K_{ib/2}(2πe^r)` changes sign, but the integral over `s > r` may restore positivity.
  No route avoids zero location or deep asymptotics.
- **A6.** Cone widths of `𝒜(c)` at `c > 0.66` and Lévy margins at `½ log 3` are convex-program
  certificates beyond the certified window `0.362`.
- **A7.** On the nine moduli the total kernel `ω + Λ(n)/√n − P` is positive at every point of the
  anti-diagonal (`totalAntiDiagonalKernel_pos_forall_iff`), so no nonnegative gauge pays it; a
  certificate must come from ratio atoms and shared surplus (AIP open question 6); it is ACT open
  question 1 restricted to nine moduli. The finite reading, per-modulus ranges `½log n < r ≤
  ½log n + η_n` of the own-strip payment (`two_mul_primePowerShift_le_stripSurplus`, `η = 1/12` from
  the fold potential `1.9 − η/p − 3η²`), does not globalize: strips share their surplus.
