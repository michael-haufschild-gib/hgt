# Off-line first moment of zeta zeros from one mollified mean square

- **ID:** OFFLINE-MOMENT-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/rs-phase-locking-geometric-mean-law.md` §(iii) (the `(L)` gate) ·
  Levinson consumer chain (`LevinsonOddFiberFinal`)
- **Statement:** For every bounded-coefficient real Dirichlet polynomial `Ψ = ∑_{n≤N} b_n n^{-s}`
  with `b_1 = 1`, every abscissa `σ₀ ∈ [1/4, 1/2)` or `σ₀ = 1/2`, and admissible heights
  `20 ≤ T₁ < T₂`, the multiplicity-weighted first horizontal moment of the zeta zeros in
  `[1/2, 15/2] × [T₁, T₂]` obeys
  `2π ∑ m_ρ (Re ρ − 1/2) ≤ ½(T₂−T₁) log( Msq/(T₂−T₁) ) + C + K (log T₂ + log Mb)`,
  where `Msq ≥ ∫_{T₁}^{T₂} |ζΨ(σ₀+it)|² dt`, `Mb ≥ ∑ |b_n| n⁴`, and `C, K` are the absolute
  Littlewood-budget constants of `exists_levinson_mollified_budget_le`.

## Goal
Quantify the `(L)` gate of the Riemann–Siegel phase-locking lane: `(1/T)∫_0^T log|ζ(1/2+it)| dt
→ 0 ⟺ ∑_{γ≤T}(β−1/2)⁺ = o(T)`. By Littlewood's lemma the left side is `2π ∑ (β−1/2)⁺ + O(log T)`,
so an unconditional ceiling on the first moment is an unconditional ceiling on the logarithmic mean
of `|ζ|` on the critical line and on the average displacement of zeros from the line. The theorem
is a *rate* statement (a first moment), not a positivity statement; it is the first-moment reading
of the corpus's Levinson budget, which previously only extracted counts.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof = the Lean proof)
- [x] 2 → 3  formalized: `RHTower.exists_zetaOffLineFirstMoment_le_of_mollified_meanSquare`,
  `RHTower.exists_zetaOffLineFirstMoment_le_of_line_meanSquare`
  (`formal/GaloisForLFunctions/RHTower/ZetaOffLineFirstMomentMollified.lean`, wired after
  `LevinsonOddFiberFinal`; `lake build` green; axioms `propext, Classical.choice, Quot.sound`)
- [ ] 3 → 4  publication-ready

## Proof (as formalized)
1. At `λ = 0` the mollified Levinson detector is `ζ·Ψ`; the corpus budget
   `exists_levinson_mollified_budget_le` bounds `weightedLittlewoodBoundary (ζΨ) σ₀ (15/2) T₁ T₂`
   by `½(T₂−T₁) log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)` (left edge by Jensen, far-right edge
   `O(1)` by Cauchy/decay, horizontal edges by Backlund).
2. The exact weighted Littlewood identity for the entire product `F = (s−1)²ζ·Ψ` on
   `[σ₀, 15/2] × [T₁, T₂]` (`exists_entire_weighted_littlewood_rectangle_allow_left_zeros`) gives
   `2π ∑_{F(w)=0} m_F(w)(Re w − σ₀) = weightedLittlewoodBoundary F`; the pole gauge `(s−1)²`
   contributes exactly zero (`weightedLittlewoodBoundary_poleGauge_mul`).
3. Every zeta zero of `[1/2, 15/2] × [T₁, T₂]` is a zero of `F` in the wider rectangle;
   `m_F = m_ζ + m_Ψ ≥ m_ζ` (`analyticOrderAt_mul`, and `analyticOrderAt ((s−1)²ζ) = analyticOrderAt ζ`
   away from `1`), and `Re w − 1/2 ≤ Re w − σ₀` with all terms nonnegative. The mollifier's own
   zeros are simply dropped.
4. The line version: the mean square `σ ↦ ∫|ζΨ(σ+it)|²` is continuous on `[1/4, 1/2]`
   (`continuous_clamped_meanSquare`), so the abscissa bound with `Msq + ε` holds for `σ₀` close to
   `1/2` and `ε → 0⁺` closes it (`ge_of_tendsto`).

## Corollary on paper (inputs not in Lean: the mollified mean value theorems)
Take `Ψ` the Levinson/Conrey mollifier `b_n = μ(n)P(log(y/n)/log y)`, `P(x) = x`, `y = T^θ`.
Conrey (1989): `(1/T)∫_0^T |ζΨ(1/2+it)|² dt → 1 + 1/θ` for `θ < 4/7`; Levinson (1974): the same
with `θ < 1/2`. Choosing `T₂ ∈ [T, T+1]` with zero-free horizontal edges (finitely many bad
heights) and `T₁ = 20`, the theorem gives, with `S(T) := ∑_{0<γ≤T, β>1/2} m_ρ (β − 1/2)`,

```text
S(T) ≤ (T/4π) · log(1 + 1/θ) + o(T),        i.e.
S(T) ≤ (0.0805 + o(1)) T   (θ = 4/7, Conrey),   S(T) ≤ (0.0874 + o(1)) T   (θ = 1/2, Levinson).
```

Equivalently (Littlewood's lemma, `N(T) ~ (T/2π) log T`):

```text
(1/T) ∫_0^T log|ζ(1/2+it)| dt ≤ ½ log(11/4) + o(1) = 0.5058 + o(1),
average displacement  S(T)/N(T) ≤ (0.5058 + o(1)) / log T  =  0.0805 × (mean spacing 2π/log T).
```

The lower bound `S(T) ≥ 0` is trivial; under RH `S ≡ 0`. `(L)` is the statement `S(T) = o(T)`.
The whole loss of the argument is Jensen's inequality on the left edge: `E log|ζΨ|² ≤ log E|ζΨ|²`
with equality only for a.e.-constant `|ζΨ|`. Farmer's long-mollifier conjecture (`θ → ∞`) would
send the ceiling to `0`, i.e. would prove `(L)`.

## Log
- 2026-09-05 — created directly at stage 3 (Lean-closed); the first-moment reading of the Levinson
  budget; line version by continuity; explicit corollary constants recorded above.

## 2026-09-05 (ii) — the sandwich is two-sided in Lean; the moment route to a better ceiling is closed

**Littlewood's lemma for `ζ` with explicit-constant edges** (`ZetaLineLogMeanLittlewoodBudget`):
`|∫_{T₁}^{T₂} log|ζ(1/2+it)| dt − 2π ∑_{ρ∈[1/2,15/2]×[T₁,T₂]} m_ρ(β − 1/2)| ≤ C + K log T₂`
(`exists_zetaLine_littlewood_edge_budget`; edges from the corpus's far-right Cauchy/decay lemmas
and the Backlund horizontal bound, applied to the trivial mollifier `Ψ ≡ 1`; the pole gauge
cancels exactly). Corollaries: the floor `∫ log|ζ(1/2+it)| ≥ −C − K log T₂`
(`exists_zetaLine_logMean_floor`) and the two-sided sandwich

```text
−(C + K log T₂) ≤ ∫_{T₁}^{T₂} log|ζ(1/2+it)| dt ≤ ½(T₂−T₁) log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)
```

(`exists_zetaLine_logMean_sandwich`) for the critical-line mean square `Msq` of any admissible
`ζΨ`. With Conrey's mean value: `0 ≤ liminf, limsup (1/T)∫_0^T log|ζ(1/2+it)| ≤ 0.5058`.

**Jensen's loss cannot be recovered from mean values** (`JensenGapSecondMomentNoGo`): for every
variance `v > 0` and `ε > 0` there is a two-point law with mean `1`, second moment `1 + v`, and
Jensen gap `log E Y − E log Y < ε` (`exists_twoPoint_mean_one_variance_jensen_gap_lt`; bulk at
`1 − a`, spike at `1 + v/a` with probability `a²/(v+a²)`). Since the mollified second and fourth
moments of `ζΨ` are exactly the mean and variance of `Y = |ζΨ|²/E|ζΨ|²`, no twisted second or
fourth moment theorem can lower the ceiling; an eighth moment, a small-ball law, or a limiting
distribution for `ζΨ − 1` (heuristically complex Gaussian with variance `1/θ`, which would give
`E log|ζΨ|² → E₁(θ)`, i.e. ceiling `≈ 0.24` at `θ = 4/7`) is required.

## 2026-09-05 — the on-line count retained: an explicit `(L)` constant below Jensen

**Lean** (`RHTower/ZetaOffLineFirstMomentLineCount`, axiom-clean, wired):
`exists_zetaOffLineFirstMoment_add_lineCount_le_of_mollified_meanSquare` — same hypotheses as the
ceiling, conclusion strengthened to
`2π[∑_{ρ ∈ [1/2,15/2]×[T₁,T₂]} m_ρ(Re ρ − 1/2) + (1/2 − σ₀)∑ m_ρ] ≤ ½(T₂−T₁)log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)`.
Littlewood on `[σ₀, 15/2]` charges every zero with `Re ρ ≥ 1/2` the full `Re ρ − σ₀`; the ceiling
had dropped the `(1/2 − σ₀)` part.

**Paper corollary (Levinson line `σ₀ = 1/2 − R/log T`).** With the mollifier normalized on the
line (Young, *A short proof of Levinson's theorem*, Thm 1, `Q = 1`, `P(x) = x`):
`c(R,θ) = 1 + (1/θ)·(e^{2R}−1)/(2R)·((1+Rθ)³−1)/(3Rθ)` (Conrey 1989 for `θ < 4/7`), and
`∑ m_ρ = (N + N₀)/2 ≥ (1+κ)N/2` by the functional-equation symmetry, `N ~ (T/2π)log T`:

```text
∑_{T<γ≤2T}(β−1/2)⁺ ≤ (T/4π)[log c(R,θ) − (1+κ)R] + o(T)      for every R > 0.
```
At `θ = 4/7`, `κ = 2/5` (Conrey), `R = 0.6`: `log 5.678 − 0.84 = 0.897`, i.e. `0.0714 T`
(`0.0706 T` with `κ = 0.417`), against the Jensen ceiling `log(11/4)/4π = 0.0805 T`; equivalently
`(1/T)∫_T^{2T} log|ζ(1/2+it)| ≤ 0.449` (was `0.506`). The recipe engine reproduces Conrey's `c` to
first order in `R` and the pod calibration at `T = 10⁶` matches to the expected `O(R/log T)`.

**Trade-off law.** The same inequality couples the proportion `κ_T = N₀/N` and the mass
`m_T = 4π∑(β−1/2)⁺/T`: `m_T + (1+κ_T)R ≤ log c(R,θ)` for all `R`. Under RH (`κ = 1, m = 0`) it is
consistent (`2R ≤ log c(R,θ)`); it cannot refute anything. Long mollifiers (`θ → ∞`, Farmer) give
`m ≤ (1 − 3κ²/4)/θ → 0`, i.e. `(L)`, with the `R`-term improving Jensen's `1/θ` by the factor
`1 − 3κ²/4`.

**Verdict on `(L)`.** Unsolved. Moments (any finite set, with the Gaussian head and orthogonality)
are inert for the log-mean: the Jensen-tight coupling `W = √(1+σ²)e^{iα} − 1` with `α` partially
locked to `arg H` satisfies every such constraint. Dips at on-line zeros give `E log⁻|ζΨ|²` lower
bounds, but unconditionally the constants are killed by possible zero clustering (Fujii's pair
bound allows every zero a neighbour within `1/log T`). The only remaining unconditional lever is
the shifted-line count above; pushing the constant to `0` needs `p_T(a) := N(1/2 + a/log T, T)/N(T)
→ 0` for fixed `a`, beyond all known zero-density technology (Selberg: `≪ e^{−a/4}`). The 2025
preprint claiming almost all zeros on the line is unverified and would give a count, not a mass.

## 2026-09-05 — zero density at the mean-spacing scale (`p_T(a)` cycle)

**Lean** (`RHTower/ZetaZeroDensityMeanSpacingScale`, axiom-clean, wired):
`exists_zetaZeroDensity_scale_le_of_mollified_meanSquare` — for every `Δ ≥ 0`,
`2π[Δ·∑_{Re ρ ≥ 1/2+Δ} m_ρ + (1/2−σ₀)∑_{Re ρ ≥ 1/2} m_ρ] ≤ ½(T₂−T₁)log(Msq/(T₂−T₁)) + C + K(log T₂+log Mb)`;
`expIntegralE1_le_exp_neg_div` — `E₁(x) ≤ e^{−x}/x`.

**Paper.** With `p_T(a) := N(1/2 + a/log T, T)/N(T)`:
* Levinson line (`σ₀ = 1/2 − R/log T`, `Δ = a/log T`, Young/Conrey `c(R,θ)`, `∑ m_ρ ≥ (1+κ)N/2`):
  `p_T(a) ≤ [log c(R,θ) − (1+κ)R]/(2a) ≤ 0.449/a` (θ=4/7, κ=2/5) — the Chebyshev form of the mass bound.
* Right-shifted line (`σ₀ = 1/2 + a'/log T`, mollifier coefficients `h^{−σ₀}`, twisted second
  moment for `θ < 17/33`): recipe value `c_lin(a',θ) = 1 + (1 − e^{−2a'})(1 − e^{−2a'θ})/(4a'²θ²)`
  (`c − 1 ≈ 1/(4a'²θ²)`: the head `∑_{k≤M}Λ(k)²k^{−1−2a'/L}/log²M` decays only polynomially), so
  `p_T(a) ≤ log c_lin(a',θ)/(2(a − a'))`, e.g. `a' = a − 1`: `p_T(a) ≲ 0.38/(a−1)²` at `θ = 4/7`.
* Exponential decay needs a sharp-head mollifier (`P ≡ 1` on `[0,1−ε]`): the head vanishes by
  Möbius inversion, the tail gives `c − 1 ≍ e^{−2θa'(1−ε)}/ε`, and Littlewood yields
  `p_T(a) ≪ e^{−2θa}` — this is exactly Conrey's exponent `8/7 = 2·(4/7)`: the density exponent
  at the mean-spacing scale is twice the admissible mollifier length (Selberg `1/4 = 2·1/8`,
  Jutila `→ 1`, Conrey `8/7`). The recipe engine's sharp-taper run was unreliable (negative values
  at `ε = 1/4`) and is not used.

**Why `p_T(a) → 0` is out of reach for this family.** Every bound above is Jensen on a mean
square: it charges `log(1 + h)` where `h = E|ζG(σ₀+it)|² − 1 > 0` is a fixed constant for fixed
`a, θ`. The true log-mean of a Gaussian deviation of variance `h` is `E₁(1/h) ≤ h e^{−1/h}`
(Lean), so the mean-square method loses the factor `e^{−1/h}`, the small-value probability, and
can never see that a positive proportion `h` of the window carries no zero. Recovering it needs the
distribution of `ζG − 1` on the line `1/2 + a/log T` (a mollified CLT), i.e. the long-mollifier
frontier again (`θ → ∞`); at fixed `θ` no second-moment argument gives `p_T(a) → 0`.

## Explicit Conrey-exponent density at the mean-spacing scale (2026-09-05)

**Right-shifted lines in Lean.** The corpus budget `exists_levinson_mollified_budget_le` carried the
hypothesis `σ₀ < 1/2`, but its proof only needs `σ₀ < 15/2`; `LevinsonMollifiedBudgetWide.lean`
is the same proof with `1/4 ≤ σ₀ < 2` (`exists_levinson_mollified_budget_le_wide`). On top of it,
`ZetaZeroDensityRightShiftedLine.lean` proves
`exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide`: for every mollifier datum
`(b, N, Mb)` with the mean-square input `∫_{T₁}^{T₂} |ζΨ(σ₀+it)|² dt ≤ Msq`, every `Δ ≥ 0`, and
`Z` the zeros of ζ in `[1/2, 15/2] × [T₁, T₂]`,

    2π · Δ · Σ_{ρ ∈ Z, Re ρ ≥ σ₀ + Δ} m_ρ ≤ ½(T₂−T₁) log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb).

(Littlewood's lemma for `ζΨ` on `[σ₀, 15/2] × [T₁, T₂]`; every zero with `Re ρ ≥ σ₀ + Δ` is charged
at least `Δ`; the `(1/2 − σ₀)`-term of the on-line count disappears since `σ₀ > 1/2` is allowed.)
Axioms: `propext, Classical.choice, Quot.sound`.

**The sharp-head taper.** With `P_ε(x) = min(1, x/ε)` (unit head `P(1) = 1`, `P(0) = 0`) the Möbius
mollifier `Ψ = Σ_{h ≤ y} μ(h) P_ε(log(y/h)/log y) h^{−s}` of length `y = T^θ` has, on the line
`σ₀ = 1/2 + a/L` (`L = log T`), the mean square (Conrey's main term, ratios/CFZ recipe, pod-checked)

    c_tap(a, θ, ε) = 1 + (e^{2aεθ} − 1)(1 − e^{−2a}) e^{−2aθ} / (4 a² ε² θ²)
                   ≈ 1 + e^{−2θ(1−ε)a} / (4 ε² θ² a²),

against the linear mollifier's `c_lin(a,θ) = 1 + (1 − e^{−2a})(1 − e^{−2aθ})/(4a²θ²)` (polynomial
decay: its head never dies). The exponential rate `2θ(1−ε)` is the density exponent of the method;
the `1/(ε²a²)` prefactor is the price of the sharp head.

**Explicit density.** Taking `σ₀ = 1/2 + a'/L`, `Δ = (a−a')/L`, `Msq = c_tap(a',θ,ε)(T₂−T₁)(1+o(1))`
and dividing by `N(T) ∼ (T/2π) L`:

    p_T(a) := N(1/2 + a/L, T)/N(T) ≤ inf_{a' < a, ε ∈ (0,1)} log c_tap(a',θ,ε) / (2(a − a')) + o(1).

Numerical optimum (θ = 4/7): the bound behaves as `(2.40 + o(1)) e^{−8a/7}`, attained at
`a' ≈ a − 0.9`, `ε ≈ 1.2/a`:

| a | taper bound | linear bound | Chebyshev 0.449/a | bound / e^{−8a/7} |
|---|---|---|---|---|
| 3 | 7.2e−2 | 7.6e−2 | 1.50e−1 | 2.21 |
| 5 | 7.9e−3 | 1.9e−2 | 9.0e−2 | 2.38 |
| 8 | 2.6e−4 | 5.0e−3 | 5.6e−2 | 2.40 |
| 12 | 2.7e−6 | 1.5e−3 | 3.7e−2 | 2.40 |

For `a ≤ 2` the Chebyshev/linear bounds are as good; the taper wins from `a ≈ 3`.

**Honesty.** (i) The one external input is Conrey's mean-value theorem for the mollified square
with a Lipschitz `P` and the shifted weight `h^{−a'/L}` (both of Conrey's shape; the kink of `P_ε`
is smoothed at no cost in the main term). (ii) The exponent `8/7 = 2·(4/7)` is Conrey's; what is
new is the explicit constant at the mean-spacing scale and the Lean skeleton on right-shifted lines
(the corpus previously only had the Levinson-line count, `σ₀ < 1/2`). (iii) `p_T(a) → 0` at fixed
`a` — the sharpened form of `(L)` — is untouched (CANNOT-300): the charge `log c` is a fixed
positive number for every fixed `a'`, and only the mollifier length moves the exponent.

Files: `formal/GaloisForLFunctions/RHTower/LevinsonMollifiedBudgetWide.lean`,
`formal/GaloisForLFunctions/RHTower/ZetaZeroDensityRightShiftedLine.lean` (both wired in
`RHTower.lean`); pod scripts `shifted_general.py` (taper kernel), `density_const.py` (optimisation).
