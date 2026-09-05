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
