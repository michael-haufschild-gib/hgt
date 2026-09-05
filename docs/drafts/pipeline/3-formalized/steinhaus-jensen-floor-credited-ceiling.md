# The credited ceiling and the Steinhaus Jensen floor (MUST-211 attack)

**Status:** stage 3 (Lean, unconditional for the flow theorems; the floor is a torus-model theorem).
**Date:** 2026-09-05. **Parent:** `1-in-progress/outer-law-mollified-product.md` (OUTER-001),
`3-formalized/zeta-off-line-first-moment-mollified-ceiling.md`.

## 1. The task and the verdict

MUST-211 asked for the torus log-mean of `Ψ_{T^θ}` uniformly in `M`, by transporting the peeling
identity `E_z log|A + zB| = log max(|A|, |B|)` from the Steinhaus torus to the flow
`t ↦ (p^{-it})_p`. The identity is corpus-owned (`circleAverage_log_norm_const_add_mul`,
`SteinhausTorusLogMean.lean`). The transport fails structurally:

* For a prime `p > √M`, `Ψ = A_p + p^{-s} B_p` with `A_p, B_p` free of `p`. Peeling needs `A_p, B_p`
  frozen while `p^{-it}` completes one period (`Δt ≈ 2π/log p`), but the spectra of `A_p, B_p`
  are `{log n : n ≤ M}`, reaching `log M ≥ log p`: no separation of scales. Kronecker times at
  which the other phases return are `exp(π(M))`, far beyond `T`.
* Distributional transfer at length `T^θ` reaches only moments of order `< 1/θ` (Montgomery–Vaughan
  diagonal range). Beyond it the flow carries swap terms (the corpus `c₄(θ)`), and the resonant
  Fourier modes `n/(n+1)` of `log|Ψ_M(z)|` with `n ≤ T` smooth have positive density `ρ(1/θ)`.
* A uniform torus law for `log|Ψ_{T^θ}|` is itself a Steinhaus transfer of a log-mean at length
  `T^θ`; `(L)` is the same statement for `log|ζ|` at length `T`.

**Verdict: BRIDGE** (between two transfer statements), with a correction to MUST-211: the lower torus
law is free up to `J_M` because `exists_edPoly_line_logMean_floor` is `T`-free, the upper law is
not needed, and the `(L)`-productive statement is the mollified upper bound
`ℓ_{ζΨ_{T^θ}}(T)/T ≤ o(1)`, which equals `(L) ∧ RZM_flow(Ψ_{T^θ}) = o(T)` — strictly stronger.

## 2. Positive survivors (Lean)

### 2.1 The credited ceiling (`ZetaOffLineFirstMomentMollifierCredit.lean`)

Littlewood's identity for `F = (s−1)²ζΨ` charges every zero of `F`; the corpus ceiling kept only
`ζ`'s. With `ord_F = ord_ζ + ord_Ψ` (`analyticOrderAt_mul`):

    2π [Σ_ζ m_ρ (Re ρ − ½) + Σ_Ψ m_w (Re w − ½)] ≤ ½(T₂−T₁) log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)

(`exists_zetaOffLineFirstMoment_add_mollifierZeroMass_le_of_mollified_meanSquare`; sums over the
zeros in `[½, 15/2] × [T₁, T₂]`, mean square on `σ₀ ∈ [¼, ½)`).

### 2.2 Littlewood for the mollifier, upper direction (`MollifierLineLogMeanZeroMass.lean`)

    ∫_{T₁}^{T₂} log‖Ψ(½+it)‖ dt ≤ 2π Σ_Ψ m_w (Re w − ½) + C + K log Mb

(`exists_edPoly_line_logMean_le_zeroMass`, `T`-free constants). With the floor lemma: the line
log-mean of a Dirichlet polynomial *is* its right-zero mass up to `O(log Mb)`.

### 2.3 The log-mean-credited ceiling

    2π Σ_ζ m_ρ (Re ρ − ½) + ∫_{T₁}^{T₂} log‖Ψ(½+it)‖ dt ≤ ½(T₂−T₁) log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)

(`exists_zetaOffLineFirstMoment_add_mollifierLogMean_le_of_mollified_meanSquare`). Read per unit
length with `Msq = c·(T₂−T₁)`: `(1/T)Σ_ζ(β−½)⁺ ≤ (1/2π)[½ log c − ℓ_Ψ/T] + o(1)`. Hence:

> **(L) criterion.** `(L)` follows from any mollifier family with
> `½ log E_flow|ζΨ|² − E_flow log|Ψ| → 0`, i.e. a vanishing flow Jensen gap of `ζΨ` (the gap
> equals `½ log E|ζΨ|² − E log|ζΨ|` since `E log|ζΨ| = E log|ζ| + E log|Ψ|` and `E log|ζ| ≥ −o(1)`).

### 2.4 The Steinhaus Jensen floor (`SteinhausTorusJensenFloor.lean`)

For continuous `Ψ` of the first `k₀` phases, radii `0 ≤ r_j < 1` on `k₀ + m` phases, `ε > 0`,
`E_r(z) = ∏_j (1 − r_j z_j)⁻¹`, `B = ∏_{j<k₀}(1 − r_j)⁻¹`:

    2 J_ε(Ψ) + Σ_{j≥k₀} log (1 − r_j²)⁻¹ ≤ log ( E‖E_r Ψ‖² + ε² B² ∏_{j≥k₀} (1 − r_j²)⁻¹ )

(`torusJensenFloor`; `J_ε(Ψ) = E ½ log max(‖Ψ‖², ε²)`). Ingredients: the torus mean square
factorizes over the large coordinates, one Poisson integral `⨍_{|z|=1} ‖1 − rz‖⁻² = (1 − r²)⁻¹` per
coordinate (`torusAverage_normSq_eulerAmp_restrict`, `circleAverage_inv_normSq_one_sub_mul`);
Jensen for the torus average (`torusAverage_log_max_le`); the corpus identity `E log‖E_r‖ = 0`;
a globally continuous clamp `eulerAmpSafe` of the Euler amplitude so that the torus-average
calculus (`torusAverage_add'`, `torusAverage_mono'`, `continuous_torusSlice`) applies.

**Meaning.** With `r_j = p_j^{-1/2}`, primes `≤ M` in the head and `M < p ≤ T` in the tail: for
*every* mollifier of the primes `≤ M = T^θ`,

    ½ log E|ζΨ|² − J(Ψ) ≥ ½ Σ_{M<p≤T} log (1 − 1/p)⁻¹ ≈ ½ log(1/θ),

with equality iff `|ζ_{≤M} Ψ|` is a.s. constant. The credited ceiling is floored by the
large-prime energy. At `θ = 4/7`: floor `0.28` against the present constant `½ log(1+1/θ) = 0.506`;
the credit can gain at most `½ log(1+θ) = 0.226`, and the linear mollifier (`J_M ≈ 0.005`) gains
nothing. The method reaches `(L)` only as `θ → 1`, the wall of `κ → 1` and Farmer, now with a
structural cause: the primes in `(M, T]` are independent of every function of the primes `≤ M`.

## 3. Honesty

* 2.1–2.3 are unconditional flow theorems; the constants are the corpus budget constants.
* 2.4 is a theorem about the Steinhaus torus; its arithmetic reading assumes the torus model of
  `|ζ|` on the line, which is exactly what `(L)` is about. The floor is therefore a statement about
  what the *method* can prove, not about `ζ`.
* No new external input; the only computation was none (the constants above are closed forms).

## 4. Files

`formal/GaloisForLFunctions/RHTower/{MollifierLineLogMeanZeroMass, ZetaOffLineFirstMomentMollifierCredit, SteinhausTorusJensenFloor}.lean`, all wired in `RHTower.lean`;
axioms `propext, Classical.choice, Quot.sound`. STATUS: CANNOT-301, F676, F677, MUST-213.

## 5. The proposed exit through the swap terms (2026-09-05, later): closed

Proposal: compute the flow Jensen gap of `ζΨ_{T^θ}` with the recipe's exact fourth moment
`c₄(θ) = 1 + 8/(3θ) + 2/θ² + 2/(3θ³)` (swap terms included) and test whether it falls below the
torus floor `½ log(1/θ)`.

**Answer: no, and no computation can change it.** The sup of `E log X` over laws with prescribed
`E X = m₁` and `E X² = m₂ > m₁²` equals `log m₁`: the two-point laws with mass `1−p` at
`m₁ − pd` and mass `p` at `m₁ + (1−p)d`, `d = √(v/(p(1−p)))`, have these moments and log-mean
`≥ log m₁ − 2√(pv/(1−p))/m₁ → log m₁` (`exists_twoPoint_logMean_ge`, Lean). Jensen is saturated
by rare large values, exactly what heavy swap tails produce; Lyapunov makes every higher moment a
weaker bound. So the fourth moment carries no information about the log-mean, and the swap terms
enter the ceiling only through the mean square `c(θ) = 1 + 1/θ`, where flow and torus agree.

**The flow Jensen gap, exactly.** By the outer decomposition and Littlewood for `ζ` and for `Ψ`
(F676),

    G_flow(θ) = ½ log c(θ) − (2π/T)[Σ_ζ(β−½)⁺ + Σ_Ψ(β−½)⁺] + O(log T / T).

It is below the torus floor iff the total right-zero mass of `ζΨ` exceeds `½ log(1+θ)·T/2π`
(`0.226·T/2π` at `θ = 4/7`). The corpus numerics (`E log|ζΨ|² ≈ 0`, `J_M ≈ 0.005`) put that mass
near `0`: `G_flow ≈ G_torus ≈ 0.506 > 0.28`.

**What would lower the gap.** Only the lower tail: `P_flow(|ζΨ(½+it)| < ε)`, governed by zeros of
`ζ` near the line, i.e. by `Σ_γ |ζ'(ρ)|^{-1}`-type negative moments (Gonek), or by fractional
negative moments `E|ζΨ|^{-2α}`, `α < ½` (then `E log X ≥ −α⁻¹ log E X^{-α}`). Neither is
unconditional. STATUS: CANNOT-302, F678.

## 6. The lower tail (2026-09-05, last): the local Jensen deficit, evaluated and closed

Correction to §5's closing proposal: `E log|ζΨ|² ≥ −O(log T/T)` is Littlewood's identity, so the
lower tail cannot pin the gap from below. What it can do is the reverse. Every zero `½ + iγ` of
`ζ` on the line is a zero of `F = ζΨ`; Poisson–Jensen on the disc `D(½ + it₀, a/L)` (`L = log T`)
gives, for `|t − t₀| < a/L`,

    log|F(½+it)| = (1/2π)∫ P(t; φ) log|F(½ + it₀ + (a/L)e^{iφ})| dφ − Σ_{ρ∈D} G_D(½+it, ρ).

Integrating in `t` over the chord, then in `t₀` over `[T, 2T]`, every `t` is covered with weight
`2a/L`; the boundary term becomes the Poisson line weight
`w(φ) = π|cos φ| − 2 + sin φ log((1+sin φ)/(1−sin φ))` (`(1/2π)∫ w = 2`) against `log|F|` on the
circle, which Jensen bounds by the `w`-weighted circle average of the shifted mean squares
`c_fix(a cos φ, θ)`; and each on-line zero contributes the averaged Green mass

    ∫_{-1}^{1}∫_{-1}^{1} log((1−uv)/|u−v|) du dv = 2∫₀¹ ((1−v²)/v) log((1+v)/(1−v)) dv
      = 8 Σ_{k odd} 1/(k²(k+2)) = π²/2 − 2 = 2.9348.

Result (unconditional, same inputs as the ceiling plus the on-line proportion `κ`):

    Σ(β−½)⁺ ≤ (T/4π) [ log C̄(a,θ) − κ a (π²/2 − 2)/(2π) ] + o(T),
    C̄(a,θ) = (1/4π) ∫₀^{2π} w(φ) c_fix(a cos φ, θ) dφ,
    c_fix(x,θ) = 1 + (1 − e^{−2x})(1 − e^{−2xθ})/(4x²θ²).

Because the disc is symmetric the cost is second order in `a` while the deficit is first order, so
there is always a gain over plain Jensen; numerically (`θ = 4/7`, `κ = 0.4`):

| method | bound |
|---|---|
| Jensen on the line | 0.0805 T |
| local deficit, discs on the line, `a = 0.30` | 0.0783 T |
| Levinson-line credit (corpus) | 0.0714 T |
| discs centred on the Levinson line, `R = 0.20, a = 0.22` | 0.0769 T |

The deficit of a zero at relative offset `x` from the disc centre, `γ(x)/γ(0)`, is
`0.58, 0.29, 0.10, 0.02` at `x = 0.25, 0.5, 0.75, 0.9`, so discs on the Levinson line credit the
on-line zeros too weakly to pay for the exponentially growing left-of-line mean square: stacking
loses. Verdict: INSIGNIFICANT as an `(L)` tool (CANNOT-303); not formalised. A uniform small-ball
law would need Gonek-type negative discrete moments and zero-spacing control at scale `1/log T`
(MUST-214).

## 7. Littlewood weights classified (2026-09-05): the Levinson shift is optimal

Green's identity for `u = log|F|`, `F = ζΨ`, on a domain `Ω ⊇ {critical line}` with
`φ = G_Ω(·, line measure)` (`Δφ = −2π·μ_line`, `φ = 0` on `∂Ω`, `β = −∂_nφ ≥ 0`):

    ∫_line log|F| dt = (1/2π) ∫_{∂Ω} log|F| β dσ − Σ_{ρ∈Ω} φ(ρ).

Special cases: right half-plane `{x > −R}` (`x = (σ−½) log T`): `φ = 2π min(x+R, R)`, `β = 2π` on
`σ₀` — Littlewood on `[σ₀, ∞)`, i.e. the Levinson shift; disc `D(½+it₀, a/L)` averaged over `t₀`:
the chord potential (§6); strip `{−R < x < R'}`: `φ = 2π(R+x)R'/(R+R')` for `x < 0`,
`2π(R'−x)R/(R+R')` for `x > 0`, `β_left = 2πR'/(R+R')`, `β_right = 2πR/(R+R')`.
Bound: `Σ(β−½)⁺ ≤ (T/4π)[log E_β c − credit]`, `E_β c` the balayage-weighted mean of the line mean
squares `c(x)`, credit `= κ φ̂/π + (off-line pair credit)`.

Why the half-plane wins:
1. Translation invariance is forced (otherwise only `min_t φ(0,t)` can be credited), so `Ω` is a
   half-plane or a strip.
2. Off-line pairs `(ρ, 1−ρ̄)` are credited only when the right member's credit is capped and
   offset-independent (half-plane: `2πR`); in a bounded symmetric domain the pair credit is
   `2φ̂ − 2πx` and keeping it cancels the off-line mass identically.
3. The left half-plane is excluded: the boundary term at `−∞` carries the functional-equation
   growth `∂_σ log|F| ≈ −log t`.
4. `log c(−x) = log c₀ + x + c₂x² + …` (slope exactly `1`, `c₂ = 0.426`): half-plane net
   `κR/2 − c₂R²/2`, symmetric strip `κρ/2 − (c₂+½)ρ²/2`, disc `0.093a − O(a²)`.

| weight (θ = 4/7, κ = 0.4, fixed coefficients) | bound |
|---|---|
| Jensen on the line | 0.0805 T |
| half-plane, R = 0.46 (Levinson shift) | 0.0732 T (0.0714 T renormalised) |
| symmetric strip, ρ = 0.22 | 0.0771 T |
| asymmetric strip, R = 0.20, R' = 0.25 | 0.0770 T |
| disc, a = 0.30 | 0.0783 T |

Verdict: the Littlewood-weight lever is exhausted (CANNOT-304). Together with CANNOT-300–303 the
whole mollified-Littlewood family is closed at `0.0714T` up to the mollifier profile.
