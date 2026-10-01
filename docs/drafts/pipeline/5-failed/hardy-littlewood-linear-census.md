# Hardy–Littlewood census: N₀(T) ≫ T/log²T from a window mean square

- **ID:** HL-LINEAR-CENSUS
- **Stage:** 5-failed (superseded)
- **Parent:** `3-formalized/hardy-square-root-census.md` (MUST-615, `N₀ ≫ √T/log²T`); loop cycles 94–95, 101+
- **Target:**
  - **Theorem.** `N₀(T) ≥ c·T/(1+log T)²` for all large `T`, unconditionally.
  - **Key input.** `∫_T^{2T} |∫_t^{t+H} Z(u) du|² dt ≤ C·H·T` for a fixed large `H` and large `T`.

## Census from the window mean square (paper, ready)

- Average over grid offsets `s ∈ [0, H)` to get an offset with `Σ_k |I(T+s+kH)|² ≤ (1/H)·∫|I|² ≤ C·T`.
- Windows without a zero satisfy `∫_W|Z| = |∫_W Z|` (`integral_abs_hardyZ_eq_abs_integral`). They carry at most `√(K·CT) = T√(C/H)`.
- The first moment `∫|Z| ≥ 3T/4` (`exists_le_integral_abs_hardyZ`, shifted range) leaves `≥ T/2` for windows with a zero.
- Cauchy–Schwarz against `∫Z² ≪ T log²T` gives `#windows with a zero ≫ T/(H log²T)`.

## Bricks for the window mean square (plan)

1. **Phase linearization.** `|θ(t+v) − θ(t) − θ'(t)v| ≤ v²·sup|θ''|`, with `|θ''(τ)| ≪ 1/τ`.
2. **Single twisted window integral.** It equals `e^{i(θ(t) − t log m)} g_H(θ'(t) − log m) + O(H³/T)`, where `g_H(r) = (e^{iHr} − 1)/(ir)`, `|g_H| ≤ min(H, 2/|r|)`, `|g_H'| ≤ H²/2`.
3. **Unified AFE.** `Z(τ) = Re(e^{iθ(τ)} Σ_n d_n(τ)(n+1)^{−iτ}) − residue` with
   `d_n(τ) = (n+1)^{−1/2}(cutoff((n+1)/x) + conj W(τ,(n+1)x))`, `x = 2√T`.
   - Source: `hardyZ_eq_two_tsum_smoothAFE_real`.
   - `|∂_τ W| ≤ A/((n+1)x)` (`exists_norm_deriv_smoothAFEZetaDualWeight_le_invScale`).
4. **Block freezing.** Use blocks of length `B = T^{3/4}/H²`. Freezing `θ'(t)` in `g_H` and `t` in `W` costs a total of `≪ x√T + …`, which is `≪ εHT` for `H ≥ 1/ε`.
5. **MVT per block** (`dirichlet_meanValue_theorem`, truncation at `N = x·T^ε`, Gaussian tail). This gives `∫_block |Σ c_m m^{−it}|² ≤ (B + 4N(1+log N)) Σ|c_m|²`.
6. **Resonance sum.** `Σ_m m^{−1}|cutoff + W|²·min(H², 4/log²(N₀/m)) ≤ C·H` with `N₀ = e^{θ'(t_j)} ≈ √(t/2π)`. The near band `|m − N₀| ≤ N₀/H` gives `2H`, the graded band `8H`, the far range `O(1)`.
7. **Assembly.** `∫_T^{2T}|I|² ≤ CHT`.
8. **Census.** As above; `N₀(T) ≫ T/(1+log T)²`.

## Status
- Census lemma (first-moment form) and supporting lemmas: [L] in `R:HardySquareRootCensus`.
- Bricks 1–7: to build.

## Retired (2026-10-01, loop cycle 102): superseded

The pinned dependency `Zeta23` is a sorry-free Lean formalization of "More than two thirds of the zeros of the Riemann zeta function lie on the critical line". Its Theorem D is transported to the corpus as `RHTower.lamzouri_montgomeryTaylor_simpleCritical_epsilon` (`R:LamzouriMontgomeryTaylorXiDensity`). It gives unconditionally `N₀ˢ(T) ≥ (0.6725 − ε)N(T) ≫ T log T`. A census of order `T/log²T` adds nothing. No further work.
