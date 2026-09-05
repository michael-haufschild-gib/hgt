# The single-input explicit (L) constant

**Status:** stage 3 (Lean, unconditional modulo the two mean-square gates, which are instances of
one theorem type). **Date:** 2026-09-05. **Parents:** `3-formalized/zeta-off-line-first-moment-mollified-ceiling.md`,
the corpus Levinson consumer chain (`LevinsonOddFiberFinal`, `LevinsonOddFiberDensity`).

## 1. Statement

`eventually_offLineMoment_le_of_gates` (`SingleInputOffLineMomentConstant.lean`): for `κ₀ ≥ 0`,
`R > 0`, `c₁, c₂ ≥ 1`, `δ > 0` with `κ₀ + 2δ < 1 − log c₂/R`, and `η > 0`,

    ZetaMollifiedMeanSquareGate R c₁ → LevinsonMeanSquareGate R c₂ →
    ∀ᶠ V, 4π · offLineMoment V ≤ (log c₁ − (1 + κ₀) R + η) · V,

where `offLineMoment V = Σ_{box ξ-zeros, Im ≤ V} m_ρ (Re ρ − ½)`. The gates say: for every
`ε > 0` and all large `U` there is a window `[T₁,T₂] ⊆ [20,U]`, `T₂ > U−1`, a real unit-head bounded
mollifier of the corpus class, and `σ₀ = ½ − R/log T₂`, with the mean square of `ζΨ`
(respectively `(ζ+λζ')Ψ`) on `σ₀` at most `(c+ε)(T₂−T₁)`. Taking `κ₀ ↑ 1 − log c₂/R`:

    limsup (1/V) Σ_{Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (log c₁ + log c₂ − 2R) / (4π).

## 2. Bricks

1. **Credited line-count ceiling** (corpus, `exists_zetaOffLineFirstMoment_add_lineCount_le_of_mollified_meanSquare`):
   `2π[Σ_Z m(Re−½) + (½−σ₀)Σ_Z m] ≤ ½(T₂−T₁) log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)`, `Z` the
   ζ-zeros in `[½,15/2] × [T₁,T₂]`.
2. **Census bridges** (`OffLineMomentCensusBridge.lean`): `rightHalfOrderSum T = Σ_{0<Im≤T, Re≥½} m`
   satisfies `2·rightHalfOrderSum = xiPosZeroCount + xiPosCriticalZeroCount` (reflection
   `window_identity` with `xi_orderAt_lineReflect`); `xiOddFiberCount ≤ xiPosCriticalZeroCount`;
   `rightHalfOrderSum T₂ − rightHalfOrderSum T₁ ≤ Σ_Z m` and
   `offLineMoment T₂ ≤ offLineMoment T₁ + Σ_Z m(Re−½)` (ξ/ζ zero and order equality in the strip).
3. **Levinson's proportion at an arbitrary target** (`LevinsonOddFiberDensityGeneral.lean`,
   `eventually_oddFiber_ge_of_gate_general`): the corpus density proof with `1/3` replaced by `κ₀`;
   the only bound it uses is `κ₀ + δ ≤ 1` (from `κ₀ + 2δ < 1 − log c₂/R ≤ 1`), with the slack
   `η ≤ 1/40` and `1 + η ≤ 41/40` in the coefficient lemma.
4. **Riemann–von Mangoldt** (corpus, `exists_xiZeroCount_close`, `xiPosZeroCount_eq_xiZeroCount`).
5. **Window arithmetic** (`offLineMoment_window_arith`): with `w = ½−σ₀`, `wL = R`,
   `S ≥ (1+κ₀+δ)N(T₂)/2 − N(T₁)`, `M(T₂) ≤ M(T₁) + M_Z`, `N(T₂) ≥ (1/2π − ε')T₂L`:
   `4π M(T₂) ≤ T₂(lc − R(1+κ₀+δ)(1−2πε')) + 12KL + 2C + 4πM(T₁) + 4πR N(T₁)/L`.
6. **Filter assembly**: `ε = c₁η/8` (so `log(c₁+ε) ≤ log c₁ + η/8`), `ε' = η/(16πR(2+κ₀+δ))`,
   `log =o(id)` for the `12K log T₂` term, `T₂B ≤ (U−1)B + |B|`, monotonicity of the moment from
   `U−1` to `T₂`, and the shift `V = U − 1`.

## 3. Reading

With the paper values at `θ = 4/7`, `R = 0.6`: `log c₁ = 1.735` (Young's formula, `P = x`, `Q = 1`),
`log c₂ = 0.36` (Levinson detector, `κ = 0.4`): `(1.735 + 0.36 − 1.2)/(4π) = 0.0712`, the corpus
constant. The formula `(log c₁ + log c₂ − 2R)/(4π)` shows the structure: each mean square costs its
log, the shift is credited twice (once per input), and by the slope law (F679) both logs grow
with slope `1` at `R = 0`, so the net first-order gain is exactly the second input's deficit.

## 4. Honesty

* The gates are hypotheses. Their content is Conrey's twisted mollified mean square on the
  Levinson line for `θ < 4/7`, in the two instances `Q = 1` and Levinson's `Q`; the corpus does not
  own it (MUST-212). Everything else is unconditional Lean.
* The proportion brick is the corpus proof reparametrised; it is not new mathematics.
* Axioms: `propext, Classical.choice, Quot.sound` for every declaration.

Files: `formal/GaloisForLFunctions/RHTower/{OffLineMomentCensusBridge, LevinsonOddFiberDensityGeneral, SingleInputOffLineMomentConstant}.lean`, all wired in `RHTower.lean`. STATUS F680.
