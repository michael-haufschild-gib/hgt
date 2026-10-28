# Small-time growth of the de Bruijn–Newman nonreal count (Q-II)

- **ID:** heat-count-small-time-growth
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (the three rungs); paper-level REDUCTION (the dictionary below)
- **Source:** `docs/reports/review-2810/obstacles-summary.md` Q-II; receivers in `index-exit-hodge-defect-collision-count`
- **Statement:** As `t ↓ 0`, `N(t) := nonrealZeroCount t ≤ e^{o(1/t)}`, then `N(t) ≤ C t^{−A}`, then `N(t) ≤ C`.

## Goal
`N(t)` bounded is `FiniteOffLine` (`finite_nonreal_zeros_iff_exists_nonrealZeroCount_le`,
`index_exit_first_rung_tfae`, Lean). An effective bound reduces RH to a finite computation.

## Gates
- [x] 0 → 1  in-progress: receivers and tools located in Lean; reduction found (below)
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Current state [Lean]
- `exists_nonrealZeroCount_and_collisionMass_le_interiorLindelof`: `N(t) ≤ C R log R`,
  `R = 2π e^{(27/40+ε)/t}`, so `κ := limsup_{t→0} t log N(t) ≤ 27/40`.
- The constant `27/40` comes from the pointwise horizon threshold `(c − w)² > 4c μ(1/2 + w)` on
  `w ∈ [0, 1/2]`, binding on the chord `μ(1/2) ≤ 1/6`, `μ(5/7) ≤ 1/14`. The Euler anchor needs
  `c > 1/2`, so the pointwise horizon gives at best `e^{(1/2+ε)/t}`, even under Lindelöf.

## The dictionary: the heat count is a zero-density count
Coordinates: a zero `z` of `H_0 = Ξ` has `Im z = β − 1/2`, and the Gaussian average defining `H_t`
at ordinate `x` has its saddle at abscissa `1/2 + w`, `w = t log(x/2π)`.

**Mean-field rate.** A nonreal zero `x + iy` obeys
`ẏ = −2 Σ_{j} (y − y_j)/|z − z_j|²`.
- Its conjugate contributes `−1/y`. This term alone is the energy-transition rate: `y²` drops by
  `2t`.
- The real zeros near `x`, of density `(1/2π) log(x/2π)`, contribute about `−log(x/2π)`.

So depth `δ` at ordinate `x` survives until `t ≈ δ / log x`, and is absorbed once
`t log x > δ`. With `δ < 1/2` this reproduces the sharp horizon `c = 1/2`.

**Claims.** Let `E(σ) := limsup_T log N(σ, T)/log T` be the zero-density exponent.
- **(S) Sufficiency [paper sketch].** `κ ≤ sup_{0<w<1/2} w·E(1/2 + w)`. Proof route:
  - replace the Euler anchor by an interior anchor at `w = t log x`;
  - the small values of `ζ` at the anchor occur near zeros with `β ≥ 1/2 + w − o(1)` (zero density) or on a Dirichlet-polynomial large-deviation set;
  - large values left of the saddle are controlled by mean values (moments) instead of `μ`;
  - sum over dyadic `x`, using `#zeros ≤ x^{E}` at depth `t log x`.
- **(N) Necessity [paper sketch].** `N_off(δ, T) ≤ C log T · N(c δ²/log T)`. Proof route:
  - window energy `Σ_window y²`;
  - pair terms `(y_k − y_j)²/|z_k − z_j|² ≤ 1`, at most `C log x` partners per zero;
  - nonreal zeros are not created forward in time (`nonrealZeroCount_antitoneOn`);
  - so the energy of `k` zeros of depth `≥ δ` lasts until `t ≈ δ²/(C log x)`.

  Consequence: `E(1/2 + δ) ≤ κ/(c δ²)`.

**Rungs translated (S + N).**

| Rung | Equivalent density statement | Known? |
|---|---|---|
| `N(t) ≤ e^{o(1/t)}` (`κ = 0`) | `N(σ, T) = T^{o(1)}` for every `σ > 1/2` | Open; beyond the density hypothesis and beyond Lindelöf (Lindelöf gives only `E ≤ 2(1 − σ)`) |
| `N(t) ≤ C t^{−A}` | `N_off(δ, T) ≤ C (log T/δ²)^{A'}` (polylog off-line density) | Open |
| `N(t) ≤ C` | `FiniteOffLine` | Open; equivalence [Lean] |

**Exponent values under (S)** (`κ ≤ sup_w w E(1/2+w)`):

| Density input | Bound on `κ` |
|---|---|
| trivial `E ≤ 1` | `1/2` (the sharp horizon) |
| corpus power saving `E(1/2+δ) ≤ 1 − δ/40` (`exists_zetaZeroDensity_powerSaving`) | `79/160` |
| Huxley `12/5` | `3/20` |
| Guth–Maynard `30/13` | `15/104` |
| density hypothesis | `1/8` |
| RH | `0` |

## Tool barriers
- **Energy transition** (`riemannHeat_upper_energy_le`):
  - The law is global in the ordinate. Its right side `Σ_ρ ((Im ρ)² − 2t − c)_+` is infinite unless only finitely many zeros have `(Im ρ)² > 2t + c`, so it is vacuous before finiteness.
  - Its rate `2t` is the conjugate self-interaction. The mean-field rate `t log x` is absent.
- **KKL horizon with Lindelöf chords:** pointwise, so the threshold is `c ≥ 1/2` (Euler anchor). It cannot go below `e^{(1/2+ε)/t}`.
- **Quadratic cost** (`resolventIndexCharge_le_packetCharge`):
  - It is a lower bound: `k` right copies cost `≥ 50k² − 3k/2`.
  - Combined with a work bound `W(t)`, it gives `N ≲ √W`. The upper estimate on `W(t)` is the same open problem.
- **Q-II premise is false.** The count is not "dynamical instead of arithmetic". Under (S) + (N) it is the density function `N(1/2 + t log x, x)` summed over `x`.

## Open core
- A sub-power zero-density theorem `N(σ, T) = T^{o(1)}`, `σ > 1/2`. Rung 1 needs it by (N).
- Without it, the reachable improvements are the constant only:
  - `27/40 → 1/2`: large-value counting;
  - `→ 79/160`: corpus density, with (S);
  - `→ 15/104`: Guth–Maynard, with (S).

## Survivors to formalize (not dependency-closed)
- (N), the necessity reduction. It certifies that rung 1 is at least as hard as sub-power density. Needs:
  - zero dynamics of `H_t`, via the polynomial approximants `xiRealApprox` and Hurwitz counting on boxes;
  - uniform local zero counts for `H_s` in unit windows;
  - flux control for a weighted window energy.
- (S), the sufficiency transfer. Needs:
  - interior anchors with small-value control;
  - mean values of `ζ` in the strip.

## Log
- 2026-10-28 — created; dictionary `κ = sup_w w E(1/2+w)` found (paper sketch); rung 1 identified with sub-power density.
