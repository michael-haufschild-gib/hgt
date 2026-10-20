# SRT explicit-lag loop (goal: 100 significant contributions toward `P_v ≥ 0` for `v ≥ V`)

- **ID:** srt-explicit-lag-1020
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** formal/GaloisForLFunctions/SquareRootThreshold/README.md (research topics 1, 2, 4)
- **Statement:** For `ζ` and one generic width, prove `P_v ≥ 0` for all `v ≥ V` with explicit `V`,
  knowing that every crystal and every finite off-line set has a first negative lag.

## Goal
100 contributions, each meeting one of: (1) explicit unconditional `V`; (2) visibility at
`ζ`-density for a non-attained top with controlled lag; (3) off-diagonal prime pairs at `λ > 1`
with the consequence for `P_v`; (4) exact aperture/height/length tradeoff with the strongest
unconditional estimate; (5) the proof says what replaces the attainment premise of grids.
Not counted: nonselective positivity apertures, invisibility without witness, pair-correlation
restatements.

## Coordination
Other agents work in `SquareRootThreshold/` (window prime polynomial, Stieltjes, zero-count
remainder, ground-energy bridges). Check `ls SquareRootThreshold/` before naming a module. My lane:
effective (finite-window) visibility of the lag family, records, non-attained tops, grids.

## Conjecture queue
1. Finite Laplace windows: `P_v ≥ 0` on `[0, V]` bounds the Laplace pole of every off-line zero
   by the potential of the others (effective Landau inequality; record-potential law).
2. Non-attained tops (chains) seen by the continuum lag family at an explicit lag.
3. `ζ`: companion law at the Legendre record from finite lag positivity, with the corpus
   zero-free region, local count and 6/5 density.
4. Grids: z-transform (Pringsheim) version; the attainment premise replaced by a non-aliasing
   condition at the record.
5. Clusters: Toeplitz/positive-definite version of the Laplace window in the height variable.

## Contribution ledger (append-only)
- **L1 · Finite lag windows: the record-potential law** — `FiniteLagWindowRecordPotentialLaw`.
  Criteria 2, 5. `norm_evenCoeff_mul_lapWin_le`: if the difference family is nonnegative on a
  finite range `[0, V]`, then for every exponent `z₀` and `s = σ + it`,
  `|D(z₀)E_V(z₀−s)| ≤ |M|(|E_V(−σ)|+|E_V(−s)|) + Σ_z|D||E_V(z−σ)| + Σ_{z≠z₀}|D||E_V(z−s)|`,
  `E_V(z) = ∫_0^V e^{zu}du` (`lapWin`), via `|G(σ+it)| ≤ G(σ)` for the Laplace window of the
  nonnegative `φ(0) − φ` (`norm_integral_cexp_mul_le`, `integral_lagWindow_eq`). Effective Landau:
  every exponent is tested, not only the top. `loudness_bound_of_lag_nonneg` /
  `exists_lag_neg_of_loudness`: with `|Im z| ≥ η`, separation `g` from `s`, `κ = 1/η + 1/g`,
  `θ = Re z₀ − σ`, `2κNθ ≤ 1` and loudness ratio `Σ|D|e^{Re z V} ≤ N|D(z₀)|e^{Re z₀ V}`, negativity on
  `[0, V]` once `κN|D(z₀)|(e^{θV} − 2) > 4|M|/σ + κΣ|D|`: first negative lag
  `≤ θ⁻¹ log(2 + (4|M|/σ + κΣ|D|)/(κN|D(z₀)|))`, valid for non-attained tops (the record exists at
  every lag). `zeta_crowding_of_lag_primeWindow_nonneg`: for ζ (η = 4), `P_v ≥ 0` on `[0, V]` forces
  every loud off-line zero to be crowded. What replaces attainment: the loudness ratio at the lag
  itself. Axioms: [propext, Classical.choice, Quot.sound]. Olean built; wired.
- **L2 · Lag grids: the aliasing-potential law** — `LagGridAliasingPotentialLaw`. Criterion 5.
  Grid window `G(ζ) = Σ_{k≤K}(φ(0) − φ(kℓ))ζ^k` has nonnegative coefficients, `|G(ζ)| ≤ G(|ζ|)`;
  termwise `G(e^{−sℓ}) = φ(0)Q_K(e^{−sℓ}) − Σ_z D(z)Q_K(e^{(z−s)ℓ})`, `Q_K(w) = Σ_{k≤K} w^k`
  (`geomWin`, `sum_lagGrid_eq`, `norm_sum_cexp_mul_le`). `norm_evenCoeff_mul_geomWin_le`: grid
  record-potential law. `grid_loudness_bound_of_lag_nonneg` / `exists_grid_lag_neg_of_loudness`:
  distances `|Im z|`, `|z − s|` become aliasing gaps `|1 − e^{(z−σ)ℓ}| ≥ η`, `|1 − e^{(z−s)ℓ}| ≥ g`;
  with `κ = 1/η + 1/g`, `2κN(e^{θℓ} − 1) ≤ 1`, some grid lag `≤ Kℓ` is negative once
  `κN|D(z₀)|(e^{θ(K+1)ℓ} − 2) > 4|M|/(1 − e^{−σℓ}) + κΣ|D|`. What replaces attainment on a grid:
  no loud zero aliases onto the positive real axis or onto the record. C54's hidden chain is
  exactly the case `η → 0` (grid images `e^{δ_n + iθ_n}` accumulate at `e^{1/4}`).
  `zeta_grid_crowding_of_lag_primeWindow_nonneg`: ζ version on prime windows `X = e^{kℓ}`.
  Axioms: [propext, Classical.choice, Quot.sound]. Olean built; wired.
