# Card 2 (spectral terminal-horizon model) — what is built and what is left

## Built and compiling (namespace `GaloisForLFunctions.HTGeometry.Interfinity`)

* `SpectralHorizonCocycle.lean` — `laplaceCochain V s = exp(-(V s)) - 1`, `laplaceMul`,
  `laplaceCochain_add` (cocycle), `abs_laplaceCochain_le`,
  `integrableOn_laplaceCochain_sq` (item 1, needs `β > -2`),
  `eq_one_of_isPrimitive`, `isCoboundary_iff` (Hilbert coboundary iff `β > 0`),
  `observerLine`, `deathCut`, `stableRegion`, `mem_stableRegion_iff`,
  `deathCut_add` (horizon width `= max 0 (-β/2)`), `deathCut_eq_iff`.
* `SpectralFinitePart.lean` — `ChartFun` (continuous on `[0,1]`, bounded, linear modulus at 0),
  `ChartFun.ofContDiff`, `ChartFun.transport`, `integrableOn_chart_mul_rpow`,
  `integrableOn_chart_sub_mul_rpow`, `integrableOn_source_pairing`, `rpow_succ_split`.
* `SpectralPrimitiveIdentity.lean` — `finitePart` (three branches), `sourcePairing`,
  `finitePart_transport_sub` (**the primitive identity (6)**),
  `finitePart_transport_of_pos`, `tendsto_transported_finitePart` (stability for `a > 0`).
* `SpectralCutObstruction.lean` — `ChartFun.const`, `cutIntegral`, `cutIntegral_le`,
  `tendsto_cutIntegral_atBot`, `finitePart_const_transport`,
  `not_tendsto_finitePart_of_nonpos` (**no stable primitive for `a ≤ 0`**).

Card 2 items 1, 2 and 3 are therefore complete.

## Left

### item 4a — fixed subspace of the multiplication semigroup is `ℂ δ₀`
The paper argument needs two facts that are hard in Lean:
1. **smooth division**: `φ_V(s) = s/(e^{-Vs} − 1)` (value `−1/V` at `0`) is smooth and nowhere
   zero on `[0,1]`;
2. **Hadamard**: a smooth `h` with `h 0 = 0` is `s · r` with `r` smooth.
Both are *false-free but nontrivial*.  Note the statement is **false for merely continuous test
functions** (the ideal `(e^{-s}−1)·C⁰` is strictly smaller than `{g : g 0 = 0}`), so the test class
must have the Hadamard property.  Cheapest honest route found so far: take the test class to be
**real-analytic** germs on a neighbourhood of `[0,1]`, where both facts follow from power-series
shifts and `AnalyticAt.div` (nonvanishing denominator).  Alternative: build Hadamard for `C^∞` via
`r s = ∫₀¹ h' (t s) dt` plus differentiation under the integral (heavy).

### item 4b — deficient asymptotics (9)
Needs `Γ(a) = ∫₀^∞ (e^{-t} − 1) t^{a-1} dt` for `−1 < a < 0` (integrate by parts from
`Γ(a) = Γ(a+1)/a`), then `V^a T_V η_a → c Γ(a) δ₀`; the `a = 0` line needs
`∫₀^V (e^{-t} − 1)/t dt = −(log V + γ) + o(1)`.

### item 5 — complex time
Sectorial `γ(a,z) → Γ(a)` uniformly on closed subsectors of `Re z > 0`, `R^a T_z η_a →
c Γ(a) e^{-i a θ} δ₀`, phase slope `∂_θ arg = −a = 𝔡_β − ρ`, and the logarithmic contact law at
`a = 0`.
