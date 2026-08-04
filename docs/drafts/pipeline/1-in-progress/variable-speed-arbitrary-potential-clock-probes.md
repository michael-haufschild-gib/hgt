# Clock probes for an arbitrary potential on a variable-speed chart

- **ID:** `variable-speed-arbitrary-potential-clock-probes`
- **Stage:** 1-in-progress
- **Type:** CONSTRUCTION / HYPERBOLIC PDE / CLOCKS
- **Parent:** `../2-fully-proven/new_scientific_knowledge/clocks/two-species-conformal-clock-scale-law.md`
- **Predecessor:** `../3-formalized/new_scientific_knowledge/time-dependent-principal-part-clock-probes.md`
  (closed: the variable-speed chart carries probes for the **constant** potential `-m²`, at every
  event, and the two-species scale law holds on its conformal orbit)
- **Status:** open. Target: probes for an **arbitrary** smooth potential on the chart

  ```
  □u = -∂₀²u + c(t)² ∑ᵢ ∂ᵢ²u,      □u + V u = 0.
  ```

## Why the predecessor does not reach it

The predecessor's field is a *free* evolution: fibre by fibre it solves `û'' + ω(t)²û = 0`, which is
diagonal in the frequency. A potential `V(y)` is multiplication in space, hence **convolution in the
frequency**, which couples the fibres. The corpus solves exactly that coupling for the flat chart —
`KleinGordonPotentialFlow.lean` — by a Duhamel/Volterra equation in the Banach space `E →ᵇ ℂ`:

```
û(t) = cos(t⟨ξ⟩)/⟨ξ⟩ · G₀ + ∫₀ᵗ (sin((t-s)⟨ξ⟩)/⟨ξ⟩) · (a_s * û(s)) ds.
```

Both factors of the kernel are bounded by `1` *uniformly in `(t,s)`*, which is what the corpus's
Volterra theory asks for. For a variable speed the free propagator is the Hill flow, whose bounds
carry `e^{K|t-s|}`: bounded on every window, not on the line. So the abstract input has to be
weakened before the construction can be repeated.

## Plan

1. **Windowed Volterra theory** (infrastructure the corpus lacks).
   `VolterraLinearIntegralEquation.lean` assumes `∀ t s, ‖K t s‖ ≤ M` and `∀ t, ‖f t‖ ≤ F`. Replace
   by bounds on `|t|, |s| ≤ T`, one `M(T), F(T)` per window. The cheap route is *not* to redo the
   440-line development: clamp the data to the window (`timeClamp`), observe that the Picard
   iterates at `|t| ≤ T` never look outside it, and transport every conclusion of the global theory
   along that equality.
2. **The two-parameter Hill propagator.** The Duhamel kernel needs the solution started at an
   arbitrary time `s`, not at `0`. Do *not* build it by translating the speed: the base-time
   derivative of a translated flow is painful, and it is not needed. For any fundamental pair the
   propagator is the bilinear combination

   ```
   P(t,s) = S(t)C(s) - C(t)S(s),
   ```

   already separated in the two times and built from the two base-`0` solutions the corpus owns. All
   that has to be added is the Wronskian normalization `CS' - SC' = 1`.
3. **The multipliers.** `hillCoscSymbol t ξ := C(t,ξ)/ω(0,ξ)` and `hillPropSymbol t s ξ := P(t,s,ξ)`
   as elements of `E →ᵇ ℂ`; both bounded on windows, and the free term must carry one power of
   damping — the undamped cosine family is *not* norm-continuous in time (at a fixed time difference
   the sup over frequencies of `|cos(tω) - cos(t'ω)|` is `2`).
4. **The driven flow.** `hillPotentialFlow a G₀ := volterraSolution (free term) (kernel)` with the
   windowed theory, its pointwise Duhamel identity, and the two time derivatives — the second one
   being the equation `∂ₜ²û = -ω(t)²û + (a_t * û)`.
5. **The field equation with a potential**, in the chart: `∂₀²u = c(t)²∑ᵢ∂ᵢ²u - m²u + V u`, where
   `V = kgPotential (a.density t)` — the same realization of the potential as in the flat case, so
   the corpus's `exists_locally_kgChartPotential_of_smooth_spacetime` applies verbatim.
6. **The chart layer and the probes.** Re-run the predecessor's chart calculus for the driven
   density, then `RegularOpenProbes` for an arbitrary smooth potential, and the two-species scale
   law on the conformal orbit with that potential.

## Boundary

The principal part must still be independent of the point. A chart whose principal part varies in
space needs genuine variable-coefficient hyperbolic theory — energy estimates in Sobolev spaces with
commutator terms — of which mathlib has none.

## Progress

### Phase 1 — the windowed Volterra theory: **done**

`formal/GaloisForLFunctions/HTGeometry/VolterraWindowedEquation.lean`:

- `timeClamp`, `volterraClampF`, `volterraClampK` — the data clamped to a window;
- **`volterraIterate_congr_of_window`** — data agreeing on a window give the same Picard iterates
  inside it, because the integral runs between `0` and the time; hence
  **`volterraSolution_congr_of_window`**;
- **`volterraSolution_eq_window`**, **`norm_volterraSolution_le_window`**,
  **`continuousOn_volterraSolution_window`** — every conclusion of the global theory, transported to
  a window on which the data are bounded;
- `VolterraLocallyBounded` and **`volterraSolution_eq_of_locallyBounded`**,
  **`continuous_volterraSolution_of_locallyBounded`** — data bounded on every window, which is what a
  propagator with growing energy supplies.

Nothing of the 440-line global development had to be reproved.

### Phase 2 — the Duhamel calculus and the fundamental pair: **done**

`formal/GaloisForLFunctions/HTGeometry/DuhamelVariableOscillator.lean` — the scalar calculus with an
*abstract* fundamental pair, since a variable frequency has no addition formula:

- `duhamelPairFirstPart`, `duhamelPairSecondPart` — the two moments of the source, with
  `t`-independent integrands;
- `duhamelPair`, `duhamelPairDeriv` and **`hasDerivAt_duhamelPair`** — the first derivative, where the
  two source terms cancel;
- **`hasDerivAt_duhamelPairDeriv`** — the second derivative *is* the driven equation
  `u'' = -ω²u + h`, the source reappearing exactly once, weighted by the Wronskian.

`formal/GaloisForLFunctions/HTGeometry/HillFundamentalPair.lean`:

- `hillCos`, `hillSin` and their velocities — the two canonical solutions;
- `const_of_hasDerivAt_zero` and **`hillWronskian_eq_one`** — the Wronskian is constant along the
  equation and equals one, which is the normalization the Duhamel formula needs;
- `hillProp` — the propagator `S(t)C(s) - C(t)S(s)`, separated in the two times, vanishing on the
  diagonal;
- **`mul_abs_hillSin_massive_le`**, `abs_hillSinDeriv_massive_le`, `abs_hillSin_massive_le` — the sine
  member gains one power of the frequency, its velocity none, both uniformly in the frequency.

`formal/GaloisForLFunctions/HTGeometry/HillPropagatorSymbol.lean` — the propagator read as a symbol:

- `hillPropSymbol`, `hillCoscSymbol` and their derivatives in each time variable;
- `hillSpeedRatio` and **`abs_hillPropSymbol_le`**, **`abs_hillCoscSymbol_le`** — bounded on every
  window of times by `2(max(1, c(0)/c_min)/m)e^{K(|t|+|s|)}`, with **no frequency on the right**;
- **`abs_hillPropSymbolTimeDeriv_le`**, **`abs_hillPropSymbolBaseDeriv_le`**,
  **`abs_hillCoscSymbolDeriv_le`** — and so are both partial derivatives, which is what makes the
  symbol Lipschitz in the times *uniformly in the frequency*: the undamped cosine family is not, and
  that is exactly why the free term carries one power of damping;
- `continuous_hillPropSymbol_freq`, `continuous_hillCoscSymbol_freq` — continuity in the frequency.

Axioms of all of the above: `[propext, Classical.choice, Quot.sound]`.

### What remains

3. Package the symbols as bounded continuous functions and prove joint continuity in the two times
   (mean value theorem with the window constants above).
4. The driven flow, by the windowed Volterra theory, and its pointwise Duhamel identity.
5. The field equation with the potential, in the chart.
6. The chart layer, the probes, and the scale law.
