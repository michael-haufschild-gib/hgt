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

### Phase 3 — the speed as a datum, and the multipliers: **done**

`formal/GaloisForLFunctions/HTGeometry/HillSpeedData.lean` — the structure `HillSpeed` bundling the
mass, the speed, its derivative and the four estimates, with every symbol bound of the previous file
restated as a method, the window constants `propSize`, `propLip`, `coscSize`, and the fundamental
pair of a fibre (`wronskian_freq`, the four `hasDerivAt_*_freq`, `coscSymbol_zero`).

`formal/GaloisForLFunctions/HTGeometry/HillPropagatorMultiplier.lean`:

- `propBCF`, `coscBCF` — the symbols as bounded continuous functions of the frequency, with
  `norm_propBCF_le_window`, `norm_coscBCF_le_window`;
- **`norm_propBCF_sub_time_le`**, **`norm_propBCF_sub_base_le`**, **`norm_coscBCF_sub_le`** — the
  mean value theorem applied on the window, with the frequency-free derivative bounds, gives sup-norm
  Lipschitz estimates in each time variable;
- **`continuous_propBCF`** (jointly in the two times), `continuous_propBCF_time`,
  `continuous_propBCF_base`, **`continuous_coscBCF`**.

A trap worth recording: `Continuous.comp` of the joint statement with `s ↦ (t, s)` **times out** on
these bounded-continuous-function types (200000 heartbeats, `isDefEq`); the one-variable statements
have to be proved directly from the Lipschitz estimate, which is instant.

### Phase 4 — the driven flow: **done**

`formal/GaloisForLFunctions/HTGeometry/HillPotentialFlow.lean`:

- `hillDuhamelKernel`, `hillFreeTerm` — the propagator followed by convolution with the transform of
  the potential, and the damped free term, with their window bounds and joint continuity;
- **`locallyBounded_hillDuhamel`** — the data are bounded on every window, which is exactly the
  hypothesis of the windowed Volterra theory;
- `hillPotentialFlow` and **`continuous_hillPotentialFlow`**, **`hillPotentialFlow_eq`**,
  `hillPotentialFlow_zero` — the evolution exists on the whole line, solves the Duhamel equation, and
  starts at the datum damped by one power of the frequency;
- `hillFlowSource`, **`hillPotentialFlow_apply_eq_duhamel`** — at a fixed frequency the evolution is
  the Duhamel solution of the driven Hill oscillator, written with that fibre's fundamental pair;
- **`hasDerivAt_hillPotentialFlow_apply`** and **`hasDerivAt_hillFlowApplyDeriv`** — hence the fibre
  is twice differentiable and solves

  ```
  ∂ₜ²û(t,ξ) = -ω(t,ξ)² û(t,ξ) + (a_t * û(t,·))(ξ)
  ```

  at every frequency and every time.

Axioms of all of the above: `[propext, Classical.choice, Quot.sound]`.

### Phase 5a — the window bounds of the driven evolution: **done**

`formal/GaloisForLFunctions/HTGeometry/HillDrivenFlowBounds.lean`:

- `hillFlowSize` and **`norm_hillPotentialFlow_le_window`** — the Volterra exponential bound with the
  window constants of the kernel;
- `hillSourceSize`, **`norm_hillFlowSource_le_window`** — the source, bounded uniformly in the
  frequency;
- `hillVelocitySize`, `norm_duhamel_velocity_part_le` and
  **`norm_hillFlowApplyDeriv_le_window`** — the velocity of the evolution, bounded on every window
  *uniformly in the frequency*. Each term of the Duhamel velocity pairs a velocity of the fundamental
  pair with the other member, and that product is a speed ratio: the frequency cancels. This is the
  domination the synthesis layer differentiates under.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### Phase 5b — the field and its wave equation: **done**

`formal/GaloisForLFunctions/HTGeometry/HillDrivenField.lean`:

- `hillDrivenDensity`, `hillDrivenDensityDeriv`, `hillDrivenDensitySecond`, `hillDrivenField` — the
  weighted density of the driven evolution, its two time derivatives and the synthesis;
- measurability of the velocity density with no joint continuity, via the corpus's
  `aestronglyMeasurable_deriv_param`;
- `norm_kgChar_mul_hillDrivenDensityDeriv_le`, `norm_kgChar_mul_hillDrivenDensitySecond_le` — the
  dominating functions, `⟨ξ⟩⁻ᴺ` times a window constant, and `⟨ξ⟩²⟨ξ⟩⁻ᴺ` times another;
- **`hasDerivAt_hillDrivenField`**, **`hasDerivAt_deriv_hillDrivenField`** — both time derivatives
  taken under the frequency integral.

`formal/GaloisForLFunctions/HTGeometry/HillDrivenWave.lean`:

- `hillDrivenDensitySecond_eq` — the second density splits into the frequency multiplier and the
  source;
- **`hillFreq_symbol`** — `-ω(t,ξ)²` is the speed squared times the spatial multiplier, minus the
  mass;
- **`integral_kgChar_mul_freq_sq`** — hence the synthesis of the frequency part is the spatial
  Laplacian term minus the mass term (stated for an arbitrary density, so it is reusable);
- `weighted_hillFlowSource_eq`, **`integral_kgChar_mul_weighted_source`** — the synthesis of the
  source is the potential times the field, by the corpus's convolution theorem;
- **`hillDrivenField_wave_equation`** —

  ```
  ∂ₜ²u = (2π)⁻²c(t)² ∑ᵢ ∂²_{eᵢ} u - m²u + V(x)·u,      V = kgPotential (b.density t),
  ```

  at every event, for an arbitrary admissible density. This is the analytic heart of the card: the
  variable-speed wave equation *with a potential*.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### Phase 6a — the chart calculus of the driven field: **done**

The corpus's `kgChartOf` and its two derivative lemmas are generic in the density family, so the
whole chart layer is an instantiation. Continuity of the partials in the event does *not* go through
continuity in the frequency — the velocity density is only known to be measurable there — but through
`continuous_kgSynthesis_event`, which asks for continuity in time and a window bound instead.

`formal/GaloisForLFunctions/HTGeometry/HillDrivenChart.lean`:

- `hillDrivenChartField`, `hillDrivenChartTimePartial`, `hillDrivenChartSpacePartial`,
  `hillDrivenChartPartial`;
- the three time-continuity lemmas at a fixed frequency and the three window bounds in the
  `A · ⟨ξ⟩⁻ᴺ` form the instrument consumes;
- `continuous_kgChartOf_of_bound` — the chart-level form of the dominated-convergence instrument;
- **`hasDerivAt_hillDrivenChartField_update`**, **`continuous_hillDrivenChartPartial`**,
  **`isC1OnPi_hillDrivenChartField`**, **`hasFDerivAt_hillDrivenChartField`**,
  **`coordPartial_hillDrivenChartField`**.

`formal/GaloisForLFunctions/HTGeometry/HillDrivenChartSecond.lean`:

- `kgFreq_pow_mul_inv_pow_le`, `inv_pow_le_inv_pow` — one weight `⟨ξ⟩⁻ᴷ` with `N = K + 2` dominates
  every density of the second-order calculus, since the frequency is at least one;
- the three second-order window bounds at that weight, and the integrability of the derived
  densities;
- `hillDrivenChartTimeSecond`, `hillDrivenChartSpaceSecond` and the four
  **`hasDerivAt_hillDrivenChart*Partial_*`**, with the two mixed objects literally equal;
- **`continuous_hillDrivenChartTimeSecond`**, **`continuous_hillDrivenChartSpaceSecond`**,
  **`isC1OnPi_hillDrivenChartTimePartial`**, **`isC1OnPi_hillDrivenChartSpacePartial`**,
  **`differentiableAt_coordPartial_hillDrivenChartField`** — the hypothesis of the divergence-form
  d'Alembertian.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### Phase 6b — the wave operator on the chart: **done**

`formal/GaloisForLFunctions/HTGeometry/HillDrivenChartWave.lean`:

- `hillDrivenChartPotential` — the potential of the convolving family, read on the event;
- `coordPartial_coordPartial_hillDrivenChartField_zero`, `..._succ` — the coordinate second
  derivatives are the second-order families;
- `hillDrivenChartSpaceSecond_eq` — the spatial one is the rescaled directional integral;
- **`hillDrivenChartField_wave_identity`** —

  ```
  ∂₀²u = c(y₀)² ∑ᵢ ∂ᵢ²u - m²u + V(y)·u
  ```

  the real parts costing nothing on the first two terms and the reality of the family
  (`IsRealFamily`) on the third;
- **`solvesPotentialWave_hillDrivenChartField`** — hence `□u + (V - m²)u = 0` for the wave operator
  `hillWaveOp d c` of the predecessor card.

### Phase 6c — the probes: **done** for events of the initial slice

`formal/GaloisForLFunctions/HTGeometry/HillDrivenProbeDatum.lean`:

- `kgBumpReal`, `kgBumpBCF`, `hillDrivenProbeDatum` — the corpus's symmetrised bump, modulated by the
  conjugate character at the chosen point;
- `hillDrivenStartWeight` and **`integral_hillDrivenStartWeight_pos`** — the evolution starts at the
  datum damped by the weight and by one power of the frequency, so the field at time zero is the
  integral of a nonnegative function which is at least one on a ball: positive (support argument,
  `integral_pos_iff_support_of_nonneg`);
- **`hillDrivenField_zero_apply`**, **`hillDrivenChartField_event_pos`**.

`formal/GaloisForLFunctions/HTGeometry/HillDrivenClockProbe.lean`:

- **`exists_localProbesOn_hillDrivenChart`** — the corpus's local-probe interface for the dressed
  potential of a real family;
- `potential_eqOn_of_hillDrivenProbes` — those probes determine the potential on their region;
- **`exists_localProbesOn_hillWaveOp_smooth`** — **clock probes for a variable speed and an
  arbitrary smooth potential**, on a neighbourhood of any event of the initial slice. The potential
  is realized as the chart potential of a real convolving family by the corpus's
  `exists_locally_kgChartPotential_of_smooth_spacetime` — the same realization as in the flat case —
  and the driven field of that family is the probe.

Axioms: `[propext, Classical.choice, Quot.sound]`.

### What remains

6d. Probes at *every* event, by shifting both the speed and the convolving family in time
    (`hillSpeedShift` and the corpus's `WienerFamily.timeShift`, whose potential transforms by
    `kgChartPotential_timeShift`), then `OpenProbes` / `RegularOpenProbes` and the two-species scale
    law on the conformal orbit of the speed chart with an arbitrary potential.
