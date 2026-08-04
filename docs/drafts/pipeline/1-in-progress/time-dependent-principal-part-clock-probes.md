# Clock probes for a time-dependent principal part

- **ID:** `time-dependent-principal-part-clock-probes`
- **Stage:** 1-in-progress
- **Type:** CONSTRUCTION / HYPERBOLIC PDE / CLOCKS
- **Parent:** `../2-fully-proven/new_scientific_knowledge/clocks/two-species-conformal-clock-scale-law.md`
- **Status:** open. The probe layer of the parent card covers the conformal orbit of the flat chart
  and the conformal orbit of every foliated chart. This card attacks the next class: charts whose
  principal part depends on the time coordinate but not on the point, with an **arbitrary** smooth
  potential — which the foliation route does not reach, because its probes are constant along the
  leaves and therefore only see potentials that are functions of the leaf label.

## The construction

For `g = -dt² + c(t)²δ` the wave operator is Fourier-diagonal in the spatial variable, so the field
splits frequency by frequency into the Hill oscillator

```
û'' + ω(t)²û = 0,     ω(t) = √(m² + c(t)²|ξ|²).
```

(The massless case `ω = c·|ξ|` is the same equation with `m = 0`; the massive frequency is the one a
clock species actually has, and it is the one treated below.)

Two facts make a synthesis possible, and both are now proved.

**The energy is controlled by the frequency alone.**
`formal/GaloisForLFunctions/HTGeometry/HillOscillatorEnergy.lean`:

- `hillEnergy`, `hillEnergy_nonneg` — the energy `u'² + ω²u²`;
- **`hasDerivAt_hillEnergy`** — `E' = 2ωω'u²`: the oscillator terms cancel against the equation, so
  the energy moves only with the frequency;
- **`hillEnergy_le_of_logDeriv_le`** — Grönwall: `|ω'| ≤ Kω` gives `E(t) ≤ E(a)e^{2K(t-a)}`;
- **`abs_deriv_le_of_scaled`** — for `ω = c·s` the scale cancels in `ω'/ω`, so **one constant serves
  every frequency**. This uniformity is the whole point: a synthesis over all frequencies needs a
  bound that does not degrade as `|ξ| → ∞`.

**The oscillator exists for all time.**
`formal/GaloisForLFunctions/HTGeometry/HillEquationSolution.lean`:

- `hillField`, `norm_hillField_le`, `continuous_hillField` — the first-order system and its bound;
- `hillFlow`, `hillFlow_eq`, `hillFlow_zero`, `hasDerivAt_hillFlow` — the corpus's Volterra series
  (no smallness: each iteration integrates one more power of the time variable) applied to the
  system, then the fundamental theorem of calculus;
- `hillSolution`, `hillSolutionDeriv`, `hasDerivAt_hillSolution`,
  **`hasDerivAt_hillSolutionDeriv`** — the scalar oscillator with prescribed position and velocity;
- **`hillEnergy_hillSolution_le`** — a global solution carrying the frequency-uniform energy bound.

Axioms of all the above: `[propext, Classical.choice, Quot.sound]`.

**The bounds the synthesis consumes.**
`formal/GaloisForLFunctions/HTGeometry/HillOscillatorBounds.lean`:

- `abs_deriv_le_sqrt_hillEnergy`, `mul_abs_le_sqrt_hillEnergy` — `|u'| ≤ √E` and `ω|u| ≤ √E`;
- `sqrt_hillEnergy_le`, **`abs_hillSolutionDeriv_le`**, **`mul_abs_hillSolution_le`** — the same with
  the Grönwall factor `e^{K(t-a)}` in place of the energy;
- `hillEnergy_cos_zero`, `hillEnergy_sin_zero` — the initial energies of the two canonical data,
  `ω(0)²` and `1`;
- **`mul_abs_hillSolution_cos_le`** — for the datum `(1,0)`, `ω(t)|u(t)| ≤ ω(0)e^{Kt}`, so the
  oscillator is bounded by the frequency *ratio* `ω(0)/ω(t) = c(0)/c(t)`, which does not see the
  frequency at all;
- **`mul_abs_hillSolution_sin_le`** — for the datum `(0,1)`, `ω(t)|u(t)| ≤ e^{Kt}`: the oscillator
  decays like one power of the frequency, which the initial datum has to supply.

**The massive frequency.**
`formal/GaloisForLFunctions/HTGeometry/HillMassiveFrequency.lean`:

- `massiveFreq`, `massiveFreq_pos`, `massiveFreq_sq`, `continuous_massiveFreq`, `massiveFreq_sq_le`
  — the frequency `√(m² + c(t)²s²)` of a massive species, positive and bounded;
- **`hasDerivAt_massiveFreq`** — `ω' = c c' s²/ω`, by differentiating the square root;
- **`abs_deriv_massiveFreq_le`** — `|ω'| ≤ (|c'|/c)·ω`: the mass and the spatial frequency drop out,
  because `c²s² ≤ ω²` absorbs exactly the factor the derivative produces. The Grönwall constant is
  that of the speed alone;
- **`hillEnergy_massive_le`** — hence the massive oscillator inherits the energy bound with a
  constant that sees neither the mass nor the spatial frequency.
- `massiveFreq_le_mul` — the frequency ratio between two times is bounded by the ratio of the
  *speeds*, whatever the mass and the spatial frequency;
- **`abs_hillSolution_massive_cos_le`** — hence, for the datum `(1,0)`,

  ```
  |û(t,ξ)| ≤ max(1, c(0)/c(t)) · e^{Kt}
  ```

  with no mass and no frequency on the right. This is the statement the synthesis needs: the
  fibrewise solutions stay bounded uniformly over all spatial frequencies, so the family keeps the
  weight of its initial datum.
- **`abs_hillSolutionDeriv_massive_cos_le`** — the velocity costs exactly one power,
  `|∂ₜû| ≤ ω(0)e^{Kt}`;
- **`abs_hillSolutionSecond_massive_cos_le`** — the acceleration costs exactly two,
  `|∂ₜ²û| ≤ ω(t)²·max(1, c(0)/c(t))·e^{Kt}`, since it *is* the equation evaluated on the uniform
  bound.

So the fibrewise package the synthesis differentiates — value, velocity, acceleration — is complete,
each with its frequency cost made explicit.
- **`norm_hillFlow_massive_sub_le`**, **`continuousAt_hillFlow_massive`** — two massive fibres differ
  by the estimate of the speeds alone (the mass cancels from `ω₁² - ω₂² = c²(s₁² - s₂²)`), so the
  fibre is continuous, hence measurable, in the spatial frequency. The earlier continuity result was
  for the massless family `ω = c·s`; this is the one the massive synthesis uses.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## Next

1. ~~Convert the energy bound into pointwise bounds~~ — done, see above. The remaining weight
   bookkeeping is which initial datum the synthesis uses: the `(1,0)` family costs nothing in
   frequency, the `(0,1)` family costs one power.
2. Package the fibrewise solutions as a curve in the corpus's weighted Wiener space. The
   measurability half is now in hand:
   `formal/GaloisForLFunctions/HTGeometry/HillFlowFrequencyDependence.lean` proves
   **`norm_hillFlow_sub_le`** — two Hill flows started at the same datum and run with different
   frequencies satisfy

   ```
   ‖y₁(t) - y₂(t)‖ ≤ gronwallBound 0 M (δ‖y₀‖e^{Mb}) t,     δ = sup |ω₁² - ω₂²|,
   ```

   by Grönwall applied to the difference, splitting `A₁y₁ - A₂y₂ = A₁(y₁-y₂) + (A₁-A₂)y₂` and using
   `norm_hillField_sub_le` for the second term and the corpus's Volterra size bound for `‖y₂‖`. The
   flow is therefore Lipschitz in the squared frequency on every compact time interval. Specialized
   to the family that matters, `ω = c·s`:

   - **`norm_hillFlow_scaled_sub_le`** — two scales `s₁, s₂` bounded by `S` give
     `‖y_{s₁}(t) - y_{s₂}(t)‖ ≤ gronwallBound 0 (max 1 (C²S²)) (C²|s₁²-s₂²|‖y₀‖e^{Mb}) t`;
   - **`continuousAt_hillFlow_scaled`** — hence the flow is continuous in the frequency scale at
     every point, so the fibrewise solution is measurable in the frequency.

   What remains of this step is only the bookkeeping that turns that into a `WienerFamily`.
3. Differentiate the synthesis twice under the integral, as in the constant-coefficient case, and
   land in `RegularOpenProbes` for the chart `-dt² + c(t)²δ`. The frequency density itself is now
   built — `formal/GaloisForLFunctions/HTGeometry/HillSynthesisDensity.lean`:

   - `hillDensity`, `hillDensityDeriv` — the fibrewise oscillator (and its velocity) times the
     initial density;
   - `continuous_hillDensity`, `aestronglyMeasurable_hillDensity` — continuous, hence measurable, in
     the frequency;
   - **`norm_hillDensity_le`** — dominated by the initial density times `max(1,c(0)/c(t))e^{Kt}`,
     a factor with no frequency in it: the fibrewise bound holds for each frequency with its own
     existence constant, and the right-hand side never mentions that constant, so one function
     dominates every fibre;
   - `norm_hillDensityDeriv_le`, `massiveFreq_zero_le` — the velocity density costs the weight
     `ω(0) ≤ m + c(0)‖ξ‖`, one power;
   - **`integrable_of_hillDensity_bound`** — hence integrability of the density at every time from
     integrability of the datum.

   And the first derivative of the synthesis is taken —
   `formal/GaloisForLFunctions/HTGeometry/HillSynthesisField.lean`:

   - `hillSynthesis`, `hillSynthesisDeriv` — the integral of a bounded character against the density,
     and against the velocity density; leaving the character arbitrary covers every point of space at
     once;
   - `hasDerivAt_hillDensity` — the fibre is differentiable in time;
   - **`hasDerivAt_hillSynthesis`** — the synthesis is differentiable in time with derivative the
     synthesis of the velocity density, by the parametric-integral theorem. Its hypotheses are
     exactly the estimates of the previous files: measurability in the frequency, the fibrewise
     derivative, and a dominating function `(m + c(0)‖ξ‖)e^{Kb}‖G₀(ξ)‖` valid on a whole ball of
     times.
   - `hillDensitySecond`, `hillSynthesisSecond`, `hasDerivAt_hillDensityDeriv`,
     `norm_hillDensitySecond_le` and **`hasDerivAt_hillSynthesisDeriv`** — the same one level up: the
     velocity synthesis is differentiable in time with derivative the synthesis of
     `-ω(t)²û`, dominated by `(m² + C²‖ξ‖²)·max(1,c(0)/c_min)·e^{Kb}·‖G₀(ξ)‖`. The lower bound
     `c_min > 0` on the speed is what makes the ratio `c(0)/c(r)` uniform over the time interval.

   The spatial side is taken too —
   `formal/GaloisForLFunctions/HTGeometry/HillFieldSpace.lean`:

   - `hillEvolutionField` — the field is the corpus's `kgSynthesis` of the Hill density, so the
     corpus's spatial machinery applies verbatim: it is stated for an *arbitrary* density, and
     nothing about the evolution has to be repeated;
   - **`integrable_weight_mul_hillDensity`** — the density inherits every weighted integrability of
     the datum, with a frequency-independent constant; this is where the earlier domination enters;
   - **`hasDerivAt_hillEvolutionField_dir`**, **`hasDerivAt_deriv_hillEvolutionField_dir`** — the
     first and second spatial derivatives, each costing one power of the frequency through the
     factor `2πi⟪ξ,v⟫`.

   And the two halves meet —
   `formal/GaloisForLFunctions/HTGeometry/HillFieldEquation.lean`:

   - **`hillDensitySecond_symbol`** — the multiplier of the second time derivative *is* the spatial
     multiplier plus the mass: `-(m² + c(t)²‖ξ‖²) = (c(t)²/(2π)²)(-4π²‖ξ‖²) - m²`;
   - **`hillSynthesisSecond_eq`** — hence, integrating, the synthesis of the second-derivative
     density equals `(2π)⁻²c(t)²` times the sum of the second spatial directional derivatives over an
     orthonormal basis, minus `m²` times the field. That is the field equation
     `∂ₜ²u = (2π)⁻²c(t)²Δu - m²u`, at the level of the integrals representing both sides.

   And read back through the derivatives —
   `formal/GaloisForLFunctions/HTGeometry/HillFieldTimeEquation.lean`:

   - `hillSynthesis_kgChar` — the synthesis against the character *is* the field, definitionally;
   - **`hasDerivAt_hillEvolutionField_time`** — the field is differentiable in time;
   - **`hasDerivAt_deriv_hillEvolutionField_time`** — its second time derivative is
     `(2π)⁻²c(t)²·(∑ᵢ ∂²_{eᵢ}) - m²` applied to the field. The statement is now about the field
     itself, which is what a probe interface consumes.

   Toward the nonvanishing, the estimates now run in both time directions —
   `formal/GaloisForLFunctions/HTGeometry/HillEnergyTwoSided.lean`:

   - **`hillEnergy_le_of_logDeriv_le_neg`** — the Grönwall bound for negative times, obtained by
     reversing the time variable *in the energy function alone*: the differential inequality
     `|E'| ≤ 2KE` is invariant under `t ↦ -t`, so no uniqueness or reversal statement about the flow
     is needed;
   - **`hillEnergy_le_abs`** — hence `E(t) ≤ E(0)e^{2K|t|}` for every `t`.

   and the fibrewise bounds follow it —
   `formal/GaloisForLFunctions/HTGeometry/HillBoundsTwoSided.lean`:

   - `sqrt_hillEnergy_le_abs` — the square root of the energy, bounded by `√E(0)·e^{K|t|}`;
   - `hillEnergy_massive_le_abs` — the same for the massive fibre;
   - **`abs_hillSolution_massive_le_abs`** — `|û(t,ξ)| ≤ max(1, c(0)/c(t))·e^{K|t|}` for *every* time,
     still with no mass and no frequency on the right;
   - **`abs_hillSolutionDeriv_massive_le_abs`** — `|∂ₜû| ≤ ω(0)e^{K|t|}`, one power, for every time.

   and so does the stability in the frequency —
   `formal/GaloisForLFunctions/HTGeometry/HillFlowTwoSidedStability.lean`:

   - **`norm_hillFlow_sub_le_neg`**, **`norm_hillFlow_sub_le_abs`** — the comparison of two flows
     backward in time, and hence for every time with `|t|`, by the same reversal trick applied to the
     difference;
   - **`continuousAt_hillFlow_massive_all`** — the massive fibre is continuous in the spatial
     frequency at *every* time, which is the form the synthesis needs on a two-sided neighbourhood of
     an event.

   and the density statements follow —
   `formal/GaloisForLFunctions/HTGeometry/HillDensityTwoSided.lean`:

   - **`norm_hillDensity_le_abs`**, **`norm_hillDensityDeriv_le_abs`** — the density and velocity
     density bounds at *every* time, with `|t|` in the exponential and the same frequency costs;
   - **`continuous_hillDensity_all`**, `aestronglyMeasurable_hillDensity_all`,
     **`integrable_hillDensity_all`** — continuity, measurability and integrability with the `0 ≤ t`
     hypothesis gone;
   - **`hillDensity_zero`** — the fibre starts at `1`, so the density starts at the initial density;
   - **`hillEvolutionField_zero`** — hence the field starts at the *plain synthesis* of its datum.

   The last one is where the nonvanishing will come from: the corpus's constant-coefficient
   construction already supplies data whose plain synthesis does not vanish at a prescribed point, so
   the same data serve here, and continuity of the field near `t = 0` does the rest.

   and both are now proved —
   `formal/GaloisForLFunctions/HTGeometry/HillFieldContinuity.lean`:

   - `continuous_hillDensity_time` — the fibre is continuous in time;
   - **`continuousAt_hillEvolutionField`** — the field is continuous in the time and the point
     *together*, by dominated convergence: the dominating function is the same for all nearby times
     because the speed is bounded below, which is exactly what the hypothesis `c ≥ c_min > 0` buys;
   - **`eventually_hillEvolutionField_ne_zero`** — hence a datum whose plain synthesis does not vanish
     at a point gives a field that does not vanish on a whole neighbourhood of that event.

   So the analytic construction is complete for the chart `-dt² + c(t)²δ`: a field solving the
   equation, twice differentiable in time and space, nonvanishing near a prescribed event. In the
   real form the chart layer consumes —
   `formal/GaloisForLFunctions/HTGeometry/HillRealField.lean`:

   - `hillRealField` — the real part of the synthesis;
   - **`hasDerivAt_hillRealField_time`**, **`hasDerivAt_deriv_hillRealField_time`** — both time
     derivatives, since the real part is a continuous linear map and commutes with them;
   - **`eventually_hillRealField_ne_zero`** — nonvanishing near the event, from a datum whose plain
     synthesis has nonzero real part.

4. The chart-level packaging. Begun in
   `formal/GaloisForLFunctions/HTGeometry/HillChartField.lean`:

   - `hillChartField` — the field read as a function of the event, time `y 0` and point
     `kgSpatial d y`;
   - **`eventually_hillChartField_ne_zero`** — it does not vanish near an event on the initial slice
     whose datum has a nonvanishing real synthesis there. The transport is a composition with a
     continuous map, so the neighbourhood produced in `ℝ × E` pulls back to a neighbourhood of the
     event.

   - `add_smul_single_eq_update` — moving along a coordinate direction is updating that coordinate;
   - **`hillChartField_add_smul_single_zero`**, **`hillChartField_add_smul_single_succ`** — along the
     time axis the chart field moves only its time argument; along a spatial axis it moves its point
     by `s(2π)⁻¹` in the corresponding direction. These are the transport identities the
     `coordPartial` computations consume.

   The time-derivative theorems, which had been proved only on `0 < t < b`, now hold everywhere —
   `formal/GaloisForLFunctions/HTGeometry/HillSynthesisTwoSided.lean`:

   - **`hasDerivAt_hillSynthesis_all`** — the synthesis is differentiable in time at *every* time, the
     dominating functions on the unit ball around `t` being the ones at `|t| + 1`;
   - **`hasDerivAt_hillEvolutionField_time_all`**, **`hasDerivAt_hillRealField_time_all`** — hence so
     are the field and the real field.

   This matters for the chart: an event is an arbitrary point of spacetime, not one on or after the
   initial slice, so every downstream statement had inherited the interval restriction.

   What remains: the coordinate partials themselves (from the transport identities and these
   derivatives), then `IsC1OnPi` and the second partials, matching the chart's wave operator against
   the equation, and landing in `RegularOpenProbes`. The fibrewise estimates this step
   consumes are now proved (value, velocity, acceleration, with costs `0`, `1`, `2` powers of the
   frequency); what is left is the dominated-convergence bookkeeping of the corpus's synthesis
   layer, which is written for the constant-coefficient propagator and has to be re-run with these
   bounds in place of the explicit `sin`/`cos` symbols.
4. Then the two-species scale law on that chart, and its conformal orbit by the existing transfer.

## Boundary

The class attacked here is still special: the principal part must not depend on the point. A chart
that is neither conformally flat nor foliated and whose principal part varies in space needs genuine
variable-coefficient hyperbolic theory — energy estimates in Sobolev spaces with commutator terms —
of which mathlib has none. That is the next barrier after this card, not this card.
