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
û'' + ω(t)²û = 0,     ω(t) = c(t)·|ξ|.
```

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
   land in `RegularOpenProbes` for the chart `-dt² + c(t)²δ`.
4. Then the two-species scale law on that chart, and its conformal orbit by the existing transfer.

## Boundary

The class attacked here is still special: the principal part must not depend on the point. A chart
that is neither conformally flat nor foliated and whose principal part varies in space needs genuine
variable-coefficient hyperbolic theory — energy estimates in Sobolev spaces with commutator terms —
of which mathlib has none. That is the next barrier after this card, not this card.
