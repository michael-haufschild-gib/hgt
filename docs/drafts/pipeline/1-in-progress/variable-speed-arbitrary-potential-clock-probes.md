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
   arbitrary time `s`, not at `0`. Time translation of the speed gives it:
   `hillFlowFrom ω s y₀ t := hillFlow (ω(·+s)) y₀ (t-s)`. Needed: it solves the equation, its value
   at `t = s` is `y₀`, the energy bound in the form `E(t) ≤ E(s)e^{2K|t-s|}`, and joint continuity in
   `(t, s, ξ)` — the last from the corpus's flow-comparison estimate `norm_hillFlow_sub_le`, since
   two base times give two coefficient functions close on windows.
3. **The multipliers.** `hillCosc t ξ := u_c(t;0,ξ)/ω(0,ξ)` and `hillSinc t s ξ := u_s(t;s,ξ)`, the
   damped cosine and the sine propagator, as elements of `E →ᵇ ℂ`; both bounded on windows, and the
   sine gains one power of the weight because `ω(t)|u_s| ≤ e^{K|t-s|}` and `ω ≥ ½ min(m,c_min)⟨ξ⟩`.
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
