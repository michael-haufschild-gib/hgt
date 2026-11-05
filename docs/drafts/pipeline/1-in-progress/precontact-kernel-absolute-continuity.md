# Precontact kernel absolute continuity

- **ID:** precontact-kernel-absolute-continuity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ75; regularity part of Σ35.
- **Statement:** On every compact precontact aperture interval, evaluation Gram functions are absolutely continuous, with density given by the two endpoint traces.

## Mathematical route

For fixed old aperture `a` and enclosure `c`, the exact collar estimate gives
`(log(1/h)−E(a,c)) ΔK ≤ M_L(h)+M_R(h)`.
The existing actual-source limits give
`M_j(h)/(h log(1/h)) → |τ_j(a,z)|²`.
Hence the right upper derivative of the diagonal kernel is at most
`|τ_L(a,z)|²+|τ_R(a,z)|²` at every precontact aperture.

Remaining proof obligations: matching lower derivative by collar trial vectors;
continuity and integral reconstruction; polarization to finite evaluation Grams.
None of these estimates is asserted uniformly at contact.

For the lower bound, take
`u_h=(τ_L 1_left+τ_R 1_right)/sqrt(log(1/h))`.
`ccmWeilForm_intervalSource_upper` and the bounded opposite-half-line
crossing give `limsup ‖u_h‖²/h ≤ |τ_L|²+|τ_R|²`.
The strong residual limits give `Re⟨u_h,ΔE⟩/h → |τ_L|²+|τ_R|²`.
Then `0≤‖ΔE−u_h‖²` gives the matching lower derivative.
For left continuity, `exists_strict_smaller_aperture_of_compact_tsupport`
and `denseRange_smoothCore` provide approximation from smaller windows.

The same estimates give `‖ΔE_z−u_{h,z}‖²/h → 0`, uniformly over the
admitted constant collars at the enlarged aperture. Finite linear
combinations then have density
`|Σ_i α_i τ_L(a,z_i)|²+|Σ_i α_i τ_R(a,z_i)|²`: their trial collars combine
linearly, their error norms tend to zero, and the variational lower bound
matches the trial-energy upper bound.

Once the right derivative equals the trace energy everywhere, monotonicity
identifies it almost everywhere with the integrable ordinary derivative.
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` then gives exact
integral reconstruction, hence absolute continuity. This route needs no
uniform trace bound.

## Formal results

`eventually_kernel_increment_le_endpoint_energy` and
`exists_left_aperture_small_evalVectorIncrement` are kernel-checked in
`TheWeilKernelHasFiniteRightGrowth.lean`; their transitive axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] Source and conjecture fixed before formalization.
- [ ] Dependency-closed paper proof of absolute continuity and trace density.
- [ ] Lean formalization and transitive axiom audit.
