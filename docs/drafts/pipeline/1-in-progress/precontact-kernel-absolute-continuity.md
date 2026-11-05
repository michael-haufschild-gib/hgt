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

Remaining proof obligations: left continuity from density of smaller windows;
exclude singular growth using finite upper derivatives; obtain the matching
lower derivative by collar trial vectors; polarize to finite evaluation Grams.
None of these estimates is asserted uniformly at contact.

For the lower bound, take
`u_h=(τ_L 1_left+τ_R 1_right)/sqrt(log(1/h))`.
`ccmWeilForm_intervalSource_upper` and the bounded opposite-half-line
crossing give `limsup ‖u_h‖²/h ≤ |τ_L|²+|τ_R|²`.
The strong residual limits give `Re⟨u_h,ΔE⟩/h → |τ_L|²+|τ_R|²`.
Then `0≤‖ΔE−u_h‖²` gives the matching lower derivative.
For left continuity, `exists_strict_smaller_aperture_of_compact_tsupport`
and `denseRange_smoothCore` provide approximation from smaller windows.

An alternative to a general singular-measure argument is a uniform trace
bound on `a∈[a₀,c]`, `a₀>0`, with `c` precontact. Fix the cutoff row-mass
estimate on the enclosing aperture; the truncation argument in
`TheCompletedWeilRieszVectorsAreBounded` then bounds the physical source
using its L² norm and the exponential forcing. The positive ground energy
at `c` controls those L² norms. Uniform endpoint forcing would bound the
trace energy and yield local Lipschitz continuity by the one-sided mean
value inequality. This uniform assembly remains to be proved.

## Gates

- [x] Source and conjecture fixed before formalization.
- [ ] Dependency-closed paper proof of absolute continuity and trace density.
- [ ] Lean formalization and transitive axiom audit.
