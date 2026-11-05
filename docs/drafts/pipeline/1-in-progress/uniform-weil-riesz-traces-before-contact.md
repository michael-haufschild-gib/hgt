# Uniform Weil Riesz traces before contact

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** On each compact interval of positive precontact apertures, actual Fourier Riesz sources are uniformly bounded and their normalized endpoint readouts depend continuously on aperture.

## Uniform source bound

Choose one cutoff from the uniform divergence of the Gamma row mass on a
fixed enclosing aperture `B`. The positive-level argument then bounds each
real graph coordinate by
`archTailBound(δ)‖F‖ + E + 2|⟨F,1⟩| + 2|⟨F,tanh⟩|`.
The same expression bounds its negative. Extension into the fixed complete
Weil space bounds graph mass norms by the enclosing Riesz norm. The real
graph decomposition is orthogonal, so each coordinate inherits this bound.
This would make the existing individual boundedness theorem uniform.

## Endpoint continuity

Strong convergence in the enclosing Weil space gives physical L² convergence.
A common source bound controls the small-distance part of each renewal
readout through the L¹ mass of the causal kernel. Away from zero, the causal
kernel is L². The remaining inputs are strong continuity of the actual
localized forcings and uniform bounds for them. For the cutoff commutators,
split the jump integral at a small distance: a common Lipschitz bound
controls the near part, and uniform cutoff convergence controls the rest.

## Lean status

Individual source bounds and both exact renewal readouts are formalized.
Uniform graph-norm transfer, aperture continuity of the actual Riesz source,
and uniform localized-forcing bounds are not yet formalized.
