# Real and complex camera weights

`weightedImage c f g = Σ_z c(z) pointImage(f,g,z)`.
Absolute Lorentzian summability guarantees convergence for compact `C²`
windows on the strip.

The isolating windows depend on carrier geometry, not on coefficient values.
`weighted_discMoment_readout_slow` chooses one pair for all complex weights.
`weighted_discMoment_readout_rvm_explicit` retains `cameraMomentHeight`;
`zeta_weighted_discMoment_readout_explicit` supplies the actual ζ count
and the explicit `zetaWeightedMomentCameraHeight` at aperture `λL_T`, `λ>1/2`.
The usual polynomial isolation and cluster-radius conditions remain.

For every `a>0` and `θ>1`, `zeta_positive_mimic_weighted_count` gives
constants `A≥0,T₀≥40`, uniform over all positive on-line mimics of the
aperture-`a` ζ image. Above `T₀`, every finite subset in the camera band
`|Im z−T|≤T/2` and interval `[x,y]` satisfies

`Σ w(z) ≤ θ log(T/2π)(y−x)/(2π) + A log(T/2π)`.

The proof integrates modulated windows against an enlarged interval.
`cameraStripEnvelope` controls the actual off-line point-image and has
mass at most `[1+ε+(ε+ε²)e^ε]∫|b̂|²`. Choosing a small aperture and
capturing most of the kernel mass preserves any density coefficient
above `1/(2π)`. The wider central ζ band has the sharp multiplicity
count; its exterior is paid by absolute Lorentzian mass.

Weighted mass does not control support cardinality.
`exists_real_weighted_flat_image_with_many_atoms` constructs arbitrarily
many distinct positive atoms in a unit interval, all weights below one,
with the same flat image `∫f·conj(g)` at the fixed aperture. The construction
uses reciprocal-density weights on the simple lattice. It does not claim
that these flat images are ζ images.
