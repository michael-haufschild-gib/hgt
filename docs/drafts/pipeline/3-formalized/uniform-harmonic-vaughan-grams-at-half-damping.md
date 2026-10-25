# Uniform harmonic Vaughan Gram bound at half damping

- **ID:** uniform-harmonic-vaughan-grams-at-half-damping
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** uniform-half-damping-vaughan-harmonic-gram.md
- **Verification:** Three Gram targets passed corrected producing and final direct repository checks; three packet targets passed their corrected final direct check. All six transitive audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

Put `K_(U,V)=subHalfZetaCoeff(1/2)H_UH_V`, `s=(0,0,-1,1,0)`, and
`J(T)=Σ_(1≤n≤T)1/(n+1)`. One constant controls every cutoff pair, horizon,
and matrix entry:

`|Gᶜ_ij(T;U,V)−K_(U,V)²s_i s_j J(T)|≤C`.

The actual smooth-subtracted rows have one nonnegative summable cell envelope
dominating both `sqrt(n)|r_i(n)|/[n(n+1)]` and `r_i(n)²/[n(n+1)]` together.
Thus their energies and absolute smooth pairings have common finite bounds,
including zero cutoffs. Expanding each Gram entry and bounding the residual
product by half the sum of its two squares gives the matrix error estimate.
The common logarithmic prefix and finite-head inputs are themselves proved
for the actual Vaughan rows; no analytic premise remains undischarged.

The module
`GaloisForLFunctions/BezoutValuationIncidence/UniformHarmonicVaughanGramsAtHalfDamping.lean`
proves:

- `exists_summable_pmPronicVaughanSmoothRemainder_half_envelope`;
- `exists_uniform_pmPronicVaughanSmoothRemainder_half_mixed_and_energy_bound`;
- `exists_uniform_pmPronicVaughanCentredGram_half_harmonic_error_bound`.

The programme umbrella imports the module. Its olean supports the written
moving-limit and packet specializations, and its temporary draft was removed
after the final direct check.

For every real coefficient vector `w`, the packet specialization proves

`|‖Σ_i w_i e_i‖_T²−[K_(U,V)(w_3−w_2)]²J(T)|≤C(Σ_i|w_i|)²`.

Annihilating the smooth coefficient gives a common finite packet-energy bound.
In particular, `w_2=w_3` suffices at every cutoff pair and horizon. These are
proved in
`GaloisForLFunctions/BezoutValuationIncidence/UniformHarmonicEnergyLawsForVaughanSuperpositions.lean`:

- `exists_uniform_pmPronicVaughanPacket_half_harmonic_energy_error`;
- `exists_uniform_pmPronicVaughanPacket_half_energy_bound_of_smooth_zero`;
- `exists_uniform_pmPronicVaughanPacket_half_energy_bound_of_equal_convolution_coefficients`.

The packet leaf passed its final direct check and all three standard-axiom
audits. It is wired, its scratch was removed, and no olean was needed because
no written non-umbrella module imports it. Moving-limit, rank, and realization
claims on the parent card remain separate verification obligations.
This theorem gives no receiver bound below half damping or fixed strip.
