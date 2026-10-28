# Compact details at one level, noncompact full translation orbits

At each fixed dyadic level j, actual details of complete profiles with
Gamma<=1 lie in a compact subset of the original half-line L2 space.
The envelope is the continuous image, under the j-th dyadic shift, of the
proved compact closure of the original detail family. Coarse coefficients
and source horizons vary freely.

Let v_j be the j-th dyadic translate of haarAtom(1), j>=0. The actual
source vectors satisfy

inner(v_j,v_k)=haarMass(1) if j=k, and 0 otherwise;
dist(v_j,v_k)^2=2 haarMass(1) for j!=k.

The mass is strictly positive, so the orbit is injective and not totally
bounded. Its literal whole-line profiles are compactly supported and of
bounded variation, with one common original Gamma energy
Gamma(haarProfile(1)). Thus a bounded Gamma family can retain infinitely
many orthogonal directions across levels. Finite generator families with
their full level orbits are not finite-dimensional compact approximants.

Lean: `SignedArithmeticHodgeTheory/CompactDetailsDoNotMakeTranslationOrbitsCompact.lean`.
Capstones: `isCompact_singleLevelGammaDetailEnvelope`,
`singleLevelGammaDetails_mem_envelope`, `inner_firstHaarTranslationOrbit`,
`dist_firstHaarTranslationOrbit_sq`,
`not_totallyBounded_firstHaarTranslationOrbit`,
`firstHaarTranslationOrbit_coeFn`, `levyEnergy_firstHaarTranslatedProfile`,
`firstHaarTranslatedProfile_compact`, `firstHaarTranslatedProfile_bv`.
Final individual no-olean audit passes. Printed capstone dependencies contain
only `propext`, `Classical.choice`, `Quot.sound`.
