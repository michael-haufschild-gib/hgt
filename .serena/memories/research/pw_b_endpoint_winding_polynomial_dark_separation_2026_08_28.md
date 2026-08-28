# HC29: PW-B endpoint winding defeats polynomial dark packets (2026-08-28)

Route: PW-B. Status: formalized positive survivor.

Module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekEndpointWindingPolynomialDarkSeparation.lean`.

For positive finite-mass backreaction `epsilon`, the literal endpoint winding profile is
`q^(k+1)` with `q=exp(-1/(4 epsilon))` in `(0,1)`. Against the degree-`d` polynomial dark packet of
order `N=2d+1`, its exact response is `q(q-1)^N`, hence strictly negative. The corresponding
rank-one PSD dark-matrix energy is the square of this response and strictly positive.

This proves the actual nonperturbative PW endpoint channel escapes every finite-polynomial dark
packet already formalized in the corpus. Remaining burden: couple this faithful exponential grade
channel to oriented recoil before divisor selection and derive a global wall law.

Audit: direct Lean and target-only build passed (11613 jobs); six endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`. Frontier map was not edited.
