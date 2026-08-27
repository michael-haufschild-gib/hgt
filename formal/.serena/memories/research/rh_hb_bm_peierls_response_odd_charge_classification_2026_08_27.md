# HB Peierls response odd-charge classification (2026-08-27)

Formalized:
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicPeierlsResponseOddChargeClassification.lean`
- card in pipeline/3-formalized with matching slug
- umbrella wired; frontier map read-only untouched.

For arbitrary divisor-dependent response correction K:
- literal source amplitude A(q)
- BM complementary exponent λ(q)
- composite charge H_K(q)=A(q)K(q)λ(q)
- exact corrected current J_K(q)=-(H_K(q)+H_K(Jq))
- pointwise cancellation iff H_K is reflection-odd at q
- universal cancellation iff H_K is globally reflection-odd.

Countermodel:
- K_height(q)=Im(q)/(A(q)λ(q)).
- H_height(q)=Im(q) off critical wall; H_height(q)=0 on wall.
- Reflection preserves wall and negates height, so H_height is reflection-odd.
- Therefore corrected current vanishes for every Xi fibre unconditionally.

Meaning:
Reflection oddness, arbitrary coefficient matching, and canonical radial normalization do not carry RH force. A successful HB producer must derive response correction from one global augmented retarded-minus-advanced Peierls propagator with analytic/causal/local regularity excluding pointwise division by vanishing A(q).

Verification:
- direct Lean passed
- targeted build 11886/11886 passed
- six theorem axiom audits: only propext, Classical.choice, Quot.sound
- scratch deleted
- primary literature audit found no exact charge classifier/countermodel; priority provisional.