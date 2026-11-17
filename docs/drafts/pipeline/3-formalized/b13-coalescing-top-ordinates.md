# Parity at a collision of top ordinates

- **Stage:** 3-formalized
- **Result:** For every depth δ > 0 and reference height r > 0 there are an aperture a and ε > 0 such that the CCM balance at a is positive whenever Σ Mⱼ|tⱼ − r| < ε Σ Mⱼ. Both a and ε work for every number of top ordinates, every positive choice of masses and every relation among the ordinates.

For a half-line unit source, Cauchy–Schwarz bounds each damped moment by B = (2δ)⁻¹ᐟ² and its change per unit frequency displacement by D = (2/(2δ)³)¹ᐟ². The phase-weighted square therefore changes by at most K|t − r|, with K = 2|a|B² + 2BD. Test the split form on a singleton maximizer and the singleton floor on a reflected split maximizer. If g is the singleton maximum minus the larger of zero and the reflected maximum, the strict gap survives for ε = g/(2K). Singleton recurrence supplies a with g > 0.

For an actual finite top layer satisfying this concentration bound, every ground state is reflection-odd at arbitrarily large apertures. This resolves the collision limit of B13-J6. General two-ordinate configurations and the arithmetic ground-state parity remain open.

**Lean.** [ParityAtCoalescingTopOrdinates.lean](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ParityAtCoalescingTopOrdinates.lean) proves `parityBalance_pos_of_transport`, `exists_aperture_positive_of_concentrated_ordinates` and `concentrated_top_ordinates_force_odd_ground`. All three axiom audits give `propext`, `Classical.choice`, `Quot.sound`.
