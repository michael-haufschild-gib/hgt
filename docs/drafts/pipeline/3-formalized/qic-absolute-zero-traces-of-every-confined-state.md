# Absolute zero traces of every confined state

- **Stage:** 3-formalized
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)
- **Lean:** `IsConfinedNullVector.tilt_domain`, `summable_zero_traces`, and `hasSum_bare_pair`. [Unit tilt and zero traces](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheUnitTiltOfEveryConfinedState.lean#L96)

Every positive-ratio confined null state F admits the unit tilt exp(−u)F in the full energy domain. Consequently LF(z) and LF(−z) are square-summable over all centred ζ zero copies, even with infinitely many off-line zeros. Pairings of any two confined states converge absolutely on the full divisor.

**Proof.** Test the null equation with φ²F, where φ = exp(−c max(u,−N)), 0 ≤ c ≤ 1. The prime and pole pairings are bounded independently of N by the original weighted mass and exponentially weighted first moments. Retain the positive confinement term a∫φ²F²exp(−8u). The truncated-tilt jump identity then bounds its sum with the nonnegative Lévy energy of φF. Both terms are separately bounded uniformly in N. Fatou in u gives ∫F²exp(−(8+2c)u) < ∞. Fatou in the jump variable gives membership of the full tilt in the energy domain. At c = 1 the Laplace sampling bound gives square-summability on both reflected zero sets. Cauchy–Schwarz and the heated explicit formula give the absolute pairing.
