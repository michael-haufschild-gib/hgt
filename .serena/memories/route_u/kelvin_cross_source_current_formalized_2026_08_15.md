Route U Kelvin cross-source current formalized.

Module:
formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgePrimeGammaKelvinCrossCurrent.lean

Main new results:
- Common-degree shifted reversal evaluation:
  Q_P(W)=(a^2+W)^d P((a^2-W)/(a^2+W)).
- Generic degree-padded antipode/Kelvin law:
  Q_(P^-)(W)=(W/a^2)^d Q_P(a^4/W), with natural degree/domain conditions.
- For actual antipodal even/odd channels:
  Q_E(a^4/W)=(a^2/W)^d Q_E(W),
  Q_O(a^4/W)=-(a^2/W)^d Q_O(W).
- Literal Gaussian cross density
  F_t(x)=Q_E(x^2)Q_O(x^2)exp(-t x^2)
  is exactly the archimedean norm polarization in the completed prime-Gamma cross balance.
- Anti-covariance:
  F_t(a^2/x)=-(a^2/x^2)^(2d) exp(-t*((a^2/x)^2-x^2)) F_t(x).
  Hence every nonzero Kelvin orbit contains opposite signs; pointwise sign closure is impossible.
- Self-dual seam: Q_O(a^2)=0 and F_t(a)=0.
- Arbitrary-weight Jacobian-paired current factors as
  F_t(x)[w(x)-(a^2/x^2)^(2d+1)exp(-t*((a^2/x)^2-x^2))w(a^2/x)].
  Specialized formally to gammaHardyPhaseRate.

Scientific interpretation:
cross branch is an oriented modular current, not positive energy. Naive inversion cancellation also fails because heat, Gamma rate, and Jacobian are not self-reciprocal. Next hard Route U target is compare exact Gamma-heat modular defect with polar and prime cross terms without dropping prime polarization.

Verification:
- scratch and checked-in lake env lean passed
- exact olean built directly, 749568 bytes
- umbrella wired but not built
- #print axioms only propext, Classical.choice, Quot.sound
- forbidden-token and diff checks passed
- Stage3 card: docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-u-kelvin-cross-source-current.md
- frontier updated.
