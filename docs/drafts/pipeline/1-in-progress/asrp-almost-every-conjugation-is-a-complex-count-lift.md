# Almost every conjugation is a complex count lift

- **ID:** asrp-almost-every-conjugation-is-a-complex-count-lift
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ASRP open topic 6; measure of the fixed-real-source conjugation family.
- **Statement:** For every fixed torus gauge `t`, independently conjugate each prime Euler factor with probability `1/2`. Almost surely the resulting prime sine current is `O(√x log²x)`, and the complex count holds exactly when the original real count holds. All real prime-power coefficients remain unchanged.

## Route

Use `HTGeometry.kolmogorov_maximal_inequality` for centered independent signs. At dyadic horizon `2^(K+1)`, coefficient energy is at most `2^(K+1)(K+1)²`, since each prime sine coefficient has absolute value at most `log n`. Threshold `√(2^(K+1))(K+1)²` gives exceptional probability at most `(K+1)⁻²`. Borel–Cantelli and dyadic interpolation give the required current bound. Apply `complexCount_torusGauge_iff` and invariance of real prime-power coefficients under conjugation.

## Gates

- [x] Corpus search found the maximal inequality and the complex count criterion.
- [ ] Check the product sign law and exact second-moment interface.
- [ ] Complete paper proof and novelty audit.
- [ ] Formalize and audit the exact result.

## Boundary

This would strengthen existence of a balanced lift to full measure in every conjugation family. It does not select the arithmetic point from a Haar-null exceptional set or prove RH. Count as one contribution only if the complete measure statement is proved.
