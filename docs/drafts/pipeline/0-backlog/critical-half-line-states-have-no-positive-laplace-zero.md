# Critical half-line states have no positive Laplace zero

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Target:** B104; a spectral substitute for unavailable positivity of the state.
- **Statement:** In the remaining finite threshold-equality case, every actual critical state F satisfies `∫ F(u) exp(su) du ≠ 0` for every real `s>0`.
- **Status:** Factorization mechanism identified; analytic identities and Lean proof open. Not counted.

Assume the indicated Laplace value vanishes. The causal resolvent

`G(u)=∫_{v≤u} exp(-s(u-v)) F(v) dv`

then vanishes on the positive half-line. Its weak derivative satisfies
`G'+sG=F`. Exponential convolution should preserve the physical and Gamma
domains, so both G and G′ are admissible tests.

For the translation-invariant Weil part, the Fourier relation gives
`Q_Weil(F)=Q_Weil(G′)+s² Q_Weil(G)`.
For the literal alias potential, integration by parts gives

`∫ F² exp(-8u)=∫ (G′)² exp(-8u)+(s²+8s)∫ G² exp(-8u)`.

Consequently the full form should satisfy

`Q(F)=Q(G′)+s²Q(G)+8s α(W₀)∫ G² exp(-8u)`.

Endpoint nonnegativity, `Q(F)=0`, and `α(W₀)>0` would force G=0 and
hence F=0, contradicting its unit norm. This does not assert that F has
one sign, nor that its polar source is nonzero.

Required work: actual resolvent domain and weak derivative; weighted
integration by parts; prime and pole factorization on measurable profiles.
The compact smooth zero-division theorem in
`HTGeometry/FourierZeroDivisionGroundStates` does not directly apply to
this half-line exponential potential. The actual-domain and weak-equation
modules on the B104 causal-coordinate card supply the intended form framework.
