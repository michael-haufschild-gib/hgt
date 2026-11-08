# Fixed-height mass gap for positive annihilators

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacles:** B13, B112.
- **Statement:** If a normalized positive two-prime Dirichlet polynomial vanishes at `σ+δ+iγ`, `δ>0`, then
  `H(σ) ≥ 1 / max(-cos(γ log 2) exp(-δ log 2), exp(-δ log 3))`.
- **Classification sought:** At a fixed height `γ`, reflected-pair annihilators can approach the unrestricted floor `exp(δ log 2)` exactly when `cos(γ log 2)=-1`.
- **Mechanism:** The lowest nonconstant frequency is uniquely `log 2`; every other frequency is at least `log 3`. Separate that atom in the real cancellation equation. Opposite phase at the first atom should be both necessary and sufficient for approaching the floor.
- **Corpus baseline:** Unit-mass phase equality and harmonic-packet equality are formalized; the quantitative first-frequency gap is not found in the corpus search.
- **Gate:** Prove the frequency gap, the quantitative inequality and both directions of the classification in Lean. No claim about actual zeta ordinates; uncounted.
