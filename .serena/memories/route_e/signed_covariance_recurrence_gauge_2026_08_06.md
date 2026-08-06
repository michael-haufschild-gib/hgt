# Route E signed covariance recurrence/gauge audit (2026-08-06)

Exact finite-prefix laws are paper-proved and Lean-certified in
`formal/GaloisForLFunctions/RHTower/GibbsSignedCovarianceAccumulation.lean`.

- For ordered distinct insertions, `ψ_j = α_j ψ_{j-1} - β_j d_j`, where
  `d_j = ∫_[x,p_j x] -Cov(parity, multiplicative energy)`.
- Unrolling: `ψ_k = A_{1:k} - Σ_j β_j A_{j+1:k} d_j`.
- `α_j = 1 - 2β_j`; retained forcing mass is exactly `(1-A_{1:k})/2 < 1/2`.
- Accumulation bound `|W-A|≤η` iff endpoint bound `|ψ_k|≤η`; this is a
  circularity theorem, not an RH producer.
- Two insertion orders obey `W^σ-W^τ=A^σ-A^τ`; order averaging cannot help.
- Positive survivor: `Q_{S∪p}+D_{S,p}=Q_S(x)+Q_S(px)`, with
  `Q=J²/Z` and nonnegative same-sign dissipation
  `D=Z(x)Z(px)/(Z(x)+Z(px))·(ψ(x)+ψ(px))²`.
- Paper Mellin balance: `E_r(S∪p)+D_r(S,p)=(1+p^{-r})E_r(S)`.
  Euler ceiling is automatic only for r>1; strict-half range 0<r≤1 needs
  independent cofinal dissipation saturation. Escape mode is antiscale
  coherence `ψ(px)≈-ψ(x)`.
- Alternating free-boundary jet is not a global sign law: for S={2,3},
  `ψ'_S(x)>0` for x≥log 2 although its free-boundary derivative is negative.

Targeted build 8659/8659 passed. Axioms only propext, Classical.choice, Quot.sound.
No full build. Static global lint was blocked by unrelated concurrent
`HTGeometry.ObserverBoundaryBuilding` umbrella/index churn.

The requested strict-half bound remains open/RH-strength. Revised first source
premise: WEIGHTED-PRIME-DILATION-INCREMENT-CANCELLATION or equivalently a
non-circular source theorem forcing critical Mellin dissipation saturation.