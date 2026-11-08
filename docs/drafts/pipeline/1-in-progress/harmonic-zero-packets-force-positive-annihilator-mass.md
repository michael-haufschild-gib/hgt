# Harmonic zero packets force positive annihilator mass

- **Stage:** 1-in-progress — formalizing the existing proof.
- **Lean target:** `ArithmeticPositiveDuality/HarmonicZeroPacketsForcePositiveAnnihilatorMass.lean`.

- **Candidate:** For a finite positive Dirichlet polynomial `P(s)=1+Σ a_n n^(−s)`, if `P(β+i kγ)=0` for `k=1,…,m`, then `H(β)=Σ a_n n^(−β)≥m`.
- **Exact identity:** With `u_n=exp(−iγ log n)`,
  `Σ a_n n^(−β)|1+u_n+⋯+u_n^m|²=(m+1)(H(β)−m)`.
  Expand the squared sum and use the prescribed Fourier moments. Equality forces every supported phase to be a nontrivial `(m+1)`st root of unity.
- **Sharp family:** `P(s)=Σ_(j=0)^m 2^(j(β−s))`, with `γ=2π/((m+1)log 2)`, has the full harmonic packet and `H(β)=m`.
- **Corpus:** `HTGeometry/CaratheodoryFejerAtomicKernelRoots.lean` supplies the positive-energy equality mechanism. The literal Dirichlet bridge and packet identity remain unformalized.
- **Limit:** No harmonic relation among actual zeta ordinates is assumed or established. This is an invariant of annihilators, not an AAL proof.
