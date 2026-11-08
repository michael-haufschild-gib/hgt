# Harmonic zero packets force positive annihilator mass

- **Stage:** 3-formalized.
- **Lean:** `ArithmeticPositiveDuality/HarmonicZeroPacketsForcePositiveAnnihilatorMass.lean`.

- **Theorem:** For a finite positive two-prime Dirichlet polynomial `P(s)=1+Σ a_n n^(−s)`, if `P(β+i kγ)=0` for `k=1,…,m`, then `H(β)=Σ a_n n^(−β)≥m`.
- **Exact identity:** With `u_n=exp(−iγ log n)`,
  `Σ a_n n^(−β)|1+u_n+⋯+u_n^m|²=(m+1)(H(β)−m)`.
  Expand the squared sum and use the prescribed Fourier moments. Equality holds exactly when every supported nonconstant phase is a nontrivial `(m+1)`st root of unity.
- **Sharp family:** `P(s)=Σ_(j=0)^m 2^(j(β−s))`, with `γ=2π/((m+1)log 2)`, has the full harmonic packet and `H(β)=m`.
- **Declarations:** `harmonic_zero_packet_energy`, `harmonic_zero_packet_mass_le`, `harmonic_zero_packet_mass_eq_iff`, `exists_sharp_harmonic_packet`.
- **Audit:** Direct Lean check passed without warnings. All four capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import added.
- **Limit:** No harmonic relation among actual zeta ordinates is assumed or established. This is an invariant of annihilators, not an AAL proof.
