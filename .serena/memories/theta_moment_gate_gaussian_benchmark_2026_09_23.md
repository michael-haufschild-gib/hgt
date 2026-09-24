# Why the theta-moment gates resist soft methods: they sit BELOW the Gaussian benchmark

Notation: `m_k = thetaCuspRawEvenMoment k = 2∫₀^∞ x^{2k} Φ(x) dx`, Φ = `thetaCuspFullSource`.
Ratios `r_j = m_j / m_{j-1}`.

**Gaussian benchmark.** For Φ = e^{−x²}, `m_k ∝ Γ(k+1/2)`, so
`m₀m₂/m₁² = Γ(1/2)Γ(5/2)/Γ(3/2)² = 3` exactly, and `5m₀m₂³ = 9m₁³m₃` exactly
(`ThetaCuspQuarticRatioGate` is an equality at the Gaussian — the module says so).

**The gates demand strictly better than Gaussian.**
- `ThetaCuspRelaxedFourthMomentConcentration` is `16 m₀m₂ ≤ 45 m₁²`, i.e. `m₀m₂/m₁² ≤ 2.8125 < 3`.
- The clean sufficient route via ratio monotonicity needs `5m₂ ≤ 9m₁·(m₀/m₀)`… concretely
  `r₂/r₁ ≤ 9/5 = 1.8`, i.e. `m₀m₂/m₁² ≤ 1.8`, far below 3.
So NO argument that is sharp only up to the Gaussian can discharge them. They are statements that Φ
is strictly more concentrated than a Gaussian in this ratio — consistent with Φ being super-Gaussian
(`thetaCuspLogConcavityScale x = π e^{2x}`, see `theta_kernel_total_positivity_triage_2026_09_23`),
but requiring a SHARP quantitative input.

**Soft methods provably bottom out too high.**
- Cauchy–Schwarz gives only log-convexity `m_{k+1}² ≤ m_k m_{k+2}` (now proved at every index:
  `thetaCuspRawEvenMoment_succ_sq_le`, `RHTower/ThetaCuspMomentLogConvexity.lean`, axiom-clean).
  That is the WRONG direction for the gates, which need a reverse bound.
- Log-concavity of Φ gives log-concavity of `n ↦ M_n/n!` (`M_n = ∫x^nΦ`), hence along the even
  progression `m_k = M_{2k}`: `m_{k+1}² ≥ m_k m_{k+2}·(2k+2)!²/((2k)!(2k+4)!)`. At k = 0 this is
  `m₀m₂ ≤ 6 m₁²` — ratio ≤ 6, versus Gaussian 3 and target 2.8125. A factor of two too weak.

**Consequence.** Do not attempt the moment gates by Cauchy–Schwarz, plain log-concavity, or any
reverse-Hölder bound for log-concave measures: those are all lossy by a factor ≳ 2 relative to the
Gaussian, and the targets lie below the Gaussian. Any real attempt must use the explicit
double-exponential form of Φ, not a soft concavity class. This also explains why the corpus closed
the first Hankel minor via explicit Stein/quadrature enclosures rather than by structural means.
