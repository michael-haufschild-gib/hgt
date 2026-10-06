# (N1) through Riemann-kernel translates (2026-10-06)

## Setup
- Tests `f = Σ_k b_k Φ(x − log k)` with `Φ̂ = Ξ`, so `f̂ = Ξ(t)·D(t)` with `D = Σ b_k k^{it}`.
- Because `Ξ` vanishes at every zero, on- and off-line, the explicit formula gives, for every Weil-positive `lam`:
  `∫|f̂|² dμ_lam = Σ_m (Λ − lam)(m) m^{−½} 2g(log m)`, where `g = f⋆f̃ = Σ X_{kl} K(· − log(k/l))`, `K = Φ⋆Φ̃`, `X = bbᵀ` (PSD lift).
- Consequence: if for every window `W₀` off `Z` there are such tests with `g(log m)` small (weighted by `log m`) and `Ξ²P ≥ c` on `W₀`, then (N1) holds. Every producer is then carried by `Z`, so U holds and RH ⟺ PBAP.
- `K` decays super-exponentially: `K(0)=0.320`, `K(log2)=2.4e-2`, `K(log3)=2.9e-4`, `K(log4)=1.9e-6`, `K(log6)=3.6e-11`. Each condition `g(log m) = 0` therefore couples only pairs with `k/l ≈ m`. Tails are controlled, unlike the cell tests of `2026-10-06-cpin-nyquist`.

## Exact obstruction at finite length
For finite `N`, imposing `g(log m) = 0` for all `m` forces `X = 0`. Far conditions are dominated by the extreme-ratio pair `(N,1)`, then by the next ratio, and so on down to the diagonal, where `Σ X_kk/k = 0`. So exact prime-blindness needs an infinite Dirichlet series. Finite tests only reach a residual `≈ ‖X‖·K(log(m_max/N))`.

## Numerics (`rkt.py`, CLARABEL/SCS, double precision; `rkt.out`, `rkt2.out`)
- Conditions were imposed down to a coefficient threshold `ε·K(0)`.
- At ε = 1e-4 and 1e-7, N = 6 is feasible: `P ≥ 27` on [17,18] and `P ≥ 11` on [39.5,40.5] with `g(0) = 1`.
- At ε = 1e-10, N = 6 becomes infeasible at t₀ = 40, while N = 12 is feasible.
- At ε = 1e-13, N ≤ 24 is infeasible and N = 48 is borderline (inaccurate).
- The required length N grows as the threshold decreases, as the exact obstruction predicts.
- The objective `min P` is the wrong normalization: P can be huge where Ξ² is tiny, which gives "unbounded" statuses. The right objective is `min_{W₀} Ξ²P`.

## Interpretation
- (N1) reduces to the joint limit `N → ∞`, `ε → 0`, with `min_{W₀} Ξ²P` bounded below and residual `→ 0`. A twin with a zero in `W₀` would force `min_{W₀}Ξ²P ≲ residual`.
- Deciding the asymptotics needs extended-precision SDP (constraints with coefficients `≪ 1e-16`), which double precision cannot represent.
