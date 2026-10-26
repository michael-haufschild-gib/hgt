# Two Euler factors determine the pole trace

- **ID:** adr-two-euler-factors
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `0 < ε < 1/2`, `α = 1 − ε`, `D_p w(n) = w(⌊n/p⌋)`, and call a row admitted when its
  full pronic energy `Σ w(n)²/(n(n+1))` is finite. For `w(0) = 0`:
  `w − 2^α D₂w` and `w − 3^α D₃w` admitted ⟺ `w − c n^α` admitted for some `c`, and `c` is unique.
  One factor does not suffice: `n^α cos(2π log₂ n)` passes the law at `2` but differs from every
  `c n^α` by infinite energy. For the total cofactor sum `S_ε v`, the eta law and the `3`-adic law
  together are equivalent to the renormalized inversion law `S_ε v − c n^α` admitted.

## Paper proof
1. **Log scale.** `g(u) = e^{−u/2} w(⌊e^u⌋)`. Since `⌊e^u⌋ = n` on `[log n, log(n+1))` and
   `∫ e^{−u} = 1/(n(n+1))` there, the pronic energy is `∫ g²`. As `⌊⌊x⌋/p⌋ = ⌊x/p⌋`,
   `e^{−u/2}(D_pw)(⌊e^u⌋) = p^{−1/2} g(u − log p)`, so the law at `p` reads
   `f_p = g − λ_p g(· − τ_p) ∈ L²`, `τ_p = log p`, `λ_p = p^{1/2−ε} = e^{κτ_p}`, `κ = 1/2 − ε > 0`.
2. **One law.** `S = Σ_{i≥0} λ^{−(i+1)} f(· + (i+1)τ)`: weighted Cauchy–Schwarz and translation
   invariance give `∫ S² ≤ (Σ λ^{−(i+1)})² ∫ f²`, and the series converges a.e. Where it converges,
   `S(u) = λ^{−1}(f(u+τ) + S(u+τ))` and `f(u+τ) = g(u+τ) − λ g(u)`, so `π = e^{−κu}(g + S)` satisfies
   `π(u+τ) = π(u)`. Thus `g = e^{κu}π − S`: one law fixes `g` modulo `L²` only up to `e^{κu}` times a
   `τ`-periodic function.
3. **Two laws.** `e^{κu}(π₂ − π₃) = S₂ − S₃ ∈ L²`. With `δ = π₂ − π₃`,
   `ψ(u) = π₃(u + τ₂) − π₃(u) = −(δ(u+τ₂) − δ(u))` a.e., so `∫_{u>0} ψ² < ∞`; `ψ` is `τ₃`-periodic, so the
   energy over `(0, Mτ₃]` is `M` times its circle energy, forcing `ψ = 0` a.e. Hence `π₃` has the
   periods `τ₂, τ₃`; lifted to `ℝ/τ₃ℤ` it is invariant under the rotation by `τ₂`, which is ergodic
   because `τ₂/τ₃ = log 2/log 3` is irrational (`2^a ≠ 3^b`); so `π₃ = c₃` a.e. Symmetrically
   `π₂ = c₂`, and `c₂ = c₃` since `e^{κu} ∉ L²(0, ∞)`. Then `g − c e^{κu} = −S₂ ∈ L²`.
4. **Back to rows.** `e^{κu} = e^{−u/2}(e^u)^α` and `0 ≤ x^α − ⌊x⌋^α ≤ 1`, so the pole row's profile
   differs from `c e^{κu}` by `O(e^{−u/2})` on `u ≥ 0`; for `u < 0` the profile vanishes.
5. **Uniqueness.** `(c' − c)² (n+1)^{2α}/((n+1)(n+2)) ≥ (c' − c)²/(2(n+1))` is not summable.
6. **Converse.** `n^α − p^α⌊n/p⌋^α ∈ [0, p^α]` (subadditivity of `x^α`), and `D_p` contracts the
   pronic norm by `√(2/p)`.
7. **Ghost.** For `n = 2m` both terms coincide (`log₂(2m) = log₂ m + 1`); for `n = 2m + 1` the defect
   is `≤ 1 + 2π/log 2` (mean value for `x^α`, `|cos a − cos b| ≤ |a − b|`, `log(1 + 1/m) ≤ 1/m`). If
   `ghost − c n^α` were admitted, step 4 gives `∫_{u>0} (cos(2πu/log 2) − c)² < ∞` for a
   `log 2`-periodic continuous function, hence `cos(2πu/log 2) ≡ c`, false at `u = 0` and
   `u = (log 2)/2`.

## Lean
`ArithmeticDefectRigidity/OnePrimeEulerLawsLeavePeriodicGhosts.lean`: `circleLift_coe_ae`,
`ae_eq_zero_of_periodic`, `exists_ae_eq_const_of_two_periods`, `sq_tsum_mul_le`,
`lintegral_sq_antiCausalSum_ne_top`, `logGhost_add_period`, `ae_periodic_logGhost`,
`ae_periodic_of_weighted_difference`, `exists_lintegral_sub_const_mul_exp_ne_top`.
`ArithmeticDefectRigidity/TwoEulerFactorsDetermineThePoleTrace.lean`: `lintegral_logProfile_sq`,
`pronicEnergy_ne_top_iff`, `lawDefect_logProfile`, `exists_pronicEnergy_sub_pole_ne_top`,
`eq_of_pronicEnergy_sub_pole_ne_top`, `pronicEnergy_eulerLaw_ne_top`, `cofactor_two_euler_laws_iff`,
`abs_eulerLaw_two_dyadicGhost_le`, `pronicEnergy_dyadicGhost_sub_pole_eq_top`,
`one_euler_factor_leaves_a_ghost`. Standard axioms only.

## Insight
The pole trace is not a chosen renormalization: it is the unique invariant left by two
multiplicatively independent Euler factors. A single factor `1 − p^α D_p` is blind to the whole
`p`-adic ghost family `n^α Π({log_p n})`; the second factor acts on the ghost as an irrational
rotation of the circle `ℝ/log p`, whose only invariant functions are constants. The renormalized
inversion law therefore has a domain-free, trace-free formulation on all rows, and the trace is
recovered as the ergodic invariant.
