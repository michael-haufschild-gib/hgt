# Sub-Progression Dirichlet Stabilizer Inversion & Universal Polynomial Cell-Holonomy Growth Along `(+1, ×2)`

- **Route / Programme:** `ArithmeticCorrelationGeometry` (`ACG`) × `RenormalizedBiarithmeticGeometry` (`RBG` §9 Open Topic #4) × `BiarithmeticGaugeGeometry` (`BGG`)
- **Status:** Fully proven on paper; proceeding directly to Lean 4 formalization in `formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/SubProgressionStabilizerInversionAndCellHolonomyGrowth.lean`

## 1. Statements (100% Unconditional)

### Part A — Zero-Ramification Sub-Progression Stabilizer Inversion (`ACG`)
1. **Principal Gauge Identity (`dirichletGauge_one_eq_zero`, `twistedPrimeCoalSum_dirichletGauge_one`):**
   For every modulus `q : ℕ`, `dirichletGauge (1 : DirichletCharacter ℂ q) = 0` pointwise on all primes (including primes dividing `q`), so `twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge 1) = primeCoalSum Ω g X θ₀` with **zero ramified-prime error**.
2. **Sub-Progression Congruent-Pair Annihilation & Pure Nontrivial-Character Inversion (`congruent_coalWeight_sum_eq_zero_of_mul_lt`, `primeCoalSum_eq_neg_sum_nontriv`, `exists_nontriv_neg_re_twistedPrimeCoalSum_ge`, `primeCoalSum_sq_le_totient_sub_one_mul_sum_sq`, `eventually_bandwidth43_subProgression_window`):**
   Whenever `0 < θ₀ ≤ 1/2`, `θ₀ * X < q`, and `2 * q * θ₀ < 1`, every coalescent prime pair `(n, m)` in `primeRange X` satisfies `1 ≤ |n - m| ≤ θ₀ * X < q`, so `(n : ZMod q) ≠ (m : ZMod q)`. Thus the congruent stabilizer sum vanishes identically and
   $$\mathrm{primeCoalSum}(\Omega, g, X, \theta_0) = -\sum_{\chi \ne 1 \pmod q} \operatorname{Re}\mathrm{twistedPrimeCoalSum}(\Omega, g, X, \theta_0, \mathrm{dirichletGauge}(\chi)),$$
   yielding a pigeonhole witness `χ ≠ 1` at level `primeCoalSum / (φ(q) - 1)` and Cauchy–Schwarz RMS reciprocity `(primeCoalSum)^2 ≤ (φ(q) - 1) ∑_{χ ≠ 1} (Re twistedPrimeCoalSum)^2`, with non-vacuity across `κ ∈ (1/3 + η, 1 - η)` at bandwidth `4/3`.

### Part B — Universal Polynomial Cell-Holonomy & Liouville Agreement Growth (`RBG` §9 Open Topic #4)
3. **Quadratic Square-Absorber Charged-Cell Law (`two_mul_mul_succ_mem_chargedCells_iff`):**
   For every real sign gauge `ω` (`IsRealSignGauge ω`) with `realSignChar ω 2 = -1` and every `t ≥ 1` with `2 * t * (t + 1) ≤ X`, since `2 * (2 * t * (t + 1)) + 1 = (2 * t + 1)^2` has `σ_ω((2t + 1)^2) = 1`:
   $$2 t (t + 1) \in \mathrm{chargedCells}(\omega, X) \iff \sigma_\omega(t) \ne \sigma_\omega(t + 1).$$
4. **Universal Short-Block Sign-Change Witness (`exists_realSignChar_ne_succ_in_block`):**
   For every real sign gauge `ω` with `realSignChar ω 2 = -1` and every `u ≥ 1`, `L ≥ 6` satisfying `36 * u ≤ L ^ 2`, there exists `t ∈ Icc u (u + L - 1)` such that `realSignChar ω t ≠ realSignChar ω (t + 1)`.
5. **Unconditional `X^{1/4}` Cell-Holonomy & Liouville Agreement Growth (`card_chargedCells_ge_of_fourth_pow`, `sqrt_sqrt_div_sub_one_le_card_chargedCells`, `sqrt_sqrt_div_sub_one_le_card_liouvilleAgreements`, `hsDefect_liouville_ge_of_fourth_pow`):**
   For every real sign gauge `ω` with `realSignChar ω 2 = -1`:
   - Whenever `162 * (K + 1) ^ 4 ≤ X`, `K ≤ (chargedCells ω X).card` and `∀ c : ℝ, 2 * K ≤ hsDefect ω X c`;
   - Unconditionally for **every** `X : ℕ`, `Nat.sqrt (Nat.sqrt (X / 162)) - 1 ≤ (chargedCells ω X).card`;
   - Specializing to `ω = PrimeGauge.liouvilleGauge`, for **every** `X : ℕ`:
     $$\lfloor (X / 162)^{1/4} \rfloor - 1 = \mathrm{Nat.sqrt}(\mathrm{Nat.sqrt}(X / 162)) - 1 \le \#\{1 \le a \le X : \lambda(a) = \lambda(2a + 1)\},$$
     upgrading `RBG`'s `one_le_liouvilleAgreements` (`1 ≤ N₊`) to unconditional polynomial growth uniformly across all real sign gauges flipping `2`.

## 2. Dependency-Closed Paper Proof of Part B

1. **Quadratic Square-Absorber:** Set $a = 2t(t+1)$ ($t \ge 1$). Then $2a + 1 = 4t^2 + 4t + 1 = (2t + 1)^2$, so $\sigma_\omega(2a + 1) = \sigma_\omega(2t+1)^2 = 1$ (`realSignChar_sq_eq_one`). Meanwhile $\sigma_\omega(a) = \sigma_\omega(2)\sigma_\omega(t)\sigma_\omega(t+1) = -\sigma_\omega(t)\sigma_\omega(t+1)$. Thus $\sigma_\omega(a)\sigma_\omega(2a+1) \ne \sigma_\omega(2) = -1 \iff \sigma_\omega(t)\sigma_\omega(t+1) \ne 1 \iff \sigma_\omega(t) \ne \sigma_\omega(t+1)$.
2. **Short-Block Witness:** Given $u \ge 1$, $L \ge 6$, $36 u \le L^2$, put $D := \lfloor 2u / L \rfloor + 1 \ge 1$. Since $\sigma_\omega(2D) = -\sigma_\omega(D) \ne \sigma_\omega(D)$, discrete intermediate value yields $d \in [D, 2D - 1]$ with $\sigma_\omega(d) \ne \sigma_\omega(d + 1)$. Put $q := \lfloor (u + d - 1)/d \rfloor \ge 1$, so $u \le dq \le u + d - 1$.
   - If $2u < L$, then $D = 1$, $d = 1$, and $(d + 1)q = 2u < u + L$.
   - If $L \le 2u$, then $4u^2 \ge L^2 \ge 36u \implies u \ge 9$, $2u < DL \le dL \implies 2u + 1 \le dL$, and $(d - 1)L \le 2\lfloor 2u/L\rfloor L \le 4u \implies 36u(d-1)^2 \le L^2(d-1)^2 \le 16u^2 \implies 9(d - 1)^2 \le 4u$. For $d \in \{1, 2\}$, $d^2 - 1 \le 3 < 9 \le u$; for $d \ge 3$, $4(d^2 - 1) \le 9(d - 1)^2 - (d - 1)(5d - 13) \le 9(d - 1)^2 \le 4u$, so $d^2 - 1 \le u$ in all cases. Hence $u + d^2 - 1 \le 2u < dL$, i.e. $(d + 1)(u + d - 1) \le d(u + L)$, so $d(d + 1)q \le d(u + L) \implies (d + 1)q \le u + L$.
   Since $\sigma_\omega(q) \in \{\pm 1\}$, $\sigma_\omega(dq) = \sigma_\omega(d)\sigma_\omega(q) \ne \sigma_\omega(d + 1)\sigma_\omega(q) = \sigma_\omega((d + 1)q)$, so some $t \in [dq, (d + 1)q - 1] \subseteq [u, u + L - 1]$ satisfies $\sigma_\omega(t) \ne \sigma_\omega(t + 1)$.
3. **Disjoint Parabolic Blocks:** For $1 \le k \le K$, take $u_k = 9k^2$ and $L_k = 18k$, satisfying $L_k \ge 18 \ge 6$, $L_k^2 = 324 k^2 = 36 u_k$, and $u_k + L_k - 1 = 9k^2 + 18k - 1 < 9(k + 1)^2 = u_{k+1}$. Picking $t_k \in [u_k, u_k + L_k - 1]$ yields $K$ strictly increasing witnesses $t_k < 9(K + 1)^2$, hence $K$ distinct charged cells $a_k = 2 t_k (t_k + 1) \le 2 \cdot 9(K + 1)^2 \cdot 9(K + 1)^2 = 162(K + 1)^4 \le X$.
