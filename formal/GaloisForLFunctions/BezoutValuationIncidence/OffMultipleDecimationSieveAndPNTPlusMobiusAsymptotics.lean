import GaloisForLFunctions.BezoutValuationIncidence.VaughanTypeIIShortAndAllHorizonMobiusL2Energy
import GaloisForLFunctions.HTGeometry.CoefficientDecimationSieve
import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import GaloisForLFunctions.HTGeometry.MollifierL2Contraction
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Off-Multiple Coefficient Decimation Sieve, Mollifier $L^2$ Contraction, and PNT+ Möbius Asymptotics

This module connects `BezoutValuationIncidence` across the Lean corpus to `HTGeometry` and
`PNTPlus`:

1. **Exact Off-Multiple Coefficient Decimation/Inflation Sieve and Euler-Density Scale Law
   (`offMultiple_decimation_sieve_and_scale_law`):**
   Connects `decimate_inflate`, `sieveOffMultiple_eq_sum_divisors`,
   `sum_divisors_moebiusDiv_complex`, `LSeries_offMultiple`, and `J_sieveOffMultiple`
   (`HTGeometry/CoefficientDecimationSieve.lean:52, 134, 154, 223, 242`):
   - Decimation $D_q$ inverts inflation $S_q$, and the off-multiple prime sieve `sieveOffMultiple P`
     expands over divisors of the primorial $P^\#$ as $\sum_{d \mid P^\#} \mu(d) S_d D_d$, with
     $\sum_{d \mid P^\#} \mu(d)/d = \operatorname{sieveDensity}(P)$.
   - For any `LSeriesSummable` sequence $b$, $L(E_q b, s) = L(b, s) - q^{-s} L(D_q b, s)$.
   - Any additive functional $J$ carrying the inflation character $q^{-s}$ on a source family `pol`
     carrying the decimation character $q^{s-1}$ satisfies the exact Euler-product scale law
     $J(\operatorname{sieveOffMultiple}(P, \operatorname{pol}(a))) = \operatorname{sieveDensity}(P) \cdot J(\operatorname{pol}(a))$.

2. **Reciprocal Zeta Dirichlet Series, Euler Clock Mean, and Mollifier $L^2$ Contraction
   (`realDirichlet_moebius_eulerClock_and_mollifier_contraction`):**
   Connects `ofReal_tsum_moebius_eq` and `integral_id_eulerClockLaw`
   (`HTGeometry/RealDirichletSeries.lean:177, 208`) with `integral_sq_mollify_le` and
   `integral_sq_mollify_le_of_isProbabilityDensity` (`HTGeometry/MollifierL2Contraction.lean:20, 28`):
   - For every $\sigma > 1$, $\sum_{n=1}^\infty \mu(n) n^{-\sigma} = 1 / \zeta(\sigma)$ and the Euler
     clock mean is $(\sum (\log n)\Lambda(n) n^{-\sigma}) / (\sum \Lambda(n) n^{-\sigma})$.
   - Line mollification by any probability density $\rho \ge 0$ ($\int \rho = 1$) is an $L^2(\mathbb{R})$
     contraction $\int (\operatorname{mollify} \rho u)^2 \le \int u^2$.

3. **PNT+ Floor-Quotient and Harmonic Möbius Cancellation, Liouville $o(x)$ Law, and Chebyshev AP
   Asymptotics (`pntPlus_mobius_floor_harmonic_liouville_and_ap_asymptotics`):**
   Connects `sum_mobius_floor`, `sum_mobius_floor_tail_isLittleO`, `sum_mobius_div_approx`,
   `mu_pnt_alt`, `lambda_pnt`, and `chebyshev_asymptotic_pnt`
   (`PNTPlus/Consequences.lean:2056, 2093, 2103, 2191, 2210, 2245`):
   - Exact finite-horizon identity $\sum_{n=1}^{\lfloor x \rfloor} \mu(n) \lfloor x/n \rfloor = 1$ for
     all $x \ge 1$, with tail $\sum_{\lfloor x/K \rfloor < n \le \lfloor x \rfloor} \mu(n) \lfloor x/n \rfloor = o(x)$
     and quantitative harmonic-Möbius approximation `sum_mobius_div_approx`.
   - Unconditional harmonic Möbius cancellation $\sum_{n < \lfloor x \rfloor} \mu(n)/n = o(1)$,
     Liouville cancellation $\sum_{n < \lfloor x \rfloor} (-1)^{\Omega(n)} = o(x)$, and Chebyshev
     asymptotic $\sum_{p \le x,\, p \equiv a \pmod q} \log p \sim x / \varphi(q)$ in coprime
     arithmetic progressions.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction Asymptotics
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

/-! ## §1. Off-Multiple Coefficient Decimation/Inflation Sieve and Euler-Density Scale Law -/

/-- **Off-Multiple Coefficient Decimation/Inflation Sieve and Euler-Density Scale Law
(`offMultiple_decimation_sieve_and_scale_law`):**
1. Decimation inverts inflation ($D_q(S_q b) = b$ for $q > 0$), `sieveOffMultiple P b M` expands as
   $\sum_{d \mid P^\#} \mu(d) S_d D_d b(M)$, and $\sum_{d \mid P^\#} \mu(d)/d = \operatorname{sieveDensity}(P)$.
2. For any `LSeriesSummable` sequence $b$, $L(E_q b, s) = L(b, s) - q^{-s} L(D_q b, s)$.
3. If $J$ is an additive functional carrying the inflation character $q^{-s}$ and `pol` carries the
   decimation character $q^{s-1}$, then $J(\operatorname{sieveOffMultiple}(P, \operatorname{pol}(a))) =
   \operatorname{sieveDensity}(P) \cdot J(\operatorname{pol}(a))$. -/
theorem offMultiple_decimation_sieve_and_scale_law
    {q : ℕ} (hq : 0 < q) (b : ℕ → ℂ) (M : ℕ) (P : Finset Nat.Primes)
    {s : ℂ} (hb : LSeriesSummable b s)
    {J : (ℕ → ℂ) → ℂ} {pol : ℕ → ℕ → ℂ}
    (hsub : ∀ u v : ℕ → ℂ, J (fun n => u n - v n) = J u - J v)
    (hdec : ∀ a r : ℕ, decimate r (pol a) = pol (a * r))
    (hchar : ∀ a r : ℕ, 0 < r → J (pol (a * r)) = ((r : ℂ)) ^ (s - 1) * J (pol a))
    (hinf : ∀ (r : ℕ) (u : ℕ → ℂ), 0 < r → J (inflate r u) = ((r : ℂ)) ^ (-s) * J u)
    (a : ℕ) :
    ((decimate q (inflate q b) = b) ∧
      (sieveOffMultiple P b M =
        ∑ d ∈ (sievePrimorial P).divisors, ((μ d : ℤ) : ℂ) * multipleProjection d b M) ∧
      (∑ d ∈ (sievePrimorial P).divisors, ((μ d : ℤ) : ℂ) / (d : ℂ) =
        ((sieveDensity P : ℝ) : ℂ))) ∧
    (LSeries (offMultiple q b) s =
      LSeries b s - ((q : ℂ)) ^ (-s) * LSeries (decimate q b) s) ∧
    (J (sieveOffMultiple P (pol a)) = ((sieveDensity P : ℝ) : ℂ) * J (pol a)) :=
  ⟨⟨decimate_inflate hq b,
    sieveOffMultiple_eq_sum_divisors P b M,
    sum_divisors_moebiusDiv_complex P⟩,
   LSeries_offMultiple hq hb,
   J_sieveOffMultiple hsub hdec hchar hinf P a⟩

/-! ## §2. Reciprocal Zeta Dirichlet Series, Euler Clock Mean, and Mollifier $L^2$ Contraction -/

/-- **Reciprocal Zeta Dirichlet Series, Euler Clock Mean, and Mollifier $L^2$ Contraction
(`realDirichlet_moebius_eulerClock_and_mollifier_contraction`):**
1. For every $\sigma > 1$, $\sum_{n=1}^\infty \mu(n) n^{-\sigma} = 1 / \zeta(\sigma)$ and the Euler
   clock mean equals $(\sum (\log n)\Lambda(n) n^{-\sigma}) / (\sum \Lambda(n) n^{-\sigma})$.
2. Line mollification satisfies Young's $L^2$ bound $\int (\operatorname{mollify} \rho u)^2 \le
   (\int |\rho|)^2 \int u^2$ and is an $L^2$ contraction when $\rho \ge 0$ has unit integral. -/
theorem realDirichlet_moebius_eulerClock_and_mollifier_contraction
    {σ : ℝ} (hσ : 1 < σ) {ρ u : ℝ → ℝ}
    (hρm : Measurable ρ) (hum : Measurable u)
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρi : Integrable ρ) (hρ1 : (∫ t, ρ t) = 1)
    (hu2 : Integrable (fun x => u x ^ (2 : ℕ)))
    (hconv : Integrable (fun x => mollify ρ u x ^ (2 : ℕ))) :
    ((((∑' n : ℕ, (moebius n : ℝ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) = 1 / riemannZeta (σ : ℂ)) ∧
      ((∫ y, y ∂(eulerClockLaw σ)) =
        (∑' n : ℕ, (Real.log n * Λ n) * (n : ℝ) ^ (-σ)) /
          ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ))) ∧
    ((∫ x, mollify ρ u x ^ (2 : ℕ)) ≤ ∫ x, u x ^ (2 : ℕ)) :=
  ⟨⟨ofReal_tsum_moebius_eq hσ, integral_id_eulerClockLaw hσ⟩,
   integral_sq_mollify_le_of_isProbabilityDensity hρm hum hρ0 hρi hρ1 hu2 hconv⟩

/-! ## §3. PNT+ Floor-Quotient and Harmonic Möbius Cancellation, Liouville $o(x)$, and Chebyshev AP -/

/-- **PNT+ Floor-Quotient and Harmonic Möbius Cancellation, Liouville $o(x)$ Law, and Chebyshev AP
Asymptotics (`pntPlus_mobius_floor_harmonic_liouville_and_ap_asymptotics`):**
1. For all $x \ge 1$ and $K > 0$, $\sum_{n=1}^{\lfloor x \rfloor} \mu(n) \lfloor x/n \rfloor = 1$,
   $|x \sum_{n=1}^{\lfloor x/K \rfloor} \mu(n)/n - 1| \le x/K + |\sum_{\lfloor x/K \rfloor < n \le \lfloor x \rfloor} \mu(n) \lfloor x/n \rfloor|$,
   and the floor-quotient tail is $o(x)$ as $x \to \infty$.
2. Unconditionally, $\sum_{n < \lfloor x \rfloor} \mu(n)/n = o(1)$,
   $\sum_{n < \lfloor x \rfloor} (-1)^{\Omega(n)} = o(x)$, and for $\gcd(a, q) = 1$ ($1 \le q$, $a < q$),
   $\sum_{p \le x,\, p \equiv a \pmod q} \log p \sim x / \varphi(q)$. -/
theorem pntPlus_mobius_floor_harmonic_liouville_and_ap_asymptotics
    {x : ℝ} (hx : 1 ≤ x) {K : ℕ} (hK : 0 < K)
    {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) (ha' : a < q) :
    ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = 1) ∧
      (|x * (∑ n ∈ Finset.Icc 1 ⌊x / K⌋₊, (μ n : ℝ) / n) - 1| ≤
        x / K + |∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)|) ∧
      ((fun y : ℝ => ∑ n ∈ Finset.Ioc ⌊y / K⌋₊ ⌊y⌋₊, (μ n : ℝ) * (⌊y / (n : ℝ)⌋ : ℝ)) =o[atTop]
        fun y => y)) ∧
    (((fun y : ℝ => ∑ n ∈ Finset.range ⌊y⌋₊, (μ n : ℝ) / n) =o[atTop] fun _ => (1 : ℝ)) ∧
      ((fun y : ℝ => ∑ n ∈ Finset.range ⌊y⌋₊, (-1 : ℤ) ^ (Ω n)) =o[atTop] fun y => y) ∧
      ((fun y : ℝ => ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊y⌋₊),
          if p % q = a then Real.log p else 0) ~[atTop]
        fun y => y / q.totient)) :=
  ⟨⟨_root_.sum_mobius_floor x hx,
    _root_.sum_mobius_div_approx x K hK hx,
    _root_.sum_mobius_floor_tail_isLittleO K hK⟩,
   ⟨_root_.mu_pnt_alt,
    _root_.lambda_pnt,
    _root_.chebyshev_asymptotic_pnt hq ha ha'⟩⟩

end GaloisForLFunctions.BezoutValuationIncidence

end
