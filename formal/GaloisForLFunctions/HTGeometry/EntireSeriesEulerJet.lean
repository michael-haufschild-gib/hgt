import GaloisForLFunctions.HTGeometry.PolynomialEulerJet
import GaloisForLFunctions.HTGeometry.ExpCompositeEulerJet

/-!
# Euler jets of an entire power series

For a coefficient sequence whose series converges on every disc, the Euler operator acts termwise:

```text
Θ^r (∑ c n u^n) (x) = ∑ n^r · c n · x^n .
```

The partial sums are polynomials, on which `Θ` is the polynomial Euler operator and acts on a
monomial by multiplication by its degree.  The jet-weighted series converges because a coefficient
sequence with factorial decay makes `(2R)^n / n!` bounded, leaving a geometric series with a
polynomial factor.

The termwise formula is what turns a tail bound on the coefficients into a bound on the tail's
contribution to the jets of the carrier at finitely many nodes.
-/

open Polynomial Filter Metric Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Summability of the jet-weighted series -/

/-- A summable real sequence is bounded above. -/
theorem exists_bound_of_summable {u : ℕ → ℝ} (hu : Summable u) :
    ∃ M : ℝ, ∀ n, u n ≤ M := by
  obtain ⟨M, hM⟩ := hu.tendsto_atTop_zero.bddAbove_range
  exact ⟨M, fun n => hM ⟨n, rfl⟩⟩

/-- **The jet-weighted series of a coefficient sequence with factorial decay converges.** -/
theorem summable_pow_mul_of_factorial_decay {c : ℕ → ℂ}
    (hc : ∀ n, ‖c n‖ ≤ ((n.factorial : ℝ))⁻¹) (r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun n : ℕ => (n : ℝ) ^ r * (‖c n‖ * R ^ n) := by
  have hfac : Summable fun n : ℕ => (2 * R) ^ n / (n.factorial : ℝ) :=
    Real.summable_pow_div_factorial (2 * R)
  obtain ⟨M, hM⟩ := exists_bound_of_summable hfac
  have hgeom : Summable fun n : ℕ => (n : ℝ) ^ r * ((1 : ℝ) / 2) ^ n := by
    refine summable_pow_mul_geometric_of_norm_lt_one r ?_
    rw [Real.norm_of_nonneg (by norm_num)]
    norm_num
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (mul_nonneg (norm_nonneg _) (pow_nonneg hR n)))
    (fun n => ?_) (hgeom.mul_left M)
  have hfac0 : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hRn : ‖c n‖ * R ^ n ≤ M * ((1 : ℝ) / 2) ^ n := by
    have h1 : ‖c n‖ * R ^ n ≤ ((n.factorial : ℝ))⁻¹ * R ^ n :=
      mul_le_mul_of_nonneg_right (hc n) (pow_nonneg hR n)
    have h2 : ((n.factorial : ℝ))⁻¹ * R ^ n =
        ((2 * R) ^ n / (n.factorial : ℝ)) * ((1 : ℝ) / 2) ^ n := by
      rw [mul_pow, div_pow, one_pow]
      field_simp
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (hM n) (by positivity))
  calc (n : ℝ) ^ r * (‖c n‖ * R ^ n) ≤ (n : ℝ) ^ r * (M * ((1 : ℝ) / 2) ^ n) :=
        mul_le_mul_of_nonneg_left hRn (by positivity)
    _ = M * ((n : ℝ) ^ r * ((1 : ℝ) / 2) ^ n) := by ring

/-! ### The Euler operator on monomials and partial sums -/

theorem polyEuler_monomial (n : ℕ) (a : ℂ) :
    polyEuler (Polynomial.monomial n a) = Polynomial.monomial n ((n : ℂ) * a) := by
  cases n with
  | zero => simp [polyEuler]
  | succ m =>
      rw [polyEuler, Polynomial.derivative_monomial, show (m + 1 - 1) = m by omega,
        show (X : Polynomial ℂ) = X ^ 1 by rw [pow_one],
        Polynomial.X_pow_mul_monomial 1 m (a * ((m + 1 : ℕ) : ℂ))]
      congr 1
      ring

theorem polyEuler_iterate_monomial (r n : ℕ) (a : ℂ) :
    polyEuler^[r] (Polynomial.monomial n a) = Polynomial.monomial n ((n : ℂ) ^ r * a) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, polyEuler_monomial]
      congr 1
      ring

/-- The partial sum of a coefficient series, as a polynomial. -/
def partialPoly (c : ℕ → ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range N, Polynomial.monomial n (c n)

theorem polyEuler_iterate_partialPoly (c : ℕ → ℂ) (N r : ℕ) :
    polyEuler^[r] (partialPoly c N) =
      ∑ n ∈ Finset.range N, Polynomial.monomial n ((n : ℂ) ^ r * c n) := by
  induction r with
  | zero => simp [partialPoly]
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, polyEuler, Polynomial.derivative_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hstep := polyEuler_monomial n ((n : ℂ) ^ r * c n)
      rw [polyEuler] at hstep
      rw [hstep]
      congr 1
      ring

theorem eval_polyEuler_iterate_partialPoly (c : ℕ → ℂ) (N r : ℕ) (x : ℂ) :
    (polyEuler^[r] (partialPoly c N)).eval x =
      ∑ n ∈ Finset.range N, (n : ℂ) ^ r * c n * x ^ n := by
  rw [polyEuler_iterate_partialPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Polynomial.eval_monomial]

/-! ### The entire function and its jet series -/

/-- The jet-weighted series of a coefficient sequence. -/
def jetSeriesFun (c : ℕ → ℂ) (r : ℕ) : ℂ → ℂ := fun u => ∑' n : ℕ, (n : ℂ) ^ r * c n * u ^ n

/-- The partial sums of the jet-weighted series. -/
def jetPartialFun (c : ℕ → ℂ) (r N : ℕ) : ℂ → ℂ :=
  fun u => ∑ n ∈ Finset.range N, (n : ℂ) ^ r * c n * u ^ n

theorem jetPartialFun_eq_eval (c : ℕ → ℂ) (r N : ℕ) (u : ℂ) :
    jetPartialFun c r N u = (polyEuler^[r] (partialPoly c N)).eval u :=
  (eval_polyEuler_iterate_partialPoly c N r u).symm

theorem norm_jet_term_le {c : ℕ → ℂ} (r n : ℕ) {u : ℂ} {R : ℝ} (hu : ‖u‖ ≤ R) :
    ‖(n : ℂ) ^ r * c n * u ^ n‖ ≤ (n : ℝ) ^ r * (‖c n‖ * R ^ n) := by
  have hR : 0 ≤ R := le_trans (norm_nonneg u) hu
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  have hun : ‖u‖ ^ n ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg u) hu n
  calc (n : ℝ) ^ r * ‖c n‖ * ‖u‖ ^ n ≤ (n : ℝ) ^ r * ‖c n‖ * R ^ n :=
        mul_le_mul_of_nonneg_left hun (by positivity)
    _ = (n : ℝ) ^ r * (‖c n‖ * R ^ n) := by ring

theorem summable_jetSeries {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ ((n.factorial : ℝ))⁻¹) (r : ℕ) (u : ℂ) :
    Summable fun n : ℕ => (n : ℂ) ^ r * c n * u ^ n := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_jet_term_le r n (le_refl ‖u‖)) ?_
  exact summable_pow_mul_of_factorial_decay hc r (norm_nonneg u)

/-- **Locally uniform convergence of the jet-weighted partial sums.** -/
theorem tendstoLocallyUniformlyOn_jetPartial {c : ℕ → ℂ}
    (hc : ∀ n, ‖c n‖ ≤ ((n.factorial : ℝ))⁻¹) (r : ℕ) :
    TendstoLocallyUniformlyOn (jetPartialFun c r) (jetSeriesFun c r) atTop Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hKR : K ⊆ Metric.closedBall (0 : ℂ) R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hbound : ∀ n : ℕ, ∀ x ∈ K, ‖(n : ℂ) ^ r * c n * x ^ n‖ ≤ (n : ℝ) ^ r * (‖c n‖ * R ^ n) := by
    intro n x hx
    have hxR : ‖x‖ ≤ R := by
      have hmem := hKR hx
      rwa [Metric.mem_closedBall, dist_zero_right] at hmem
    exact norm_jet_term_le r n hxR
  have huniform := tendstoUniformlyOn_tsum
    (u := fun n : ℕ => (n : ℝ) ^ r * (‖c n‖ * R ^ n))
    (f := fun n : ℕ => fun x : ℂ => (n : ℂ) ^ r * c n * x ^ n)
    (summable_pow_mul_of_factorial_decay hc r hR0) hbound
  intro v hv
  exact tendsto_finset_range.eventually (huniform v hv)

theorem differentiable_jetPartialFun (c : ℕ → ℂ) (r N : ℕ) :
    Differentiable ℂ (jetPartialFun c r N) := by
  have hfun : jetPartialFun c r N = fun u => (polyEuler^[r] (partialPoly c N)).eval u := by
    funext u
    exact jetPartialFun_eq_eval c r N u
  rw [hfun]
  exact Polynomial.differentiable _

/-- The jet-weighted series is entire. -/
theorem differentiable_jetSeriesFun {c : ℕ → ℂ}
    (hc : ∀ n, ‖c n‖ ≤ ((n.factorial : ℝ))⁻¹) (r : ℕ) :
    Differentiable ℂ (jetSeriesFun c r) := by
  rw [← differentiableOn_univ]
  refine (tendstoLocallyUniformlyOn_jetPartial hc r).differentiableOn ?_ isOpen_univ
  exact Filter.Eventually.of_forall fun N => (differentiable_jetPartialFun c r N).differentiableOn

theorem deriv_jetPartialFun (c : ℕ → ℂ) (r N : ℕ) (x : ℂ) :
    x * deriv (jetPartialFun c r N) x = jetPartialFun c (r + 1) N x := by
  have hfun : jetPartialFun c r N = fun u => (polyEuler^[r] (partialPoly c N)).eval u := by
    funext u
    exact jetPartialFun_eq_eval c r N u
  rw [hfun, Polynomial.deriv, jetPartialFun_eq_eval, Function.iterate_succ_apply', polyEuler,
    Polynomial.eval_mul, Polynomial.eval_X]

/-- **The Euler operator raises the jet weight of the series.** -/
theorem eulerOp_jetSeriesFun {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ ((n.factorial : ℝ))⁻¹) (r : ℕ) :
    eulerOp (jetSeriesFun c r) = jetSeriesFun c (r + 1) := by
  funext x
  have hderiv : Tendsto (fun N => deriv (jetPartialFun c r N) x) atTop
      (𝓝 (deriv (jetSeriesFun c r) x)) := by
    have hloc := (tendstoLocallyUniformlyOn_jetPartial hc r).deriv
      (Filter.Eventually.of_forall fun N =>
        (differentiable_jetPartialFun c r N).differentiableOn) isOpen_univ
    exact hloc.tendsto_at (Set.mem_univ x)
  have h1 : Tendsto (fun N => x * deriv (jetPartialFun c r N) x) atTop
      (𝓝 (x * deriv (jetSeriesFun c r) x)) := hderiv.const_mul x
  have h2 : Tendsto (fun N => jetPartialFun c (r + 1) N x) atTop
      (𝓝 (jetSeriesFun c (r + 1) x)) :=
    (summable_jetSeries hc (r + 1) x).hasSum.tendsto_sum_nat
  have h3 : (fun N => x * deriv (jetPartialFun c r N) x)
      = fun N => jetPartialFun c (r + 1) N x := by
    funext N
    exact deriv_jetPartialFun c r N x
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The Euler operator acts termwise on an entire power series.** -/
theorem eulerOp_iterate_jetSeriesFun {c : ℕ → ℂ}
    (hc : ∀ n, ‖c n‖ ≤ ((n.factorial : ℝ))⁻¹) (r : ℕ) :
    eulerOp^[r] (jetSeriesFun c 0) = jetSeriesFun c r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, eulerOp_jetSeriesFun hc r]

/-- The jet-weighted series is smooth. -/
theorem contDiff_jetSeriesFun {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ ((n.factorial : ℝ))⁻¹) (r : ℕ) :
    ContDiff ℂ (⊤ : ℕ∞) (jetSeriesFun c r) := by
  have hd : Differentiable ℂ (jetSeriesFun c r) := differentiable_jetSeriesFun hc r
  have ha : AnalyticOnNhd ℂ (jetSeriesFun c r) Set.univ :=
    hd.differentiableOn.analyticOnNhd isOpen_univ
  exact ha.contDiff

/-- **The jets of a carrier along an exponential phase, for an entire power-series source.** -/
theorem iteratedDeriv_expComp_jetSeriesFun {c : ℕ → ℂ}
    (hc : ∀ n, ‖c n‖ ≤ ((n.factorial : ℝ))⁻¹) (lam s : ℂ) (r : ℕ) (t : ℂ) :
    iteratedDeriv r (fun v => jetSeriesFun c 0 (Complex.exp (lam * v + s))) t =
      lam ^ r * jetSeriesFun c r (Complex.exp (lam * t + s)) := by
  rw [iteratedDeriv_expComp (contDiff_jetSeriesFun hc 0) lam s r t,
    eulerOp_iterate_jetSeriesFun hc r]

end

end GaloisForLFunctions.HTGeometry
