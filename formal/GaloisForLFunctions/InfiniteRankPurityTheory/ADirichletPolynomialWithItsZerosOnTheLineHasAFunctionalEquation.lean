import GaloisForLFunctions.InfiniteRankPurityTheory.ADirichletPolynomialWithAFunctionalEquationIsNotAFactor
import GaloisForLFunctions.RHTower.ThetaHalfLinePortGauge
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.AbsMax

/-!
# A Dirichlet polynomial with its zeros on the line has a functional equation

Let `D(s) = Σ a_n n^{-s}` be a Dirichlet polynomial with a constant term and one further term, all
of whose zeros lie on the critical line. Then `|D(1 - s̄)| = N^{Re s - 1/2} |D(s)|` for some
`N > 1`: the functional equation is forced by the zeros. Hence no such polynomial has all its zeros
among the zeros of `ξ`, with no functional equation assumed.

* `tendsto_reflPoly_div`, `exists_entire_quotient`: the reflected polynomial
  `D^♯(s) = conj D(1 - s̄)` has the zeros of `D` with the same orders, so `D^♯/D` extends to an
  entire function `g` without zeros.
* `exists_bound_on_strip`: `g` is bounded on vertical strips. `D` is almost periodic, so every
  interval of a fixed length contains a height at which `|D|` is bounded below across the strip;
  the maximum principle on the rectangles between two such heights bounds `g`.
* `exists_left_bound`: far to the left the top term of `D` dominates.
* `exists_functionalEquation_of_zeros_on_line`: `g` is of exponential type, hence `g = e^{αs + β}`;
  `|g| = 1` on the line gives `Im α = 0` and `|g(s)| = e^{α (Re s - 1/2)}`, and the growth of `D` to
  the left gives `α > 0`.
* `exists_zero_not_xi_zero_of_constantTerm`: a Dirichlet polynomial with a constant term and one
  further term has a zero that is not a zero of `ξ`.
-/

open Complex Filter Topology Set Metric
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

/-! ### The reflected polynomial -/

/-- The reflected polynomial `D^♯(s) = conj D(1 - s̄) = Σ conj(a_n) n^{-(1 - s)}`. -/
def reflPoly (a : ℕ →₀ ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ a.support, conj (a n) * (n : ℂ) ^ (-(1 - s))

theorem reflPoly_eq {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (s : ℂ) :
    reflPoly a s = conj (finiteDirichletPolynomial a (1 - conj s)) := by
  unfold reflPoly finiteDirichletPolynomial
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [map_mul, conj_natCast_cpow_neg (pos_of_mem_support ha0 hn)]
  simp

theorem differentiable_reflPoly {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) : Differentiable ℂ (reflPoly a) := by
  intro z
  refine DifferentiableAt.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_support ha0 hn).ne'
  exact (((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).neg.const_cpow
    (Or.inl hn0)).const_mul _

theorem norm_reflPoly_le {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) {c : ℝ} {s : ℂ} (hs : s.re ≤ c) :
    ‖reflPoly a s‖ ≤ ∑ n ∈ a.support, ‖a n‖ * (n : ℝ) ^ (c - 1) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn0 := pos_of_mem_support ha0 hn
  rw [norm_mul, RCLike.norm_conj, Complex.norm_natCast_cpow_of_pos hn0]
  refine mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn0) ?_) (norm_nonneg _)
  simp only [Complex.neg_re, Complex.sub_re, Complex.one_re]
  linarith

/-- The reflected polynomial is of exponential type. -/
theorem norm_reflPoly_le_exp {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) {N : ℕ} (hN : ∀ n ∈ a.support, n ≤ N)
    (hN1 : 1 ≤ N) (s : ℂ) :
    ‖reflPoly a s‖ ≤ (∑ n ∈ a.support, ‖a n‖) * Real.exp (Real.log N * ‖s‖) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn0 := pos_of_mem_support ha0 hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  rw [norm_mul, RCLike.norm_conj, Complex.norm_natCast_cpow_of_pos hn0,
    ← Real.rpow_def_of_pos hNpos]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hre : (-(1 - s)).re ≤ ‖s‖ := by
    have := Complex.re_le_norm s
    simp only [Complex.neg_re, Complex.sub_re, Complex.one_re]
    linarith
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hre).trans
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN n hn) (norm_nonneg _))

/-! ### The top term dominates to the left -/

/-- **Far to the left the top term dominates.** -/
theorem exists_left_bound {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) {N : ℕ} (hNmem : N ∈ a.support)
    (hN : ∀ n ∈ a.support, n ≤ N) (hN2 : 2 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ≤ -C →
      ‖a N‖ / 2 * (N : ℝ) ^ (-w.re) ≤ ‖finiteDirichletPolynomial a w‖ := by
  set A : ℝ := ∑ n ∈ a.support, ‖a n‖ with hA
  have haN : 0 < ‖a N‖ := norm_pos_iff.mpr (Finsupp.mem_support_iff.mp hNmem)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  set q : ℝ := ((N : ℝ) - 1) / N with hq
  have hq0 : 0 < q := by rw [hq]; exact div_pos (by linarith) (by linarith)
  have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
  have hNq : (N : ℝ) * q = N - 1 := by rw [hq]; field_simp
  have hlim : Tendsto (fun C : ℝ => A * q ^ C) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_atTop_of_base_lt_one q (by linarith) hq1).const_mul A
  obtain ⟨C, hC, hC0⟩ := ((hlim.eventually (gt_mem_nhds (half_pos haN))).and
    (eventually_ge_atTop 0)).exists
  refine ⟨C, hC0, fun w hw => ?_⟩
  have hx : C ≤ -w.re := by linarith
  have hx0 : 0 ≤ -w.re := hC0.trans hx
  have hNx : 0 < (N : ℝ) ^ (-w.re) := Real.rpow_pos_of_pos (by linarith) _
  have hsplit : finiteDirichletPolynomial a w = a N * (N : ℂ) ^ (-w)
      + ∑ n ∈ a.support.erase N, a n * (n : ℂ) ^ (-w) := by
    rw [finiteDirichletPolynomial, ← Finset.add_sum_erase _ _ hNmem]
  have hmain : ‖a N * (N : ℂ) ^ (-w)‖ = ‖a N‖ * (N : ℝ) ^ (-w.re) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have htail : ‖∑ n ∈ a.support.erase N, a n * (n : ℂ) ^ (-w)‖
      ≤ A * q ^ C * (N : ℝ) ^ (-w.re) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ n ∈ a.support.erase N,
        ‖a n * (n : ℂ) ^ (-w)‖ ≤ ‖a n‖ * (q ^ C * (N : ℝ) ^ (-w.re)) := by
      intro n hn
      have hns := Finset.mem_of_mem_erase hn
      have hn0 := pos_of_mem_support ha0 hns
      have hnN : (n : ℝ) ≤ N - 1 := by
        have h1 : n ≤ N := hN n hns
        have h2 : n ≠ N := Finset.ne_of_mem_erase hn
        have h3 : n + 1 ≤ N := by omega
        have : ((n + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h3
        push_cast at this
        linarith
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc (n : ℝ) ^ (-w.re) ≤ ((N : ℝ) - 1) ^ (-w.re) :=
            Real.rpow_le_rpow (by positivity) hnN hx0
        _ = (N : ℝ) ^ (-w.re) * q ^ (-w.re) := by
            rw [← hNq, Real.mul_rpow (by linarith) hq0.le]
        _ ≤ (N : ℝ) ^ (-w.re) * q ^ C :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hx) hNx.le
        _ = q ^ C * (N : ℝ) ^ (-w.re) := mul_comm _ _
    calc ∑ n ∈ a.support.erase N, ‖a n * (n : ℂ) ^ (-w)‖
        ≤ ∑ n ∈ a.support.erase N, ‖a n‖ * (q ^ C * (N : ℝ) ^ (-w.re)) := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ a.support, ‖a n‖ * (q ^ C * (N : ℝ) ^ (-w.re)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ => by positivity
      _ = A * q ^ C * (N : ℝ) ^ (-w.re) := by rw [hA, ← Finset.sum_mul]; ring
  have h := norm_sub_le_norm_add (a N * (N : ℂ) ^ (-w))
    (∑ n ∈ a.support.erase N, a n * (n : ℂ) ^ (-w))
  rw [hsplit]
  have hC' : A * q ^ C * (N : ℝ) ^ (-w.re) ≤ ‖a N‖ / 2 * (N : ℝ) ^ (-w.re) :=
    mul_le_mul_of_nonneg_right hC.le hNx.le
  rw [hmain] at h
  linarith

/-! ### The quotient is entire and has no zeros -/

/-- A nonzero Dirichlet polynomial does not vanish identically on the critical line. -/
theorem exists_ne_zero_on_line {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (hane : a ≠ 0) :
    ∃ t : ℝ, finiteDirichletPolynomial a ((1 / 2 : ℂ) + t * I) ≠ 0 := by
  by_contra hcon
  have hall : ∀ t : ℝ, finiteDirichletPolynomial a ((1 / 2 : ℂ) + t * I) = 0 := fun t => by
    by_contra h
    exact hcon ⟨t, h⟩
  refine finiteDirichletPolynomial_ne_zero a ha0 hane (funext fun s => ?_)
  have han : AnalyticOnNhd ℂ (finiteDirichletPolynomial a) univ :=
    (differentiable_finiteDirichletPolynomial a ha0).differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 / 2 : ℂ), finiteDirichletPolynomial a z = 0 := by
    rw [frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.mp hU
    refine ⟨(1 / 2 : ℂ) + ((ε / 2 : ℝ) : ℂ) * I, hεU ⟨?_, ?_⟩, hall _⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    · intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ _) hfreq
    (mem_univ s)

/-- **The reflected polynomial has the zeros of `D`, with the same orders.** At every point the
quotient `D^♯/D` has a nonzero limit. -/
theorem tendsto_reflPoly_div {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (hane : a ≠ 0)
    (hline : ∀ z : ℂ, finiteDirichletPolynomial a z = 0 → z.re = 1 / 2) (z : ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto (reflPoly a / finiteDirichletPolynomial a) (𝓝[≠] z) (𝓝 c) := by
  have hDd := differentiable_finiteDirichletPolynomial a ha0
  have hRd := differentiable_reflPoly ha0
  have hfix : ∀ u : ℂ, u.re = 1 / 2 → (1 : ℂ) - conj u = u := fun u hu => by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp
  by_cases hDz : finiteDirichletPolynomial a z = 0
  · -- a zero, on the line: factor `D` and reflect the factorization
    have hz := hfix z (hline z hDz)
    have hDan : AnalyticAt ℂ (finiteDirichletPolynomial a) z := hDd.analyticAt z
    have hfin : analyticOrderAt (finiteDirichletPolynomial a) z ≠ ⊤ := by
      intro htop
      rw [analyticOrderAt_eq_top] at htop
      exact finiteDirichletPolynomial_ne_zero a ha0 hane (funext fun s =>
        (hDd.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (mem_univ z) htop (mem_univ s))
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
    obtain ⟨h, hhan, hhne, hheq⟩ := hDan.analyticOrderAt_eq_natCast.mp hn.symm
    have hreflz : Tendsto (fun w : ℂ => 1 - conj w) (𝓝 z) (𝓝 z) := by
      have hc : Continuous fun w : ℂ => 1 - conj w := continuous_const.sub Complex.continuous_conj
      have := hc.tendsto z
      rwa [hz] at this
    have hheq' : ∀ᶠ w in 𝓝 z, finiteDirichletPolynomial a (1 - conj w)
        = (1 - conj w - z) ^ n • h (1 - conj w) := hreflz.eventually hheq
    have hhne' : ∀ᶠ w in 𝓝 z, h w ≠ 0 := hhan.continuousAt.eventually_ne hhne
    have hcz : conj z = 1 - z := by linear_combination -hz
    refine ⟨(-1) ^ n * (conj (h z) / h z), mul_ne_zero (pow_ne_zero _ (by norm_num))
      (div_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hhne) hhne), ?_⟩
    have hlim : Tendsto (fun w => (-1 : ℂ) ^ n * (conj (h (1 - conj w)) / h w)) (𝓝[≠] z)
        (𝓝 ((-1) ^ n * (conj (h z) / h z))) := by
      have h1 : Tendsto (fun w => conj (h (1 - conj w))) (𝓝 z) (𝓝 (conj (h z))) :=
        (Complex.continuous_conj.tendsto _).comp (hhan.continuousAt.tendsto.comp hreflz)
      exact ((h1.div hhan.continuousAt.tendsto hhne).const_mul _).mono_left nhdsWithin_le_nhds
    refine hlim.congr' ?_
    filter_upwards [nhdsWithin_le_nhds hheq, nhdsWithin_le_nhds hheq', nhdsWithin_le_nhds hhne',
      self_mem_nhdsWithin] with w hw1 hw2 hw3 hw4
    have hwz : w - z ≠ 0 := sub_ne_zero.mpr hw4
    have hc : conj (1 - conj w - z) = -(w - z) := by
      rw [map_sub, map_sub, map_one, Complex.conj_conj, hcz]
      ring
    simp only [Pi.div_apply]
    rw [reflPoly_eq ha0, hw2, hw1, smul_eq_mul, smul_eq_mul, map_mul, map_pow, hc,
      neg_pow (w - z) n, mul_assoc, mul_div_assoc, mul_div_mul_left _ _ (pow_ne_zero n hwz)]
  · -- not a zero: the reflected polynomial does not vanish either
    have hRz : reflPoly a z ≠ 0 := by
      intro h0
      rw [reflPoly_eq ha0, map_eq_zero] at h0
      have hre := hline _ h0
      have hre' : z.re = 1 / 2 := by
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
        linarith
      rw [hfix z hre'] at h0
      exact hDz h0
    exact ⟨reflPoly a z / finiteDirichletPolynomial a z, div_ne_zero hRz hDz,
      ((hRd.continuous.continuousAt.div hDd.continuous.continuousAt hDz).tendsto).mono_left
        nhdsWithin_le_nhds⟩

/-- **The quotient `D^♯/D` is an entire function without zeros.** -/
theorem exists_entire_quotient {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (hane : a ≠ 0)
    (hline : ∀ z : ℂ, finiteDirichletPolynomial a z = 0 → z.re = 1 / 2) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ w, g w ≠ 0) ∧ ∀ w, finiteDirichletPolynomial a w ≠ 0 →
      g w = reflPoly a w / finiteDirichletPolynomial a w := by
  have hDd := differentiable_finiteDirichletPolynomial a ha0
  have hRd := differentiable_reflPoly ha0
  have hmer : MeromorphicOn (reflPoly a / finiteDirichletPolynomial a) univ := fun z _ =>
    (hRd.analyticAt z).meromorphicAt.div (hDd.analyticAt z).meromorphicAt
  have hord : ∀ z, meromorphicOrderAt (reflPoly a / finiteDirichletPolynomial a) z = 0 := fun z =>
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hmer z (mem_univ z))).mp
      (tendsto_reflPoly_div ha0 hane hline z)
  have hNF := meromorphicNFOn_toMeromorphicNFOn (reflPoly a / finiteDirichletPolynomial a) univ
  have hord' : ∀ z, meromorphicOrderAt
      (toMeromorphicNFOn (reflPoly a / finiteDirichletPolynomial a) univ) z = 0 := fun z => by
    rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ z), hord z]
  refine ⟨toMeromorphicNFOn (reflPoly a / finiteDirichletPolynomial a) univ, fun z => ?_,
    fun z => ?_, fun w hw => ?_⟩
  · exact ((hNF (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by rw [hord' z])).differentiableAt
  · exact (hNF (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mp (hord' z)
  · have han : AnalyticAt ℂ (reflPoly a / finiteDirichletPolynomial a) w :=
      (hRd.analyticAt w).div (hDd.analyticAt w) hw
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hmer (mem_univ w),
      toMeromorphicNFAt_eq_self.mpr han.meromorphicNFAt]
    rfl

/-! ### The quotient is bounded on vertical strips -/

/-- **Good heights and the maximum principle.** If `g = D^♯/D` off the zeros of `D`, and `g` is
bounded on the two boundary lines of a vertical strip, it is bounded on the strip. -/
theorem exists_bound_on_strip {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (hane : a ≠ 0)
    (hline : ∀ z : ℂ, finiteDirichletPolynomial a z = 0 → z.re = 1 / 2) {g : ℂ → ℂ}
    (hgd : Differentiable ℂ g)
    (hg : ∀ w, finiteDirichletPolynomial a w ≠ 0 →
      g w = reflPoly a w / finiteDirichletPolynomial a w)
    {x₁ x₂ K₁ : ℝ} (hx : x₁ < x₂) (hK : ∀ w : ℂ, w.re = x₁ ∨ w.re = x₂ → ‖g w‖ ≤ K₁) :
    ∃ K : ℝ, ∀ w : ℂ, x₁ ≤ w.re → w.re ≤ x₂ → ‖g w‖ ≤ K := by
  obtain ⟨T₀, hT₀⟩ := exists_ne_zero_on_line ha0 hane
  have hDd := differentiable_finiteDirichletPolynomial a ha0
  -- `D` does not vanish on the horizontal line at height `T₀`
  have hseg : ∀ x : ℝ, finiteDirichletPolynomial a ((x : ℂ) + T₀ * I) ≠ 0 := by
    intro x h0
    have hre := hline _ h0
    have hx' : x = 1 / 2 := by simpa using hre
    rw [hx'] at h0
    exact hT₀ (by simpa using h0)
  have hcont : Continuous fun x : ℝ => ‖finiteDirichletPolynomial a ((x : ℂ) + T₀ * I)‖ :=
    (hDd.continuous.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + T₀ * I)).norm
  obtain ⟨x₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hx.le)
    (hcont.continuousOn (s := Icc x₁ x₂))
  have hm₀pos : 0 < ‖finiteDirichletPolynomial a ((x₀ : ℂ) + T₀ * I)‖ := norm_pos_iff.mpr (hseg x₀)
  have hm : ∀ x ∈ Icc x₁ x₂, ‖finiteDirichletPolynomial a ((x₀ : ℂ) + T₀ * I)‖
      ≤ ‖finiteDirichletPolynomial a ((x : ℂ) + T₀ * I)‖ := fun x hx => isMinOn_iff.mp hmin x hx
  -- almost periods of `D` on the strip
  have hsum : LSeriesSummable (fun n => a n) ((x₂ - 1 : ℝ) : ℂ) :=
    lSeriesSummable_of_finite_support (f := fun n => a n) ha0 a.support
      (fun n hn => Finsupp.notMem_support_iff.mp hn) _
  obtain ⟨L, hL, hτ⟩ := GaloisForLFunctions.isStripAlmostPeriodicOn_of_bounded_LSeries
    (x := x₁ - 1) (l' := x₁) (u := x₂) (u₀ := x₂ - 1) (by linarith) hx.le (by linarith) hsum
    hDd.differentiableOn (fun z hz => norm_finiteDirichletPolynomial_le a ha0 hz)
    (fun z _ => finiteDirichletPolynomial_eq_LSeries a ha0 z)
    (‖finiteDirichletPolynomial a ((x₀ : ℂ) + T₀ * I)‖ / 2) (by positivity)
  -- every interval of length `L` contains a height at which `D` is bounded below across the strip
  have hgood : ∀ y : ℝ, ∃ T ∈ Icc y (y + L), ∀ z : ℂ, x₁ ≤ z.re → z.re ≤ x₂ → z.im = T →
      ‖finiteDirichletPolynomial a ((x₀ : ℂ) + T₀ * I)‖ / 2 ≤ ‖finiteDirichletPolynomial a z‖ := by
    intro y
    obtain ⟨τ, hτmem, hτD⟩ := hτ (y - T₀)
    refine ⟨T₀ + τ, ⟨by linarith [hτmem.1], by linarith [hτmem.2]⟩, fun z hz1 hz2 hzT => ?_⟩
    have hzform : z = ((z.re : ℝ) : ℂ) + T₀ * I + τ * I := by
      apply Complex.ext <;> simp [hzT]
    have h1 := hτD (((z.re : ℝ) : ℂ) + T₀ * I)
      (by simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
          rw [abs_le]
          constructor <;> linarith)
    have h2 := hm z.re ⟨hz1, hz2⟩
    have h3 := norm_sub_norm_le (finiteDirichletPolynomial a (((z.re : ℝ) : ℂ) + T₀ * I))
      (finiteDirichletPolynomial a (((z.re : ℝ) : ℂ) + T₀ * I + τ * I))
    rw [norm_sub_rev] at h3
    rw [hzform]
    linarith
  set B : ℝ := ∑ n ∈ a.support, ‖a n‖ * (n : ℝ) ^ (x₂ - 1) with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun n _ => by positivity
  refine ⟨max K₁ (B / (‖finiteDirichletPolynomial a ((x₀ : ℂ) + T₀ * I)‖ / 2)), fun w hw1 hw2 => ?_⟩
  obtain ⟨T₁, hT₁mem, hT₁⟩ := hgood (w.im - L - 1)
  obtain ⟨T₂, hT₂mem, hT₂⟩ := hgood (w.im + 1)
  have hT₁w : T₁ < w.im := by linarith [hT₁mem.2]
  have hT₂w : w.im < T₂ := by linarith [hT₂mem.1]
  have hT : T₁ < T₂ := hT₁w.trans hT₂w
  -- the maximum principle on the rectangle between the two heights
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Ioo x₁ x₂ ×ℂ Ioo T₁ T₂)
    ((Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)) hgd.diffContOnCl
    (fun z hz => ?_) ?_
  · rw [Complex.frontier_reProdIm, closure_Ioo hx.ne, closure_Ioo hT.ne, frontier_Ioo hx,
      frontier_Ioo hT] at hz
    rcases hz with ⟨hre, him⟩ | ⟨hre, him⟩
    · have hD : ‖finiteDirichletPolynomial a ((x₀ : ℂ) + T₀ * I)‖ / 2
          ≤ ‖finiteDirichletPolynomial a z‖ := by
        rcases him with h | h
        · exact hT₁ z hre.1 hre.2 h
        · exact hT₂ z hre.1 hre.2 h
      have hD0 : finiteDirichletPolynomial a z ≠ 0 :=
        norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hD)
      rw [hg z hD0, norm_div]
      exact le_max_of_le_right (div_le_div₀ hB0 (norm_reflPoly_le ha0 hre.2) (by positivity) hD)
    · exact le_max_of_le_left (hK z hre)
  · rw [Complex.closure_reProdIm, closure_Ioo hx.ne, closure_Ioo hT.ne]
    exact ⟨⟨hw1, hw2⟩, ⟨hT₁w.le, hT₂w.le⟩⟩

/-! ### The functional equation -/

/-- **Zeros on the line force a functional equation.** -/
theorem exists_functionalEquation_of_zeros_on_line {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (ha1 : a 1 ≠ 0)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hn₀a : a n₀ ≠ 0)
    (hline : ∀ z : ℂ, finiteDirichletPolynomial a z = 0 → z.re = 1 / 2) :
    ∃ N : ℝ, 1 < N ∧ ∀ s : ℂ, ‖finiteDirichletPolynomial a (1 - conj s)‖
      = N ^ (s.re - 1 / 2) * ‖finiteDirichletPolynomial a s‖ := by
  have hane : a ≠ 0 := fun h => ha1 (by rw [h]; rfl)
  have hDd := differentiable_finiteDirichletPolynomial a ha0
  have ha1pos : 0 < ‖a 1‖ := norm_pos_iff.mpr ha1
  -- the top frequency
  have hsne : a.support.Nonempty := ⟨1, Finsupp.mem_support_iff.mpr ha1⟩
  obtain ⟨Nt, hNtmem, hNtmax⟩ : ∃ Nt ∈ a.support, ∀ n ∈ a.support, n ≤ Nt :=
    ⟨a.support.max' hsne, Finset.max'_mem _ _, fun n hn => Finset.le_max' _ n hn⟩
  have hNt2 : 2 ≤ Nt := hn₀.trans (hNtmax n₀ (Finsupp.mem_support_iff.mpr hn₀a))
  have haNt : 0 < ‖a Nt‖ := norm_pos_iff.mpr (Finsupp.mem_support_iff.mp hNtmem)
  have hNtr : (2 : ℝ) ≤ Nt := by exact_mod_cast hNt2
  obtain ⟨CL, hCL0, hleft⟩ := exists_left_bound ha0 hNtmem hNtmax hNt2
  obtain ⟨CR, hCR0, hright⟩ := exists_far_bound a ha0 ha1
  have hright' : ∀ w : ℂ, CR ≤ w.re → ‖a 1‖ / 2 ≤ ‖finiteDirichletPolynomial a w‖ := fun w hw => by
    have h := hright (fun _ => 1) (fun _ => by simp) (by simp) w hw
    rwa [twistPoly_one] at h
  have hleft' : ∀ w : ℂ, w.re ≤ -CL → ‖a Nt‖ / 2 ≤ ‖finiteDirichletPolynomial a w‖ := fun w hw => by
    refine le_trans ?_ (hleft w hw)
    have h1 : (1 : ℝ) ≤ (Nt : ℝ) ^ (-w.re) :=
      Real.one_le_rpow (by linarith) (by linarith)
    nlinarith [haNt]
  obtain ⟨g, hgd, hg0, hg⟩ := exists_entire_quotient ha0 hane hline
  set A : ℝ := ∑ n ∈ a.support, ‖a n‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hRexp := norm_reflPoly_le_exp ha0 hNtmax (by omega : 1 ≤ Nt)
  have hlogNt : 0 ≤ Real.log Nt := Real.log_nonneg (by linarith)
  -- bounds on the two half-planes
  have hgleft : ∀ w : ℂ, w.re ≤ -CL → ‖g w‖ ≤ A / (‖a Nt‖ / 2) := by
    intro w hw
    have hD := hleft' w hw
    have hD0 : finiteDirichletPolynomial a w ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (half_pos haNt) hD)
    rw [hg w hD0, norm_div]
    refine div_le_div₀ hA0 ?_ (half_pos haNt) hD
    have h := norm_reflPoly_le ha0 (c := 1) (s := w) (by linarith)
    simpa using h
  have hgright : ∀ w : ℂ, CR ≤ w.re →
      ‖g w‖ ≤ A * Real.exp (Real.log Nt * ‖w‖) / (‖a 1‖ / 2) := by
    intro w hw
    have hD := hright' w hw
    have hD0 : finiteDirichletPolynomial a w ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (half_pos ha1pos) hD)
    rw [hg w hD0, norm_div]
    exact div_le_div₀ (by positivity) (hRexp w) (half_pos ha1pos) hD
  -- the middle strip
  set BR : ℝ := ∑ n ∈ a.support, ‖a n‖ * (n : ℝ) ^ (CR + 1 - 1) with hBR
  have hBR0 : 0 ≤ BR := Finset.sum_nonneg fun n _ => by positivity
  obtain ⟨K, hK⟩ := exists_bound_on_strip ha0 hane hline hgd hg
    (x₁ := -CL - 1) (x₂ := CR + 1) (K₁ := max (A / (‖a Nt‖ / 2)) (BR / (‖a 1‖ / 2)))
    (by linarith) (fun w hw => by
      rcases hw with hw | hw
      · exact le_max_of_le_left (hgleft w (by linarith))
      · have hD := hright' w (by linarith)
        have hD0 : finiteDirichletPolynomial a w ≠ 0 :=
          norm_pos_iff.mp (lt_of_lt_of_le (half_pos ha1pos) hD)
        rw [hg w hD0, norm_div]
        exact le_max_of_le_right
          (div_le_div₀ hBR0 (norm_reflPoly_le ha0 hw.le) (half_pos ha1pos) hD))
  -- exponential type
  set Cg : ℝ := max K (max (A / (‖a Nt‖ / 2)) (A / (‖a 1‖ / 2))) with hCg
  have hgrow : ∀ w : ℂ, ‖g w‖ ≤ Cg * Real.exp (Real.log Nt * ‖w‖) := by
    intro w
    have hexp1 : 1 ≤ Real.exp (Real.log Nt * ‖w‖) :=
      Real.one_le_exp (mul_nonneg hlogNt (norm_nonneg _))
    have hCg0 : 0 ≤ Cg := le_max_of_le_right (le_max_of_le_left (by positivity))
    rcases le_or_gt w.re (-CL - 1) with h1 | h1
    · calc ‖g w‖ ≤ A / (‖a Nt‖ / 2) := hgleft w (by linarith)
        _ ≤ Cg := le_max_of_le_right (le_max_left _ _)
        _ ≤ Cg * Real.exp (Real.log Nt * ‖w‖) := le_mul_of_one_le_right hCg0 hexp1
    · rcases le_or_gt (CR + 1) w.re with h2 | h2
      · calc ‖g w‖ ≤ A * Real.exp (Real.log Nt * ‖w‖) / (‖a 1‖ / 2) := hgright w (by linarith)
          _ = A / (‖a 1‖ / 2) * Real.exp (Real.log Nt * ‖w‖) := by ring
          _ ≤ Cg * Real.exp (Real.log Nt * ‖w‖) :=
              mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _))
                (Real.exp_pos _).le
      · calc ‖g w‖ ≤ K := hK w h1.le h2.le
          _ ≤ Cg := le_max_left _ _
          _ ≤ Cg * Real.exp (Real.log Nt * ‖w‖) := le_mul_of_one_le_right hCg0 hexp1
  obtain ⟨α, β, hexp⟩ := exists_eq_exp_affine_of_ne_zero hgd hg0 hgrow
  -- the reflected polynomial is `g` times the polynomial, also at the zeros
  have hfix : ∀ u : ℂ, u.re = 1 / 2 → (1 : ℂ) - conj u = u := fun u hu => by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp
  have hnorm : ∀ s : ℂ, ‖finiteDirichletPolynomial a (1 - conj s)‖
      = Real.exp (α * s + β).re * ‖finiteDirichletPolynomial a s‖ := by
    intro s
    by_cases hD : finiteDirichletPolynomial a s = 0
    · rw [hfix s (hline s hD), hD, norm_zero, mul_zero]
    · have h1 : reflPoly a s = g s * finiteDirichletPolynomial a s := by
        rw [hg s hD, div_mul_cancel₀ _ hD]
      have h2 := congrArg norm h1
      rwa [reflPoly_eq ha0, RCLike.norm_conj, norm_mul, hexp, Complex.norm_exp] at h2
  -- on the line the modulus of `g` is one
  obtain ⟨T₀, hT₀⟩ := exists_ne_zero_on_line ha0 hane
  have hcontline : Continuous fun t : ℝ => finiteDirichletPolynomial a ((1 / 2 : ℂ) + t * I) :=
    hDd.continuous.comp (by fun_prop)
  obtain ⟨ε, hε, hεT⟩ := Metric.eventually_nhds_iff.mp (hcontline.continuousAt.eventually_ne hT₀)
  have hline1 : ∀ t : ℝ, finiteDirichletPolynomial a ((1 / 2 : ℂ) + t * I) ≠ 0 →
      α.re / 2 - α.im * t + β.re = 0 := by
    intro t ht
    have h := hnorm ((1 / 2 : ℂ) + t * I)
    rw [hfix _ (by simp)] at h
    have hpos : 0 < ‖finiteDirichletPolynomial a ((1 / 2 : ℂ) + t * I)‖ := norm_pos_iff.mpr ht
    have hone : Real.exp (α * ((1 / 2 : ℂ) + t * I) + β).re = 1 := by
      have := mul_right_cancel₀ hpos.ne' (show (1 : ℝ) * ‖finiteDirichletPolynomial a
        ((1 / 2 : ℂ) + t * I)‖ = Real.exp (α * ((1 / 2 : ℂ) + t * I) + β).re *
          ‖finiteDirichletPolynomial a ((1 / 2 : ℂ) + t * I)‖ by rw [one_mul]; exact h)
      exact this.symm
    have hzero := (Real.exp_eq_one_iff _).mp hone
    have hre : (α * ((1 / 2 : ℂ) + t * I) + β).re = α.re / 2 - α.im * t + β.re := by
      simp [Complex.mul_re]
      ring
    rwa [hre] at hzero
  have e1 := hline1 T₀ hT₀
  have e2 := hline1 (T₀ + ε / 2)
    (hεT (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]; linarith))
  have hαim : α.im = 0 := by
    have : α.im * (ε / 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  have hβ : β.re = -(α.re / 2) := by
    rw [hαim] at e1
    linarith
  have hre : ∀ s : ℂ, (α * s + β).re = α.re * (s.re - 1 / 2) := by
    intro s
    rw [Complex.add_re, Complex.mul_re, hαim, hβ]
    ring
  -- the conductor exceeds one
  have hαpos : 0 < α.re := by
    by_contra hneg
    have hαle : α.re ≤ 0 := not_lt.mp hneg
    set M₁ : ℝ := ∑ n ∈ a.support, ‖a n‖ * (n : ℝ) ^ (-(-1 : ℝ)) with hM₁
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * M₁ / ‖a Nt‖) (by norm_num : (1 : ℝ) < 2)
    set σ : ℝ := k + 1 + CL with hσ
    have hσ1 : (1 / 2 : ℝ) ≤ σ := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have h := hnorm (σ : ℂ)
    rw [hre, Complex.conj_ofReal, Complex.ofReal_re] at h
    have hexple : Real.exp (α.re * (σ - 1 / 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hαle (by linarith))
    have hDσ : ‖finiteDirichletPolynomial a (σ : ℂ)‖ ≤ M₁ :=
      norm_finiteDirichletPolynomial_le a ha0 (by simp; linarith)
    have hup : ‖finiteDirichletPolynomial a (1 - (σ : ℂ))‖ ≤ M₁ := by
      rw [h]
      exact (mul_le_of_le_one_left (norm_nonneg _) hexple).trans hDσ
    have hlow := hleft (1 - (σ : ℂ)) (by simp; linarith)
    have hrew : -(1 - (σ : ℂ)).re = k + CL := by simp [hσ]; ring
    rw [hrew] at hlow
    have hpow : (2 : ℝ) ^ k ≤ (Nt : ℝ) ^ ((k : ℝ) + CL) := by
      calc (2 : ℝ) ^ k ≤ (Nt : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hNtr k
        _ = (Nt : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
        _ ≤ (Nt : ℝ) ^ ((k : ℝ) + CL) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : 2 * M₁ / ‖a Nt‖ * (‖a Nt‖ / 2) = M₁ := by field_simp
    have h4 : M₁ < ‖a Nt‖ / 2 * (2 : ℝ) ^ k := by
      have := mul_lt_mul_of_pos_right hk (half_pos haNt)
      rw [h3] at this
      linarith
    have h5 : ‖a Nt‖ / 2 * (2 : ℝ) ^ k ≤ ‖a Nt‖ / 2 * (Nt : ℝ) ^ ((k : ℝ) + CL) :=
      mul_le_mul_of_nonneg_left hpow (half_pos haNt).le
    linarith
  refine ⟨Real.exp α.re, by have := Real.add_one_lt_exp hαpos.ne'; linarith, fun s => ?_⟩
  rw [hnorm s, hre s, ← Real.exp_mul]

/-! ### No factor with a constant term -/

/-- **A Dirichlet polynomial with a constant term and one further term has a zero that is not a
zero of `ξ`.** No functional equation is assumed: if all zeros were zeros of `ξ` they would lie on
the critical line, which forces the functional equation. -/
theorem exists_zero_not_xi_zero_of_constantTerm (a : ℕ →₀ ℂ) (ha0 : a 0 = 0) (ha1 : a 1 ≠ 0)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hn₀a : a n₀ ≠ 0) :
    ∃ z : ℂ, finiteDirichletPolynomial a z = 0 ∧ xi z ≠ 0 := by
  by_contra hcon
  have hall : ∀ z : ℂ, finiteDirichletPolynomial a z = 0 → xi z = 0 := fun z hz => by
    by_contra hxi
    exact hcon ⟨z, hz, hxi⟩
  have hane : a ≠ 0 := fun h => ha1 (by rw [h]; rfl)
  have hline : ∀ z : ℂ, finiteDirichletPolynomial a z = 0 → z.re = 1 / 2 := fun z hz =>
    re_eq_half_of_dirichletPolynomial_zeros_subset_xi a ha0 hane hall hz
  obtain ⟨N, hN, hFE⟩ := exists_functionalEquation_of_zeros_on_line ha0 ha1 hn₀ hn₀a hline
  exact hcon (exists_zero_not_xi_zero_of_functionalEquation_complex a ha0 ha1 hN hFE)

end GaloisForLFunctions.InfiniteRankPurityTheory
