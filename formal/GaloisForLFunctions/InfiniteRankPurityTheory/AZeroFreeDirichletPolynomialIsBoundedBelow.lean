import GaloisForLFunctions.RHTower.FiniteDirichletCriticalNonannihilation
import GaloisForLFunctions.FiniteFreeProbability.HurwitzDeflation

/-!
# A zero-free Dirichlet polynomial is bounded below

A Dirichlet polynomial `D(s) = Σ a_n n^{-s}` with a constant term and no zeros in `Re s > σ₀` is
bounded away from zero on every closed half-plane `Re s ≥ σ`, `σ > σ₀`. Zero-freeness alone gives
no bound on a half-plane; the bound comes from almost periodicity.

* `finiteDirichletPolynomial_add_mul_I`: a vertical translate of `D` is the Dirichlet polynomial
  with the twisted coefficients `a_n n^{-it}`.
* `exists_far_bound`: all twists by unimodular numbers are at least `|a_1|/2` in modulus on one
  half-plane `Re s ≥ C₀`.
* `tendstoLocallyUniformly_twistPoly`: twists converge locally uniformly when their coefficients
  converge.
* `exists_le_norm_of_zeroFree`: if `D(s_k) → 0` with `Re s_k ≥ σ`, the twists `n^{-i Im s_k}` and
  the real parts have a convergent subsequence; the limit polynomial is not identically zero and
  vanishes at a point of real part `≥ σ`; by Hurwitz the translates of `D`, hence `D`, have zeros
  right of `σ₀`.
-/

open Complex Filter Topology Set Metric

noncomputable section

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower

/-- The Dirichlet polynomial with the coefficients `a_n u_n`. -/
def twistPoly (a : ℕ →₀ ℂ) (u : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ a.support, a n * u n * (n : ℂ) ^ (-z)

theorem twistPoly_one (a : ℕ →₀ ℂ) (z : ℂ) :
    twistPoly a (fun _ => 1) z = finiteDirichletPolynomial a z := by
  simp only [twistPoly, finiteDirichletPolynomial, mul_one]

theorem pos_of_mem_support {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) {n : ℕ} (hn : n ∈ a.support) : 0 < n :=
  Nat.pos_of_ne_zero fun h => (Finsupp.mem_support_iff.mp hn) (h ▸ ha0)

/-- The unimodular twist `n^{-it}`. -/
def vtwist (t : ℝ) (n : ℕ) : ℂ := (n : ℂ) ^ (-(t : ℂ) * I)

theorem norm_vtwist_of_pos (t : ℝ) {n : ℕ} (hn : 0 < n) : ‖vtwist t n‖ = 1 := by
  rw [vtwist, Complex.norm_natCast_cpow_of_pos hn]
  simp

theorem norm_vtwist_le (t : ℝ) (n : ℕ) : ‖vtwist t n‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [vtwist, Nat.cast_zero]
    by_cases h : -(t : ℂ) * I = 0
    · rw [h, Complex.cpow_zero, norm_one]
    · rw [Complex.zero_cpow h, norm_zero]
      exact zero_le_one
  · exact (norm_vtwist_of_pos t hn).le

theorem vtwist_one (t : ℝ) : vtwist t 1 = 1 := by
  rw [vtwist, Nat.cast_one, Complex.one_cpow]

/-- A vertical translate of a Dirichlet polynomial is a twist. -/
theorem finiteDirichletPolynomial_add_mul_I {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (z : ℂ) (t : ℝ) :
    finiteDirichletPolynomial a (z + t * I) = twistPoly a (vtwist t) z := by
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_support ha0 hn).ne'
  rw [vtwist, mul_assoc, ← Complex.cpow_add _ _ hn0]
  congr 2
  ring

theorem differentiable_twistPoly {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (u : ℕ → ℂ) :
    Differentiable ℂ (twistPoly a u) := by
  intro z
  refine DifferentiableAt.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_support ha0 hn).ne'
  exact (differentiableAt_id.neg.const_cpow (Or.inl hn0)).const_mul _

/-- For `n ≥ 2` and `x ≥ 0`, `n^{-x} ≤ (1/2)^x`. -/
theorem rpow_neg_le_half_rpow {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    (n : ℝ) ^ (-x) ≤ (1 / 2 : ℝ) ^ x := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.rpow_neg (by linarith), ← Real.inv_rpow (by linarith)]
  refine Real.rpow_le_rpow (by positivity) ?_ hx
  rw [one_div]
  exact inv_anti₀ (by norm_num) hn2

/-- **The constant term dominates far to the right, uniformly in the twist.** -/
theorem exists_far_bound (a : ℕ →₀ ℂ) (ha0 : a 0 = 0) (ha1 : a 1 ≠ 0) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ u : ℕ → ℂ, (∀ n, ‖u n‖ ≤ 1) → ‖u 1‖ = 1 → ∀ z : ℂ, C₀ ≤ z.re →
      ‖a 1‖ / 2 ≤ ‖twistPoly a u z‖ := by
  set A : ℝ := ∑ n ∈ a.support, ‖a n‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have ha1pos : 0 < ‖a 1‖ := norm_pos_iff.mpr ha1
  have hlim : Tendsto (fun C : ℝ => A * (1 / 2 : ℝ) ^ C) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_atTop_of_base_lt_one (1 / 2 : ℝ) (by norm_num) (by norm_num)).const_mul A
  obtain ⟨C₀, hC₀, hC₀pos⟩ := ((hlim.eventually (gt_mem_nhds (half_pos ha1pos))).and
    (eventually_ge_atTop 0)).exists
  refine ⟨C₀, hC₀pos, fun u hu hu1 z hz => ?_⟩
  have h1mem : 1 ∈ a.support := Finsupp.mem_support_iff.mpr ha1
  have hzre : 0 ≤ z.re := hC₀pos.trans hz
  have hsplit : twistPoly a u z = a 1 * u 1
      + ∑ n ∈ a.support.erase 1, a n * u n * (n : ℂ) ^ (-z) := by
    rw [twistPoly, ← Finset.add_sum_erase _ _ h1mem, Nat.cast_one, Complex.one_cpow, mul_one]
  have htail : ‖∑ n ∈ a.support.erase 1, a n * u n * (n : ℂ) ^ (-z)‖ ≤ A * (1 / 2 : ℝ) ^ C₀ := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ n ∈ a.support.erase 1,
        ‖a n * u n * (n : ℂ) ^ (-z)‖ ≤ ‖a n‖ * (1 / 2 : ℝ) ^ C₀ := by
      intro n hn
      have hns := Finset.mem_of_mem_erase hn
      have hn0 := pos_of_mem_support ha0 hns
      have hn2 : 2 ≤ n := by
        have := Finset.ne_of_mem_erase hn
        omega
      rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
      have h1 : ‖a n‖ * ‖u n‖ ≤ ‖a n‖ := mul_le_of_le_one_right (norm_nonneg _) (hu n)
      have h2 : (n : ℝ) ^ (-z.re) ≤ (1 / 2 : ℝ) ^ C₀ :=
        (rpow_neg_le_half_rpow hn2 hzre).trans
          (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hz)
      exact mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    calc ∑ n ∈ a.support.erase 1, ‖a n * u n * (n : ℂ) ^ (-z)‖
        ≤ ∑ n ∈ a.support.erase 1, ‖a n‖ * (1 / 2 : ℝ) ^ C₀ := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ a.support, ‖a n‖ * (1 / 2 : ℝ) ^ C₀ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ => by positivity
      _ = A * (1 / 2 : ℝ) ^ C₀ := by rw [hA, Finset.sum_mul]
  have hmain : ‖a 1 * u 1‖ = ‖a 1‖ := by rw [norm_mul, hu1, mul_one]
  have h := norm_sub_le_norm_add (a 1 * u 1)
    (∑ n ∈ a.support.erase 1, a n * u n * (n : ℂ) ^ (-z))
  rw [hsplit]
  linarith

/-- **Twists converge locally uniformly when their coefficients converge.** -/
theorem tendstoLocallyUniformly_twistPoly {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) {u : ℕ → ℕ → ℂ}
    {v : ℕ → ℂ} (huv : ∀ n, Tendsto (fun k => u k n) atTop (𝓝 (v n))) :
    TendstoLocallyUniformly (fun k => twistPoly a (u k)) (twistPoly a v) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε z₀
  refine ⟨ball z₀ 1, ball_mem_nhds z₀ one_pos, ?_⟩
  -- on the unit ball about `z₀` each `n^{-z}` is at most `n^{|Re z₀| + 1}`
  have hlim : Tendsto (fun k => ∑ n ∈ a.support,
      ‖a n‖ * ‖v n - u k n‖ * (n : ℝ) ^ (|z₀.re| + 1)) atTop (𝓝 0) := by
    have h : ∀ n ∈ a.support, Tendsto (fun k => ‖a n‖ * ‖v n - u k n‖ * (n : ℝ) ^ (|z₀.re| + 1))
        atTop (𝓝 (‖a n‖ * 0 * (n : ℝ) ^ (|z₀.re| + 1))) := fun n _ => by
      have h0 : Tendsto (fun k => ‖v n - u k n‖) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := v n)).sub (huv n)
        rw [sub_self] at this
        exact tendsto_norm_zero.comp this
      exact (h0.const_mul _).mul_const _
    have hs := tendsto_finsetSum a.support h
    simpa using hs
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with k hk z hz
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hk
  have hre : |z.re - z₀.re| < 1 := by
    have h := (abs_re_le_norm (z - z₀)).trans_lt (mem_ball_iff_norm.mp hz)
    rwa [sub_re] at h
  rw [twistPoly, twistPoly, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn0 := pos_of_mem_support ha0 hn
  have hpt : a n * v n * (n : ℂ) ^ (-z) - a n * u k n * (n : ℂ) ^ (-z)
      = a n * (v n - u k n) * (n : ℂ) ^ (-z) := by ring
  rw [hpt, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
  refine mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn0) ?_) (by positivity)
  have h1 := abs_lt.mp hre
  have h2 := neg_abs_le z₀.re
  linarith

/-- **A zero-free Dirichlet polynomial is bounded below.** With a constant term and no zeros in
`Re s > σ₀`, it is bounded away from zero on `Re s ≥ σ` for every `σ > σ₀`. -/
theorem exists_le_norm_of_zeroFree {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) (ha1 : a 1 ≠ 0) {σ₀ σ : ℝ}
    (hσ : σ₀ < σ) (hzero : ∀ z : ℂ, σ₀ < z.re → finiteDirichletPolynomial a z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, σ ≤ s.re → δ ≤ ‖finiteDirichletPolynomial a s‖ := by
  obtain ⟨C₀, -, hfar⟩ := exists_far_bound a ha0 ha1
  have ha1pos : 0 < ‖a 1‖ := norm_pos_iff.mpr ha1
  by_contra hcon
  -- a sequence along which the polynomial tends to zero
  have hseq : ∀ k : ℕ, ∃ s : ℂ, σ ≤ s.re ∧
      ‖finiteDirichletPolynomial a s‖ < min (‖a 1‖ / 2) (1 / ((k : ℝ) + 1)) := by
    intro k
    by_contra hk
    refine hcon ⟨min (‖a 1‖ / 2) (1 / ((k : ℝ) + 1)), lt_min (half_pos ha1pos) (by positivity),
      fun s hs => ?_⟩
    by_contra hlt
    exact hk ⟨s, hs, not_le.mp hlt⟩
  choose s hsσ hsD using hseq
  have hsC : ∀ k, (s k).re ≤ C₀ := by
    intro k
    by_contra h
    have h1 := hfar (fun _ => 1) (fun _ => by simp) (by simp) (s k) (not_le.mp h).le
    rw [twistPoly_one] at h1
    exact absurd ((hsD k).trans_le (min_le_left _ _)) (not_lt.mpr h1)
  -- compactness of the real parts and of the twists
  have hK : IsCompact (Icc σ C₀ ×ˢ (Set.pi univ fun _ : ℕ => closedBall (0 : ℂ) 1)) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_closedBall 0 1)
  have hxK : ∀ k, ((s k).re, vtwist (s k).im) ∈
      Icc σ C₀ ×ˢ (Set.pi univ fun _ : ℕ => closedBall (0 : ℂ) 1) := fun k =>
    ⟨⟨hsσ k, hsC k⟩, fun n _ => mem_closedBall_zero_iff.mpr (norm_vtwist_le _ n)⟩
  obtain ⟨⟨x, v⟩, hmem, φ, hφ, hlim⟩ := hK.tendsto_subseq hxK
  have hx : Tendsto (fun k => (s (φ k)).re) atTop (𝓝 x) :=
    (continuous_fst.tendsto _).comp hlim
  have hv : ∀ n, Tendsto (fun k => vtwist (s (φ k)).im n) atTop (𝓝 (v n)) :=
    tendsto_pi_nhds.mp ((continuous_snd.tendsto _).comp hlim)
  have hvle : ∀ n, ‖v n‖ ≤ 1 := fun n => mem_closedBall_zero_iff.mp (hmem.2 n (mem_univ n))
  have hv1 : ‖v 1‖ = 1 := by
    have h := tendsto_nhds_unique (hv 1) (by simp only [vtwist_one]; exact tendsto_const_nhds)
    rw [h, norm_one]
  have hxσ : σ ≤ x := hmem.1.1
  -- the limit polynomial vanishes at `x` and is not identically zero
  have hconv := tendstoLocallyUniformly_twistPoly ha0 hv
  have hgd := differentiable_twistPoly ha0 v
  have hgx : twistPoly a v (x : ℂ) = 0 := by
    have h1 : Tendsto (fun k => twistPoly a (vtwist (s (φ k)).im) (((s (φ k)).re : ℝ) : ℂ)) atTop
        (𝓝 (twistPoly a v (x : ℂ))) :=
      hconv.tendsto_comp hgd.continuous.continuousAt
        ((Complex.continuous_ofReal.tendsto x).comp hx)
    have h2 : Tendsto (fun k => twistPoly a (vtwist (s (φ k)).im) (((s (φ k)).re : ℝ) : ℂ)) atTop
        (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hbound : ∀ k, ‖twistPoly a (vtwist (s (φ k)).im) (((s (φ k)).re : ℝ) : ℂ)‖
          ≤ 1 / ((k : ℝ) + 1) := by
        intro k
        rw [← finiteDirichletPolynomial_add_mul_I ha0, Complex.re_add_im]
        refine ((hsD (φ k)).trans_le (min_le_right _ _)).le.trans ?_
        have hk : (k : ℝ) ≤ φ k := by exact_mod_cast hφ.id_le k
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      exact squeeze_zero (fun _ => norm_nonneg _) hbound tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_nhds_unique h1 h2
  have hgC : twistPoly a v (C₀ : ℂ) ≠ 0 := by
    have h := hfar v hvle hv1 (C₀ : ℂ) (by simp)
    exact norm_pos_iff.mp (lt_of_lt_of_le (half_pos ha1pos) h)
  -- Hurwitz: the translates have zeros near `x`, right of `σ₀`
  obtain ⟨k, w, hw, hwz⟩ := (FiniteFreeProbability.eventually_exists_zero_of_tendstoLocallyUniformly
    hconv (fun k => differentiable_twistPoly ha0 _) hgd hgC hgx (sub_pos.mpr hσ)).exists
  rw [← finiteDirichletPolynomial_add_mul_I ha0] at hwz
  refine hzero _ ?_ hwz
  have h := abs_lt.mp ((abs_re_le_norm (w - (x : ℂ))).trans_lt (mem_ball_iff_norm.mp hw))
  rw [sub_re, Complex.ofReal_re] at h
  simp only [add_re, mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, mul_one, sub_self, add_zero]
  linarith [h.1]

end GaloisForLFunctions.InfiniteRankPurityTheory
