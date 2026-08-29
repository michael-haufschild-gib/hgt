import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex

/-!
# Polynomials approximate entire functions uniformly on balls

The Taylor partial sums of an entire function converge to it uniformly on every closed ball: on the
ball of radius `R` Cauchy's estimate at radius `2R` bounds the `k`-th term by `C·2^{-k}`, so the
tail is a geometric remainder.  This is the density statement behind "a continuous linear
observation of an entire function is already realized by a polynomial".

* `taylorPoly` — the `n`-th Taylor partial sum as an honest `Polynomial ℂ`.
* `tendstoUniformlyOn_taylorPoly` — uniform convergence on every closed ball.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Metric

noncomputable section

/-- The `n`-th Taylor partial sum of `g` at the origin, as a polynomial. -/
def taylorPoly (g : ℂ → ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range n,
    Polynomial.C (iteratedDeriv k g 0 / (Nat.factorial k : ℂ)) * Polynomial.X ^ k

theorem eval_taylorPoly (g : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    (taylorPoly g n).eval z
      = ∑ k ∈ Finset.range n, (iteratedDeriv k g 0 / (Nat.factorial k : ℂ)) * z ^ k := by
  simp [taylorPoly, Polynomial.eval_finset_sum]

/-- **Geometric Cauchy bound.**  On the ball of radius `R` the `k`-th Taylor term of an entire
function is at most `C·2^{-k}`, with `C` a bound for the function on the circle of radius `2R`. -/
theorem exists_taylor_geometric_bound {g : ℂ → ℂ} (hg : Differentiable ℂ g) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      ‖iteratedDeriv k g 0 / (Nat.factorial k : ℂ)‖ * R ^ k ≤ C * (1 / 2 : ℝ) ^ k := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) (2 * R)).exists_bound_of_continuousOn
    hg.continuous.continuousOn
  have hC0 : 0 ≤ C := by
    have hne : (Metric.sphere (0 : ℂ) (2 * R)).Nonempty :=
      NormedSpace.sphere_nonempty.mpr (by linarith)
    obtain ⟨w, hw⟩ := hne
    exact le_trans (norm_nonneg _) (hC w hw)
  refine ⟨C, hC0, fun k => ?_⟩
  have h2R : (0 : ℝ) < 2 * R := by linarith
  have hcauchy := taylorCoeff_norm_mul_pow_le hg h2R hC k
  have hsplit : ‖iteratedDeriv k g 0 / (Nat.factorial k : ℂ)‖ * R ^ k
      = (‖iteratedDeriv k g 0 / (Nat.factorial k : ℂ)‖ * (2 * R) ^ k) * (1 / 2 : ℝ) ^ k := by
    rw [mul_assoc, ← mul_pow]
    congr 2
    field_simp
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hcauchy (by positivity)

/-- **Uniform polynomial approximation on balls.**  The Taylor partial sums of an entire function
converge to it uniformly on every closed ball centred at the origin. -/
theorem tendstoUniformlyOn_taylorPoly {g : ℂ → ℂ} (hg : Differentiable ℂ g) {R : ℝ} (hR : 0 < R) :
    TendstoUniformlyOn (fun n z => (taylorPoly g n).eval z) g atTop (closedBall (0 : ℂ) R) := by
  classical
  set co : ℕ → ℂ := fun k => iteratedDeriv k g 0 / (Nat.factorial k : ℂ) with hcodef
  obtain ⟨C, hC0, hCk⟩ := exists_taylor_geometric_bound hg hR
  have hgeom : Summable fun k : ℕ => C * (1 / 2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  -- the tail bound
  have hkey : ∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) R,
      ‖g z - (taylorPoly g n).eval z‖ ≤ 2 * C * (1 / 2 : ℝ) ^ n := by
    intro n z hz
    have hzR : ‖z‖ ≤ R := by simpa [Complex.dist_eq] using hz
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hterm : ∀ k : ℕ, ‖co k * z ^ k‖ ≤ C * (1 / 2 : ℝ) ^ k := by
      intro k
      rw [norm_mul, norm_pow]
      refine le_trans ?_ (hCk k)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hzR k) (norm_nonneg _)
    have hsum : HasSum (fun k => co k * z ^ k) (g z) := by
      have h := Complex.hasSum_taylorSeries_of_entire hg 0 z
      refine h.congr_fun fun k => ?_
      simp only [hcodef, sub_zero, smul_eq_mul]
      ring
    have hsummable : Summable fun k => co k * z ^ k := hsum.summable
    have hnormsummable : Summable fun k => ‖co k * z ^ k‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm hgeom
    have hshift : Summable fun k => co (k + n) * z ^ (k + n) :=
      (summable_nat_add_iff n).mpr hsummable
    have hsplit := Summable.sum_add_tsum_nat_add (f := fun k => co k * z ^ k) n hsummable
    have hgz : g z = (∑ k ∈ Finset.range n, co k * z ^ k) + ∑' k, co (k + n) * z ^ (k + n) := by
      rw [hsplit, hsum.tsum_eq]
    have hdiff : g z - (taylorPoly g n).eval z = ∑' k, co (k + n) * z ^ (k + n) := by
      rw [hgz, eval_taylorPoly]
      ring
    rw [hdiff]
    have hnormshift : Summable fun k => ‖co (k + n) * z ^ (k + n)‖ :=
      (summable_nat_add_iff n).mpr hnormsummable
    have hbound : ∀ k : ℕ, ‖co (k + n) * z ^ (k + n)‖ ≤ (C * (1 / 2 : ℝ) ^ n) * (1 / 2 : ℝ) ^ k := by
      intro k
      refine le_trans (hterm (k + n)) (le_of_eq ?_)
      rw [pow_add]
      ring
    have hgeom' : Summable fun k : ℕ => (C * (1 / 2 : ℝ) ^ n) * (1 / 2 : ℝ) ^ k :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    calc ‖∑' k, co (k + n) * z ^ (k + n)‖
        ≤ ∑' k, ‖co (k + n) * z ^ (k + n)‖ := norm_tsum_le_tsum_norm hnormshift
      _ ≤ ∑' k : ℕ, (C * (1 / 2 : ℝ) ^ n) * (1 / 2 : ℝ) ^ k :=
          Summable.tsum_le_tsum hbound hnormshift hgeom'
      _ = 2 * C * (1 / 2 : ℝ) ^ n := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
          ring
  -- convert the tail bound into uniform convergence
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have htend : Tendsto (fun n : ℕ => 2 * C * (1 / 2 : ℝ) ^ n) atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (1/2 : ℝ) < 1)
    simpa using this.const_mul (2 * C)
  filter_upwards [htend.eventually (gt_mem_nhds hε)] with n hn
  intro z hz
  have h := hkey n z hz
  rw [Complex.dist_eq]
  calc ‖g z - (taylorPoly g n).eval z‖ ≤ 2 * C * (1 / 2 : ℝ) ^ n := h
    _ < ε := hn

end

end GaloisForLFunctions.HTGeometry
