import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtCompactOpen

/-!
# Moving-pair compact-open continuity of the Hilbert--Carleman determinant

Hilbert--Schmidt convergence to a fixed kernel gives compact-open continuity of `entireDet2`.
For source families, however, both the physical kernel and a reference kernel can vary with the
same parameter.  This file proves the necessary moving-pair theorem: Hilbert--Schmidt distance
tending to zero, together with an eventual uniform Hilbert--Schmidt bound, gives locally uniform
convergence of the difference of the two entire regularized determinants to zero.
-/

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Metric Filter

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- A uniformly Hilbert--Schmidt-bounded moving pair has coefficientwise continuous
regularized determinants.  Unlike fixed-base continuity, both kernels may vary. -/
theorem tendsto_detCoeff_sub_of_hsNorm_sub_tendsto_zero_of_eventually_bound
    (A B : ℕ → ι × ι → ℂ)
    (hA : ∀ n, IsHS (A n)) (hB : ∀ n, IsHS (B n))
    (hlim : Tendsto (fun n => hsNorm (A n - B n)) atTop (nhds 0))
    (hbounded : ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n : ℕ in atTop, hsNorm (A n) ≤ M ∧ hsNorm (B n) ≤ M)
    (k : ℕ) :
    Tendsto (fun n => detCoeff (A n) k - detCoeff (B n) k) atTop (nhds 0) := by
  rcases hbounded with ⟨M, hM0, hbounded⟩
  set r : ℝ := 1 / (2 * M) with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hrM : r * M = 1 / 2 := by
    rw [hrdef]
    field_simp
  have hrMlt : r * M < 1 := by rw [hrM]; norm_num
  set ρ : ℝ := r / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hρr : ρ < r := by rw [hρdef]; linarith
  set C : ℝ := 2 * Real.exp ((r * M) ^ (2 : ℕ) / (1 - r * M)) with hCdef
  set L : ℝ := r ^ (2 : ℕ) * M / (1 - r * M) with hLdef
  have hL0 : 0 < L := by rw [hLdef, hrM]; positivity
  have hkey : ∀ n : ℕ, hsNorm (A n) ≤ M → hsNorm (B n) ≤ M →
      hsNorm (A n - B n) * L ≤ 1 →
      ‖detCoeff (A n) k - detCoeff (B n) k‖ ≤
        (C * (hsNorm (A n - B n) * L)) / ρ ^ k := by
    intro n hAM hBM hsmall
    have hAdiff : DifferentiableOn ℂ (fun z => fredholmDet (A n) z) (ball (0 : ℂ) r) :=
      fredholmDet_differentiableOn (hA n) r
        (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hAM hr0.le) hrMlt)
    have hBdiff : DifferentiableOn ℂ (fun z => fredholmDet (B n) z) (ball (0 : ℂ) r) :=
      fredholmDet_differentiableOn (hB n) r
        (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hBM hr0.le) hrMlt)
    have hsubeq : detCoeff (A n) k - detCoeff (B n) k =
        taylorCoeff ((fun z => fredholmDet (A n) z) - fun z => fredholmDet (B n) z) k := by
      simp only [detCoeff, taylorCoeff]
      rw [iteratedDeriv_sub
        ((hAdiff.analyticAt (isOpen_ball.mem_nhds (by simpa using hr0))).contDiffAt)
        ((hBdiff.analyticAt (isOpen_ball.mem_nhds (by simpa using hr0))).contDiffAt)]
      ring
    rw [hsubeq]
    refine norm_taylorCoeff_le' hρ0 ?_ ?_ k
    · exact diffContOnCl_of_differentiableOn_ball hρ0 hρr (hAdiff.sub hBdiff)
    · intro z hz
      have hzr : ‖z‖ ≤ r := by
        rw [hz, hρdef]
        linarith
      have hdet := norm_fredholmDet_sub_le (hA n) (hB n) hr0.le hAM hBM hM0.le
        hrMlt hzr (by rw [← hLdef]; exact hsmall)
      simpa [hCdef, hLdef] using hdet
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hmaj : Tendsto (fun n : ℕ =>
      (C * (hsNorm (A n - B n) * L)) / ρ ^ k) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => C * (hsNorm (A n - B n) * L)) atTop (nhds 0) := by
      simpa using (hlim.mul_const L).const_mul C
    simpa using h1.div_const (ρ ^ k)
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hmaj
  have hevsmall : ∀ᶠ n : ℕ in atTop, hsNorm (A n - B n) * L ≤ 1 := by
    have hnear := hlim.eventually (ge_mem_nhds (show (0 : ℝ) < L⁻¹ by positivity))
    filter_upwards [hnear] with n hn
    rw [← le_div_iff₀ hL0]
    simpa [div_eq_mul_inv] using hn
  filter_upwards [hbounded, hevsmall] with n hn hs
  simpa using hkey n hn.1 hn.2 hs

/-- The weighted coefficient-difference series of a uniformly bounded moving pair vanishes. -/
theorem tendsto_tsum_norm_detCoeff_sub_of_hsNorm_sub_tendsto_zero_of_eventually_bound
    (A B : ℕ → ι × ι → ℂ)
    (hA : ∀ n, IsHS (A n)) (hB : ∀ n, IsHS (B n))
    (hlim : Tendsto (fun n => hsNorm (A n - B n)) atTop (nhds 0))
    (hbounded : ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n : ℕ in atTop, hsNorm (A n) ≤ M ∧ hsNorm (B n) ≤ M)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun k => ∑' n : ℕ,
      ‖detCoeff (A k) n - detCoeff (B k) n‖ * ρ ^ n) atTop (nhds 0) := by
  rcases hbounded with ⟨M, hM0, hbounded⟩
  set E : ℝ := Real.exp ((2 * ρ) ^ (2 : ℕ) * M ^ (2 : ℕ) / 2) with hEdef
  set bnd : ℕ → ℝ := fun n => 2 * E * (1 / 2) ^ n with hbnd
  have hsumbnd : Summable bnd := by
    rw [hbnd]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (2 * E)
  have hkernel_bound : ∀ (K : ι × ι → ℂ), IsHS K → hsNorm K ≤ M → ∀ n,
      ‖detCoeff K n‖ * ρ ^ n ≤ E * (1 / 2) ^ n := by
    intro K hK hKM n
    have hKsq : hsNormSq K ≤ M ^ (2 : ℕ) := by
      have heq : hsNormSq K = hsNorm K ^ (2 : ℕ) := by
        rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg K)]
      rw [heq]
      exact pow_le_pow_left₀ (hsNorm_nonneg K) hKM 2
    calc
      ‖detCoeff K n‖ * ρ ^ n
          ≤ Real.exp ((2 * ρ) ^ (2 : ℕ) * hsNormSq K / 2) * (1 / 2) ^ n :=
            norm_detCoeff_mul_pow_le hK hρ n
      _ ≤ E * (1 / 2) ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hEdef]
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (2 * ρ)])
  have hdom : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      ‖‖detCoeff (A k) n - detCoeff (B k) n‖ * ρ ^ n‖ ≤ bnd n := by
    filter_upwards [hbounded] with k hk n
    have h1 := hkernel_bound (A k) (hA k) hk.1 n
    have h2 := hkernel_bound (B k) (hB k) hk.2 n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hbnd]
    have hsplit : ‖detCoeff (A k) n - detCoeff (B k) n‖ * ρ ^ n
        ≤ ‖detCoeff (A k) n‖ * ρ ^ n + ‖detCoeff (B k) n‖ * ρ ^ n := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
    linarith
  have hbounded' : ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n : ℕ in atTop, hsNorm (A n) ≤ M ∧ hsNorm (B n) ≤ M :=
    ⟨M, hM0, hbounded⟩
  have hpoint : ∀ n : ℕ, Tendsto
      (fun k => ‖detCoeff (A k) n - detCoeff (B k) n‖ * ρ ^ n) atTop
      (nhds ((0 : ℝ) * ρ ^ n)) := by
    intro n
    have h0 : Tendsto (fun k => ‖detCoeff (A k) n - detCoeff (B k) n‖)
        atTop (nhds 0) := by
      simpa using
        (tendsto_detCoeff_sub_of_hsNorm_sub_tendsto_zero_of_eventually_bound
          A B hA hB hlim hbounded' n).norm
    exact h0.mul_const (ρ ^ n)
  have hmain := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun k n => ‖detCoeff (A k) n - detCoeff (B k) n‖ * ρ ^ n)
    (g := fun _ : ℕ => (0 : ℝ)) hsumbnd (by simpa using hpoint) hdom
  simpa using hmain

/-- Compact-open continuity of `entireDet2` for a uniformly bounded moving pair. -/
theorem tendstoUniformlyOn_sub_entireDet2_of_hsNorm_sub_tendsto_zero_of_eventually_bound
    (A B : ℕ → ι × ι → ℂ)
    (hA : ∀ n, IsHS (A n)) (hB : ∀ n, IsHS (B n))
    (hlim : Tendsto (fun n => hsNorm (A n - B n)) atTop (nhds 0))
    (hbounded : ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n : ℕ in atTop, hsNorm (A n) ≤ M ∧ hsNorm (B n) ≤ M)
    {ρ : ℝ} (hρ : 0 < ρ) :
    TendstoUniformlyOn (fun k z => entireDet2 (A k) z - entireDet2 (B k) z)
      (fun _ => 0) atTop (closedBall (0 : ℂ) ρ) := by
  rcases hbounded with ⟨M, hM0, hbounded⟩
  set E : ℝ := Real.exp ((2 * ρ) ^ (2 : ℕ) * M ^ (2 : ℕ) / 2) with hEdef
  have hkernel_bound : ∀ (K : ι × ι → ℂ), IsHS K → hsNorm K ≤ M → ∀ n,
      ‖detCoeff K n‖ * ρ ^ n ≤ E * (1 / 2) ^ n := by
    intro K hK hKM n
    have hKsq : hsNormSq K ≤ M ^ (2 : ℕ) := by
      have heq : hsNormSq K = hsNorm K ^ (2 : ℕ) := by
        rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg K)]
      rw [heq]
      exact pow_le_pow_left₀ (hsNorm_nonneg K) hKM 2
    calc
      ‖detCoeff K n‖ * ρ ^ n
          ≤ Real.exp ((2 * ρ) ^ (2 : ℕ) * hsNormSq K / 2) * (1 / 2) ^ n :=
            norm_detCoeff_mul_pow_le hK hρ n
      _ ≤ E * (1 / 2) ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hEdef]
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (2 * ρ)])
  have hsum : ∀ k, hsNorm (A k) ≤ M → hsNorm (B k) ≤ M → Summable fun n : ℕ =>
      ‖detCoeff (A k) n - detCoeff (B k) n‖ * ρ ^ n := by
    intro k hAM hBM
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_geometric_of_lt_one
        (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)).mul_left
          (2 * E))
    have h1 := hkernel_bound (A k) (hA k) hAM n
    have h2 := hkernel_bound (B k) (hB k) hBM n
    have hsplit : ‖detCoeff (A k) n - detCoeff (B k) n‖ * ρ ^ n
        ≤ ‖detCoeff (A k) n‖ * ρ ^ n + ‖detCoeff (B k) n‖ * ρ ^ n := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
    linarith
  have hpt : ∀ k, hsNorm (A k) ≤ M → hsNorm (B k) ≤ M → ∀ z ∈ closedBall (0 : ℂ) ρ,
      dist (entireDet2 (A k) z) (entireDet2 (B k) z)
        ≤ ∑' n : ℕ, ‖detCoeff (A k) n - detCoeff (B k) n‖ * ρ ^ n := by
    intro k hAM hBM z hz
    have hzρ : ‖z‖ ≤ ρ := by simpa using mem_closedBall_zero_iff.mp hz
    have hsA : Summable fun n : ℕ => detCoeff (A k) n * z ^ n :=
      summable_of_orderTwo_bound (c := hsNormSq (A k))
        (fun R hR n => norm_detCoeff_le (hA k) hR n) z
    have hsB : Summable fun n : ℕ => detCoeff (B k) n * z ^ n :=
      summable_of_orderTwo_bound (c := hsNormSq (B k))
        (fun R hR n => norm_detCoeff_le (hB k) hR n) z
    rw [entireDet2, entireOfCoeffs, entireDet2, entireOfCoeffs, Complex.dist_eq,
      ← hsA.tsum_sub hsB]
    refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
    · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hsum k hAM hBM)
      rw [← sub_mul, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg z) hzρ n) (norm_nonneg _)
    · refine Summable.tsum_le_tsum (fun n => ?_) ?_ (hsum k hAM hBM)
      · rw [← sub_mul, norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg z) hzρ n) (norm_nonneg _)
      · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hsum k hAM hBM)
        rw [← sub_mul, norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg z) hzρ n) (norm_nonneg _)
  have hbounded' : ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n : ℕ in atTop, hsNorm (A n) ≤ M ∧ hsNorm (B n) ≤ M :=
    ⟨M, hM0, hbounded⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hdrop :=
    (tendsto_tsum_norm_detCoeff_sub_of_hsNorm_sub_tendsto_zero_of_eventually_bound
      A B hA hB hlim hbounded' hρ).eventually (eventually_lt_nhds hε)
  filter_upwards [hbounded, hdrop] with k hk hsmall z hz
  have hle := hpt k hk.1 hk.2 z hz
  have hlt : dist (entireDet2 (A k) z) (entireDet2 (B k) z) < ε :=
    lt_of_le_of_lt hle hsmall
  simpa only [Complex.dist_eq, zero_sub, norm_neg] using hlt

/-- Locally uniform moving-pair continuity of the Hilbert--Carleman determinant. -/
theorem tendstoLocallyUniformly_sub_entireDet2_of_hsNorm_sub_tendsto_zero_of_eventually_bound
    (A B : ℕ → ι × ι → ℂ)
    (hA : ∀ n, IsHS (A n)) (hB : ∀ n, IsHS (B n))
    (hlim : Tendsto (fun n => hsNorm (A n - B n)) atTop (nhds 0))
    (hbounded : ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n : ℕ in atTop, hsNorm (A n) ≤ M ∧ hsNorm (B n) ≤ M) :
    TendstoLocallyUniformly (fun k z => entireDet2 (A k) z - entireDet2 (B k) z)
      (fun _ => 0) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro C hC
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hC.isBounded
  have hρ : (0 : ℝ) < max r 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  exact (tendstoUniformlyOn_sub_entireDet2_of_hsNorm_sub_tendsto_zero_of_eventually_bound
    A B hA hB hlim hbounded hρ).mono
      (hr.trans (closedBall_subset_closedBall (le_max_left _ _)))

end GaloisForLFunctions.HTGeometry
