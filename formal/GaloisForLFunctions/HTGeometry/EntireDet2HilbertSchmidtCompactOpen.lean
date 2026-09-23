import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtContinuity

/-!
# Compact-open continuity of the Hilbert--Carleman determinant

Hilbert--Schmidt convergence of kernels gives compact-open convergence of their canonical entire
regularized determinants.  The proof upgrades coefficientwise continuity with one Carleman
geometric majorant on each closed disc.  This is the topology needed to transport complete bounded
zero divisors, including multiplicity.
-/

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Metric Filter

variable {ι : Type*} [DecidableEq ι]

theorem tendsto_tsum_norm_detCoeff_sub_of_hsNorm_sub_tendsto_zero
    (K : ℕ → ι × ι → ℂ) (K₀ : ι × ι → ℂ)
    (hK : ∀ n, IsHS (K n)) (hK₀ : IsHS K₀)
    (hlim : Tendsto (fun n => hsNorm (K n - K₀)) atTop (nhds 0))
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun k => ∑' n : ℕ,
      ‖detCoeff (K k) n - detCoeff K₀ n‖ * ρ ^ n) atTop (nhds 0) := by
  set M : ℝ := hsNorm K₀ + 1 with hMdef
  have hM0 : 0 < M := by
    have := hsNorm_nonneg K₀
    simp only [hMdef]
    linarith
  have hK₀M : hsNorm K₀ ≤ M := by simp [hMdef]
  have hbounded : ∀ᶠ k : ℕ in atTop, hsNorm (K k) ≤ M := by
    have hsmall := hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsmall] with k hk
    have hsplit : hsNorm (K k) ≤ hsNorm (K k - K₀) + hsNorm K₀ := by
      have heq : K k = (K k - K₀) + K₀ := by
        funext p
        simp
      calc
        hsNorm (K k) = hsNorm ((K k - K₀) + K₀) := congrArg hsNorm heq
        _ ≤ hsNorm (K k - K₀) + hsNorm K₀ :=
          hsNorm_add_le (isHS_sub (hK k) hK₀) hK₀
    rw [hMdef]
    linarith
  set E : ℝ := Real.exp ((2 * ρ) ^ (2 : ℕ) * M ^ (2 : ℕ) / 2) with hEdef
  set bnd : ℕ → ℝ := fun n => 2 * E * (1 / 2) ^ n with hbnd
  have hsumbnd : Summable bnd := by
    rw [hbnd]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (2 * E)
  have hkernel_bound : ∀ (A : ι × ι → ℂ), IsHS A → hsNorm A ≤ M → ∀ n,
      ‖detCoeff A n‖ * ρ ^ n ≤ E * (1 / 2) ^ n := by
    intro A hA hAM n
    have hAsq : hsNormSq A ≤ M ^ (2 : ℕ) := by
      have heq : hsNormSq A = hsNorm A ^ (2 : ℕ) := by
        rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg A)]
      rw [heq]
      exact pow_le_pow_left₀ (hsNorm_nonneg A) hAM 2
    calc
      ‖detCoeff A n‖ * ρ ^ n
          ≤ Real.exp ((2 * ρ) ^ (2 : ℕ) * hsNormSq A / 2) * (1 / 2) ^ n :=
            norm_detCoeff_mul_pow_le hA hρ n
      _ ≤ E * (1 / 2) ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hEdef]
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (2 * ρ)])
  have hbound : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      ‖‖detCoeff (K k) n - detCoeff K₀ n‖ * ρ ^ n‖ ≤ bnd n := by
    filter_upwards [hbounded] with k hk n
    have h1 := hkernel_bound (K k) (hK k) hk n
    have h2 := hkernel_bound K₀ hK₀ hK₀M n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hbnd]
    have hsplit : ‖detCoeff (K k) n - detCoeff K₀ n‖ * ρ ^ n
        ≤ ‖detCoeff (K k) n‖ * ρ ^ n + ‖detCoeff K₀ n‖ * ρ ^ n := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
    linarith
  have hpoint : ∀ n : ℕ, Tendsto
      (fun k => ‖detCoeff (K k) n - detCoeff K₀ n‖ * ρ ^ n) atTop
      (nhds ((0 : ℝ) * ρ ^ n)) := by
    intro n
    have h0 : Tendsto (fun k => ‖detCoeff (K k) n - detCoeff K₀ n‖) atTop (nhds 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp
        (tendsto_detCoeff_of_hsNorm_sub_tendsto_zero K K₀ hK hK₀ hlim n)
    exact h0.mul_const (ρ ^ n)
  have hmain := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun k n => ‖detCoeff (K k) n - detCoeff K₀ n‖ * ρ ^ n)
    (g := fun _ : ℕ => (0 : ℝ)) hsumbnd (by simpa using hpoint) hbound
  simpa using hmain

theorem tendstoUniformlyOn_entireDet2_of_hsNorm_sub_tendsto_zero
    (K : ℕ → ι × ι → ℂ) (K₀ : ι × ι → ℂ)
    (hK : ∀ n, IsHS (K n)) (hK₀ : IsHS K₀)
    (hlim : Tendsto (fun n => hsNorm (K n - K₀)) atTop (nhds 0))
    {ρ : ℝ} (hρ : 0 < ρ) :
    TendstoUniformlyOn (fun k z => entireDet2 (K k) z) (entireDet2 K₀)
      atTop (closedBall (0 : ℂ) ρ) := by
  set M : ℝ := hsNorm K₀ + 1 with hMdef
  have hbounded : ∀ᶠ k : ℕ in atTop, hsNorm (K k) ≤ M := by
    have hsmall := hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsmall] with k hk
    have hsplit : hsNorm (K k) ≤ hsNorm (K k - K₀) + hsNorm K₀ := by
      have heq : K k = (K k - K₀) + K₀ := by
        funext p
        simp
      calc
        hsNorm (K k) = hsNorm ((K k - K₀) + K₀) := congrArg hsNorm heq
        _ ≤ hsNorm (K k - K₀) + hsNorm K₀ :=
          hsNorm_add_le (isHS_sub (hK k) hK₀) hK₀
    rw [hMdef]
    linarith
  set E : ℝ := Real.exp ((2 * ρ) ^ (2 : ℕ) * M ^ (2 : ℕ) / 2) with hEdef
  have hK₀M : hsNorm K₀ ≤ M := by simp [hMdef]
  have hkernel_bound : ∀ (A : ι × ι → ℂ), IsHS A → hsNorm A ≤ M → ∀ n,
      ‖detCoeff A n‖ * ρ ^ n ≤ E * (1 / 2) ^ n := by
    intro A hA hAM n
    have hAsq : hsNormSq A ≤ M ^ (2 : ℕ) := by
      have heq : hsNormSq A = hsNorm A ^ (2 : ℕ) := by
        rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg A)]
      rw [heq]
      exact pow_le_pow_left₀ (hsNorm_nonneg A) hAM 2
    calc
      ‖detCoeff A n‖ * ρ ^ n
          ≤ Real.exp ((2 * ρ) ^ (2 : ℕ) * hsNormSq A / 2) * (1 / 2) ^ n :=
            norm_detCoeff_mul_pow_le hA hρ n
      _ ≤ E * (1 / 2) ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hEdef]
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (2 * ρ)])
  have hsum : ∀ k, hsNorm (K k) ≤ M → Summable fun n : ℕ =>
      ‖detCoeff (K k) n - detCoeff K₀ n‖ * ρ ^ n := by
    intro k hk
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_geometric_of_lt_one
        (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)).mul_left
          (2 * E))
    have h1 := hkernel_bound (K k) (hK k) hk n
    have h2 := hkernel_bound K₀ hK₀ hK₀M n
    have hsplit : ‖detCoeff (K k) n - detCoeff K₀ n‖ * ρ ^ n
        ≤ ‖detCoeff (K k) n‖ * ρ ^ n + ‖detCoeff K₀ n‖ * ρ ^ n := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
    linarith
  have hpt : ∀ k, hsNorm (K k) ≤ M → ∀ z ∈ closedBall (0 : ℂ) ρ,
      dist (entireDet2 (K k) z) (entireDet2 K₀ z)
        ≤ ∑' n : ℕ, ‖detCoeff (K k) n - detCoeff K₀ n‖ * ρ ^ n := by
    intro k hk z hz
    have hzρ : ‖z‖ ≤ ρ := by simpa using mem_closedBall_zero_iff.mp hz
    have hsA : Summable fun n : ℕ => detCoeff (K k) n * z ^ n :=
      summable_of_orderTwo_bound (c := hsNormSq (K k))
        (fun R hR n => norm_detCoeff_le (hK k) hR n) z
    have hsB : Summable fun n : ℕ => detCoeff K₀ n * z ^ n :=
      summable_of_orderTwo_bound (c := hsNormSq K₀)
        (fun R hR n => norm_detCoeff_le hK₀ hR n) z
    rw [entireDet2, entireOfCoeffs, entireDet2, entireOfCoeffs, Complex.dist_eq,
      ← hsA.tsum_sub hsB]
    refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
    · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hsum k hk)
      rw [← sub_mul, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg z) hzρ n) (norm_nonneg _)
    · refine Summable.tsum_le_tsum (fun n => ?_) ?_ (hsum k hk)
      · rw [← sub_mul, norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg z) hzρ n) (norm_nonneg _)
      · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hsum k hk)
        rw [← sub_mul, norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg z) hzρ n) (norm_nonneg _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hdrop :=
    (tendsto_tsum_norm_detCoeff_sub_of_hsNorm_sub_tendsto_zero K K₀ hK hK₀ hlim hρ).eventually
      (eventually_lt_nhds hε)
  filter_upwards [hbounded, hdrop] with k hk hsmall z hz
  exact lt_of_le_of_lt (by simpa [dist_comm] using hpt k hk z hz) hsmall

theorem tendstoLocallyUniformly_entireDet2_of_hsNorm_sub_tendsto_zero
    (K : ℕ → ι × ι → ℂ) (K₀ : ι × ι → ℂ)
    (hK : ∀ n, IsHS (K n)) (hK₀ : IsHS K₀)
    (hlim : Tendsto (fun n => hsNorm (K n - K₀)) atTop (nhds 0)) :
    TendstoLocallyUniformly (fun k z => entireDet2 (K k) z) (entireDet2 K₀) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro C hC
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hC.isBounded
  have hρ : (0 : ℝ) < max r 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  exact (tendstoUniformlyOn_entireDet2_of_hsNorm_sub_tendsto_zero
    K K₀ hK hK₀ hlim hρ).mono
      (hr.trans (closedBall_subset_closedBall (le_max_left _ _)))

end GaloisForLFunctions.HTGeometry
