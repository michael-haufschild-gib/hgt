/-
# The entire regularized determinant exists

Every Hilbert–Schmidt kernel has a regularized determinant: an entire function agreeing with the
disc-local exponential representative `fredholmDet` near the origin.

The construction is the finite-section one.  Fix `M = ‖K‖_HS + 1` and `r = 1/(2M)`, so that
`rM = 1/2`.  On `ball 0 r`:

* every truncation `Kₛ` has `‖Kₛ‖_HS ≤ M`, and `fredholmDet Kₛ` coincides there with the finite
  regularized determinant `det₂(1 + z·(−blockMatrix K s))` of its block, whose Taylor coefficients
  obey the Carleman bound `exp(R²‖K‖²_HS/2)/Rⁿ` for **every** `R > 0`;
* the determinants converge uniformly on `closedBall 0 (r/2)` because the exponent is Lipschitz in
  the Hilbert–Schmidt norm, so Cauchy's estimate on the difference makes the Taylor coefficients
  converge;
* the limit coefficients inherit the Carleman bound, hence define an entire function, which agrees
  with `fredholmDet K` on `ball 0 r` because an analytic function is the sum of its Taylor series.

Main result: `exists_isRegularizedDet`.
-/
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantExists

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Metric Filter

variable {ι : Type*} [DecidableEq ι]

/-- A function differentiable on a ball is `DiffContOnCl` on any strictly smaller ball. -/
theorem diffContOnCl_of_differentiableOn_ball {f : ℂ → ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) r)) : DiffContOnCl ℂ f (ball (0 : ℂ) ρ) := by
  have hsub : closedBall (0 : ℂ) ρ ⊆ ball (0 : ℂ) r := closedBall_subset_ball hρr
  refine ⟨hf.mono (ball_subset_closedBall.trans hsub), ?_⟩
  rw [closure_ball _ hρ.ne']
  exact (hf.mono hsub).continuousOn

/-- **Existence of the entire regularized determinant.**  Every Hilbert–Schmidt kernel has one. -/
theorem exists_isRegularizedDet {K : ι × ι → ℂ} (hK : IsHS K) :
    ∃ D : ℂ → ℂ, IsRegularizedDet K D := by
  classical
  set M : ℝ := hsNorm K + 1 with hMdef
  have hM0 : 0 < M := by have := hsNorm_nonneg K; simp only [hMdef]; linarith
  set r : ℝ := 1 / (2 * M) with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hrM : r * M = 1 / 2 := by rw [hrdef]; field_simp
  have hrMlt : r * M < 1 := by rw [hrM]; norm_num
  have hKM : hsNorm K ≤ M := by simp [hMdef]
  have hTM : ∀ s : Finset ι, hsNorm (truncKernel K s) ≤ M :=
    fun s => le_trans (hsNorm_truncKernel_le hK s) hKM
  have hrK : r * hsNorm K < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hKM hr0.le) hrMlt
  have hrT : ∀ s : Finset ι, r * hsNorm (truncKernel K s) < 1 :=
    fun s => lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hTM s) hr0.le) hrMlt
  have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) r := by simpa using hr0
  -- coefficients
  set a : ℕ → ℂ := fun n => taylorCoeff (fun z => fredholmDet K z) n with hadef
  set as : Finset ι → ℕ → ℂ :=
    fun s n => taylorCoeff (fun z => fredholmDet (truncKernel K s) z) n with hasdef
  -- differentiability on the ball
  have hdK : DifferentiableOn ℂ (fun z => fredholmDet K z) (ball 0 r) :=
    fredholmDet_differentiableOn hK r hrK
  have hdT : ∀ s : Finset ι,
      DifferentiableOn ℂ (fun z => fredholmDet (truncKernel K s) z) (ball 0 r) :=
    fun s => fredholmDet_differentiableOn (isHS_truncKernel hK s) r (hrT s)
  have hCD : ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f (ball (0 : ℂ) r) → ∀ n : ℕ, ContDiffAt ℂ n f 0 :=
    fun f hf n => ((hf.analyticAt (isOpen_ball.mem_nhds h0ball)).contDiffAt)
  -- (1) the truncated determinant has the coefficients of the finite determinant of its block
  have hagree : ∀ (s : Finset ι) (n : ℕ),
      as s n = taylorCoeff (fun z => finiteDet2 (-(blockMatrix K s)) z) n := by
    intro s n
    have hev : (fun z => fredholmDet (truncKernel K s) z)
        =ᶠ[nhds 0] fun z => finiteDet2 (-(blockMatrix K s)) z := by
      filter_upwards [isOpen_ball.mem_nhds h0ball] with z hz
      refine fredholmDet_truncKernel_eq K s ?_
      have hzr : ‖z‖ < r := by rwa [mem_ball_zero_iff] at hz
      calc ‖z‖ * hsNorm (truncKernel K s) ≤ r * M :=
            mul_le_mul hzr.le (hTM s) (hsNorm_nonneg _) hr0.le
        _ < 1 := hrMlt
    simp only [hasdef, taylorCoeff]
    rw [(GaloisForLFunctions.eventuallyEq_iteratedDeriv hev n).eq_of_nhds]
  -- (2) the uniform Carleman bound
  have hbound : ∀ (s : Finset ι) (R : ℝ), 0 < R → ∀ n : ℕ,
      ‖as s n‖ ≤ Real.exp (R ^ 2 * hsNormSq K / 2) / R ^ n := by
    intro s R hR n
    rw [hagree s n]
    refine le_trans (norm_taylorCoeff_finiteDet2_le (-(blockMatrix K s)) hR n) ?_
    have hneg : matHSNormSq (-(blockMatrix K s)) = matHSNormSq (blockMatrix K s) := by
      simp [matHSNormSq]
    have hHS : matHSNormSq (-(blockMatrix K s)) ≤ hsNormSq K := by
      rw [hneg]; exact matHSNormSq_blockMatrix_le hK s
    have hexp : Real.exp (R ^ 2 * matHSNormSq (-(blockMatrix K s)) / 2)
        ≤ Real.exp (R ^ 2 * hsNormSq K / 2) := by
      refine Real.exp_le_exp.mpr ?_
      have hR2 : (0 : ℝ) ≤ R ^ 2 := sq_nonneg R
      nlinarith
    exact div_le_div_of_nonneg_right hexp (by positivity)
  -- (3) the coefficients converge
  set ρ : ℝ := r / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hρr : ρ < r := by rw [hρdef]; linarith
  set C : ℝ := 2 * Real.exp ((r * M) ^ 2 / (1 - r * M)) with hCdef
  set L : ℝ := r ^ 2 * M / (1 - r * M) with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef, hrM]
    positivity
  have hconv : ∀ n : ℕ, Tendsto (fun s : Finset ι => as s n) atTop (nhds (a n)) := by
    intro n
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hsubeq : ∀ s : Finset ι, as s n - a n
        = taylorCoeff ((fun z => fredholmDet (truncKernel K s) z)
            - fun z => fredholmDet K z) n := by
      intro s
      simp only [hasdef, hadef, taylorCoeff]
      rw [iteratedDeriv_sub (hCD _ (hdT s) n) (hCD _ hdK n)]
      ring
    have hkey : ∀ s : Finset ι, hsNorm (truncKernel K s - K) * L ≤ 1 →
        ‖as s n - a n‖ ≤ (C * (hsNorm (truncKernel K s - K) * L)) / ρ ^ n := by
      intro s hs
      rw [hsubeq s]
      refine norm_taylorCoeff_le' hρ0 ?_ ?_ n
      · exact diffContOnCl_of_differentiableOn_ball hρ0 hρr ((hdT s).sub hdK)
      · intro z hz
        have hzr : ‖z‖ ≤ r := by rw [hz]; linarith
        have := norm_fredholmDet_sub_le (isHS_truncKernel hK s) hK hr0.le (hTM s) hKM hM0.le
          hrMlt hzr (by rw [← hLdef]; exact hs)
        simpa [hCdef, hLdef] using this
    have hnorm0 : Tendsto (fun s : Finset ι => hsNorm (truncKernel K s - K)) atTop (nhds 0) := by
      have hneg : ∀ s : Finset ι, hsNorm (truncKernel K s - K) = hsNorm (K - truncKernel K s) := by
        intro s
        have : truncKernel K s - K = -(K - truncKernel K s) := by funext p; simp
        rw [this, hsNorm_neg]
      exact (tendsto_hsNorm_sub_truncKernel hK).congr fun s => (hneg s).symm
    have hmaj : Tendsto (fun s : Finset ι =>
        (C * (hsNorm (truncKernel K s - K) * L)) / ρ ^ n) atTop (nhds 0) := by
      have h1 : Tendsto (fun s : Finset ι => C * (hsNorm (truncKernel K s - K) * L)) atTop
          (nhds 0) := by
        have := (hnorm0.mul_const L).const_mul C
        simpa using this
      simpa using h1.div_const (ρ ^ n)
    refine squeeze_zero' ?_ ?_ hmaj
    · exact Eventually.of_forall fun s => norm_nonneg _
    · have hev : ∀ᶠ s : Finset ι in atTop, hsNorm (truncKernel K s - K) * L ≤ 1 := by
        rcases eq_or_lt_of_le hL0 with hL | hL
        · exact Eventually.of_forall fun s => by rw [← hL]; simp
        · have := hnorm0.eventually (ge_mem_nhds (show (0 : ℝ) < L⁻¹ by positivity))
          filter_upwards [this] with s hs
          rw [← le_div_iff₀ hL]
          simpa [div_eq_mul_inv] using hs
      filter_upwards [hev] with s hs
      exact hkey s hs
  -- (4) the limit coefficients inherit the bound
  have habound : ∀ R : ℝ, 0 < R → ∀ n : ℕ,
      ‖a n‖ ≤ Real.exp (R ^ 2 * hsNormSq K / 2) / R ^ n := by
    intro R hR n
    refine le_of_tendsto ((hconv n).norm) ?_
    exact Eventually.of_forall fun s => hbound s R hR n
  -- (5) the entire function
  refine ⟨entireOfCoeffs a, differentiable_entireOfCoeffs habound, r, hr0, hrK, ?_⟩
  intro z hz
  have hsum : HasSum (fun n => a n * z ^ n) (fredholmDet K z) := by
    have h := Complex.hasSum_taylorSeries_on_ball hdK hz
    refine h.congr_fun fun n => ?_
    simp only [hadef, taylorCoeff, sub_zero, smul_eq_mul]
    ring
  rw [entireOfCoeffs, hsum.tsum_eq]

end GaloisForLFunctions.HTGeometry
