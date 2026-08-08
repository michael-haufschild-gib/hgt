/-
# The entire regularized determinant, as a named function

Every Hilbert–Schmidt kernel has a regularized determinant: an entire function agreeing with the
disc-local exponential representative `fredholmDet` near the origin.  This file constructs it,
`entireDet2 K`, rather than merely asserting its existence, and identifies it as the pointwise
limit of the regularized determinants of the finite blocks.

The construction is the finite-section one.  With `M = ‖K‖_HS + 1` and `r = 1/(2M)`, so `rM = 1/2`:

* every truncation `Kₛ` has `‖Kₛ‖_HS ≤ M`, and `fredholmDet Kₛ` coincides on `ball 0 r` with the
  finite regularized determinant `det₂(1 + z·(−blockMatrix K s))` of its block, whose Taylor
  coefficients obey the Carleman bound `exp(R²‖K‖²_HS/2)/Rⁿ` for **every** `R > 0`;
* the determinants converge uniformly on `closedBall 0 (r/2)` because the exponent is Lipschitz in
  the Hilbert–Schmidt norm, so Cauchy's estimate on the difference makes the Taylor coefficients
  converge;
* the limit coefficients inherit the Carleman bound, hence define an entire function, which agrees
  with `fredholmDet K` on `ball 0 r` because an analytic function is the sum of its Taylor series.

Main results:
* `detRadius`, `detCoeff`, `entireDet2` — the construction.
* `isRegularizedDet_entireDet2`, `exists_isRegularizedDet` — it is the regularized determinant.
* `tendsto_finiteDet2_entireDet2` — it is the pointwise limit of the finite block determinants.
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

/-! ## The canonical radius -/

/-- The radius `1/(2(‖K‖_HS + 1))`, chosen so that `r·(‖K‖_HS + 1) = 1/2`. -/
noncomputable def detRadius (K : ι × ι → ℂ) : ℝ := 1 / (2 * (hsNorm K + 1))

omit [DecidableEq ι] in
theorem detRadius_pos (K : ι × ι → ℂ) : 0 < detRadius K := by
  have := hsNorm_nonneg K
  rw [detRadius]
  positivity

omit [DecidableEq ι] in
theorem detRadius_mul_succ (K : ι × ι → ℂ) : detRadius K * (hsNorm K + 1) = 1 / 2 := by
  have h : hsNorm K + 1 ≠ 0 := by have := hsNorm_nonneg K; positivity
  rw [detRadius]
  field_simp

omit [DecidableEq ι] in
theorem detRadius_mul_le {K : ι × ι → ℂ} {c : ℝ} (hc : c ≤ hsNorm K + 1) :
    detRadius K * c < 1 := by
  have hle : detRadius K * c ≤ detRadius K * (hsNorm K + 1) :=
    mul_le_mul_of_nonneg_left hc (detRadius_pos K).le
  rw [detRadius_mul_succ] at hle
  linarith

omit [DecidableEq ι] in
theorem detRadius_mul_hsNorm_lt (K : ι × ι → ℂ) : detRadius K * hsNorm K < 1 :=
  detRadius_mul_le (by linarith)

theorem detRadius_mul_truncKernel_lt {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι) :
    detRadius K * hsNorm (truncKernel K s) < 1 :=
  detRadius_mul_le (le_trans (hsNorm_truncKernel_le hK s) (by linarith))

omit [DecidableEq ι] in
theorem zero_mem_ball_detRadius (K : ι × ι → ℂ) : (0 : ℂ) ∈ ball (0 : ℂ) (detRadius K) := by
  simpa using detRadius_pos K

/-! ## The coefficients -/

/-- The Taylor coefficients at the origin of the disc-local determinant. -/
noncomputable def detCoeff (K : ι × ι → ℂ) (n : ℕ) : ℂ :=
  taylorCoeff (fun z => fredholmDet K z) n

omit [DecidableEq ι] in
theorem differentiableOn_fredholmDet_ball {K : ι × ι → ℂ} (hK : IsHS K) :
    DifferentiableOn ℂ (fun z => fredholmDet K z) (ball 0 (detRadius K)) :=
  fredholmDet_differentiableOn hK _ (detRadius_mul_hsNorm_lt K)

theorem differentiableOn_fredholmDet_truncKernel_ball {K : ι × ι → ℂ} (hK : IsHS K)
    (s : Finset ι) :
    DifferentiableOn ℂ (fun z => fredholmDet (truncKernel K s) z) (ball 0 (detRadius K)) :=
  fredholmDet_differentiableOn (isHS_truncKernel hK s) _ (detRadius_mul_truncKernel_lt hK s)

/-- On the canonical disc the truncated determinant is the finite determinant of its block, so
their Taylor coefficients agree. -/
theorem detCoeff_truncKernel {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι) (n : ℕ) :
    detCoeff (truncKernel K s) n
      = taylorCoeff (fun z => finiteDet2 (-(blockMatrix K s)) z) n := by
  have hev : (fun z => fredholmDet (truncKernel K s) z)
      =ᶠ[nhds 0] fun z => finiteDet2 (-(blockMatrix K s)) z := by
    filter_upwards [isOpen_ball.mem_nhds (zero_mem_ball_detRadius K)] with z hz
    refine fredholmDet_truncKernel_eq K s ?_
    have hzr : ‖z‖ < detRadius K := by rwa [mem_ball_zero_iff] at hz
    calc ‖z‖ * hsNorm (truncKernel K s)
        ≤ detRadius K * hsNorm (truncKernel K s) :=
          mul_le_mul_of_nonneg_right hzr.le (hsNorm_nonneg _)
      _ < 1 := detRadius_mul_truncKernel_lt hK s
  simp only [detCoeff, taylorCoeff]
  rw [(GaloisForLFunctions.eventuallyEq_iteratedDeriv hev n).eq_of_nhds]

/-- **The Carleman bound for the truncated coefficients**, uniform in the truncation. -/
theorem norm_detCoeff_truncKernel_le {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι) {R : ℝ}
    (hR : 0 < R) (n : ℕ) :
    ‖detCoeff (truncKernel K s) n‖ ≤ Real.exp (R ^ 2 * hsNormSq K / 2) / R ^ n := by
  rw [detCoeff_truncKernel hK s n]
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

/-- **The truncated coefficients converge**, by Cauchy's estimate applied to the difference of the
two determinants on a closed disc. -/
theorem tendsto_detCoeff_truncKernel {K : ι × ι → ℂ} (hK : IsHS K) (n : ℕ) :
    Tendsto (fun s : Finset ι => detCoeff (truncKernel K s) n) atTop (nhds (detCoeff K n)) := by
  set r : ℝ := detRadius K with hrdef
  have hr0 : 0 < r := detRadius_pos K
  set M : ℝ := hsNorm K + 1 with hMdef
  have hM0 : 0 < M := by have := hsNorm_nonneg K; simp only [hMdef]; linarith
  have hKM : hsNorm K ≤ M := by simp [hMdef]
  have hTM : ∀ s : Finset ι, hsNorm (truncKernel K s) ≤ M :=
    fun s => le_trans (hsNorm_truncKernel_le hK s) hKM
  have hrM : r * M = 1 / 2 := detRadius_mul_succ K
  have hrMlt : r * M < 1 := by rw [hrM]; norm_num
  set ρ : ℝ := r / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hρr : ρ < r := by rw [hρdef]; linarith
  set C : ℝ := 2 * Real.exp ((r * M) ^ 2 / (1 - r * M)) with hCdef
  set L : ℝ := r ^ 2 * M / (1 - r * M) with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef, hrM]; positivity
  have hCD : ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f (ball (0 : ℂ) r) → ∀ k : ℕ, ContDiffAt ℂ k f 0 :=
    fun f hf k => ((hf.analyticAt (isOpen_ball.mem_nhds (zero_mem_ball_detRadius K))).contDiffAt)
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hsubeq : ∀ s : Finset ι, detCoeff (truncKernel K s) n - detCoeff K n
      = taylorCoeff ((fun z => fredholmDet (truncKernel K s) z) - fun z => fredholmDet K z) n := by
    intro s
    simp only [detCoeff, taylorCoeff]
    rw [iteratedDeriv_sub (hCD _ (differentiableOn_fredholmDet_truncKernel_ball hK s) n)
      (hCD _ (differentiableOn_fredholmDet_ball hK) n)]
    ring
  have hkey : ∀ s : Finset ι, hsNorm (truncKernel K s - K) * L ≤ 1 →
      ‖detCoeff (truncKernel K s) n - detCoeff K n‖
        ≤ (C * (hsNorm (truncKernel K s - K) * L)) / ρ ^ n := by
    intro s hs
    rw [hsubeq s]
    refine norm_taylorCoeff_le' hρ0 ?_ ?_ n
    · exact diffContOnCl_of_differentiableOn_ball hρ0 hρr
        ((differentiableOn_fredholmDet_truncKernel_ball hK s).sub
          (differentiableOn_fredholmDet_ball hK))
    · intro z hz
      have hzr : ‖z‖ ≤ r := by rw [hz]; rw [hρdef]; linarith
      have := norm_fredholmDet_sub_le (isHS_truncKernel hK s) hK hr0.le (hTM s) hKM hM0.le
        hrMlt hzr (by rw [← hLdef]; exact hs)
      simpa [hCdef, hLdef] using this
  have hnorm0 : Tendsto (fun s : Finset ι => hsNorm (truncKernel K s - K)) atTop (nhds 0) := by
    have hneg : ∀ s : Finset ι, hsNorm (truncKernel K s - K) = hsNorm (K - truncKernel K s) := by
      intro s
      have hE : truncKernel K s - K = -(K - truncKernel K s) := by funext p; simp
      rw [hE, hsNorm_neg]
    exact (tendsto_hsNorm_sub_truncKernel hK).congr fun s => (hneg s).symm
  have hmaj : Tendsto (fun s : Finset ι =>
      (C * (hsNorm (truncKernel K s - K) * L)) / ρ ^ n) atTop (nhds 0) := by
    have h1 : Tendsto (fun s : Finset ι => C * (hsNorm (truncKernel K s - K) * L)) atTop
        (nhds 0) := by
      have := (hnorm0.mul_const L).const_mul C
      simpa using this
    simpa using h1.div_const (ρ ^ n)
  refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hmaj
  have hev : ∀ᶠ s : Finset ι in atTop, hsNorm (truncKernel K s - K) * L ≤ 1 := by
    rcases eq_or_lt_of_le hL0 with hL | hL
    · exact Eventually.of_forall fun s => by rw [← hL]; simp
    · have := hnorm0.eventually (ge_mem_nhds (show (0 : ℝ) < L⁻¹ by positivity))
      filter_upwards [this] with s hs
      rw [← le_div_iff₀ hL]
      simpa [div_eq_mul_inv] using hs
  filter_upwards [hev] with s hs
  exact hkey s hs

/-- **The Carleman bound for the limit coefficients.** -/
theorem norm_detCoeff_le {K : ι × ι → ℂ} (hK : IsHS K) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    ‖detCoeff K n‖ ≤ Real.exp (R ^ 2 * hsNormSq K / 2) / R ^ n :=
  le_of_tendsto ((tendsto_detCoeff_truncKernel hK n).norm)
    (Eventually.of_forall fun s => norm_detCoeff_truncKernel_le hK s hR n)

/-! ## The entire determinant -/

/-- **The entire regularized determinant** `det₂(1 − zK)` of a Hilbert–Schmidt kernel. -/
noncomputable def entireDet2 (K : ι × ι → ℂ) : ℂ → ℂ := entireOfCoeffs (detCoeff K)

theorem differentiable_entireDet2 {K : ι × ι → ℂ} (hK : IsHS K) :
    Differentiable ℂ (entireDet2 K) :=
  differentiable_entireOfCoeffs (c := hsNormSq K) fun _ hR n => norm_detCoeff_le hK hR n

/-- **The construction is the regularized determinant.** -/
theorem isRegularizedDet_entireDet2 {K : ι × ι → ℂ} (hK : IsHS K) :
    IsRegularizedDet K (entireDet2 K) := by
  refine ⟨differentiable_entireDet2 hK, detRadius K, detRadius_pos K,
    detRadius_mul_hsNorm_lt K, fun z hz => ?_⟩
  have hsum : HasSum (fun n => detCoeff K n * z ^ n) (fredholmDet K z) := by
    have h := Complex.hasSum_taylorSeries_on_ball (differentiableOn_fredholmDet_ball hK) hz
    refine h.congr_fun fun n => ?_
    simp only [detCoeff, taylorCoeff, sub_zero, smul_eq_mul]
    ring
  rw [entireDet2, entireOfCoeffs, hsum.tsum_eq]

/-- **Existence of the entire regularized determinant.** -/
theorem exists_isRegularizedDet {K : ι × ι → ℂ} (hK : IsHS K) :
    ∃ D : ℂ → ℂ, IsRegularizedDet K D :=
  ⟨entireDet2 K, isRegularizedDet_entireDet2 hK⟩

/-- **The entire determinant is the pointwise limit of the finite block determinants.** -/
theorem tendsto_finiteDet2_entireDet2 {K : ι × ι → ℂ} (hK : IsHS K) (z : ℂ) :
    Tendsto (fun s : Finset ι => finiteDet2 (-(blockMatrix K s)) z) atTop
      (nhds (entireDet2 K z)) := by
  have hfin : ∀ s : Finset ι, finiteDet2 (-(blockMatrix K s)) z
      = ∑' n : ℕ, detCoeff (truncKernel K s) n * z ^ n := by
    intro s
    have h := hasSum_taylorCoeff (differentiable_finiteDet2 (-(blockMatrix K s))) z
    rw [← h.tsum_eq]
    exact tsum_congr fun n => by rw [detCoeff_truncKernel hK s n]
  rcases eq_or_ne z 0 with rfl | hz
  · have hzero : ∀ s : Finset ι, finiteDet2 (-(blockMatrix K s)) 0 = 1 := by
      intro s; simp [finiteDet2]
    have hlim : entireDet2 K 0 = 1 := by
      have := (isRegularizedDet_entireDet2 hK).eq_one_at_zero
      exact this
    simp only [hzero, hlim]
    exact tendsto_const_nhds
  · have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    set R : ℝ := 2 * ‖z‖ with hRdef
    have hR : 0 < R := by rw [hRdef]; positivity
    set bnd : ℕ → ℝ := fun n => Real.exp (R ^ 2 * hsNormSq K / 2) * (1 / 2) ^ n with hbnd
    have hsumbnd : Summable bnd := by
      rw [hbnd]
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hdom : ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ Real.exp (R ^ 2 * hsNormSq K / 2) / R ^ n) →
        ∀ n, ‖a n * z ^ n‖ ≤ bnd n := by
      intro a ha n
      rw [norm_mul, norm_pow, hbnd]
      have hzn : ‖z‖ ^ n ≠ 0 := by positivity
      have hkey : (Real.exp (R ^ 2 * hsNormSq K / 2) / R ^ n) * ‖z‖ ^ n
          = Real.exp (R ^ 2 * hsNormSq K / 2) * (1 / 2) ^ n := by
        have hRn : R ^ n = 2 ^ n * ‖z‖ ^ n := by rw [hRdef, mul_pow]
        rw [hRn, div_pow, one_pow]
        field_simp
      calc ‖a n‖ * ‖z‖ ^ n
          ≤ (Real.exp (R ^ 2 * hsNormSq K / 2) / R ^ n) * ‖z‖ ^ n :=
            mul_le_mul_of_nonneg_right (ha n) (by positivity)
        _ = Real.exp (R ^ 2 * hsNormSq K / 2) * (1 / 2) ^ n := hkey
    have hconv := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter (Finset ι)))
      (f := fun s n => detCoeff (truncKernel K s) n * z ^ n)
      (g := fun n => detCoeff K n * z ^ n) hsumbnd
      (fun n => ((tendsto_detCoeff_truncKernel hK n).mul_const (z ^ n)))
      (Eventually.of_forall fun s =>
        hdom _ fun n => norm_detCoeff_truncKernel_le hK s hR n)
    have hgoal : (fun s : Finset ι => finiteDet2 (-(blockMatrix K s)) z)
        = fun s : Finset ι => ∑' n : ℕ, detCoeff (truncKernel K s) n * z ^ n := funext hfin
    rw [hgoal, entireDet2, entireOfCoeffs]
    exact hconv

/-! ## Locally uniform convergence -/

/-- The scalar majorant used on a closed disc of radius `ρ`: with `R = 2ρ` the Carleman bound turns
into a geometric series. -/
theorem norm_detCoeff_mul_pow_le {K : ι × ι → ℂ} (hK : IsHS K) {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ‖detCoeff K n‖ * ρ ^ n
      ≤ Real.exp ((2 * ρ) ^ 2 * hsNormSq K / 2) * (1 / 2) ^ n := by
  have hR : (0 : ℝ) < 2 * ρ := by positivity
  have hkey : (Real.exp ((2 * ρ) ^ 2 * hsNormSq K / 2) / (2 * ρ) ^ n) * ρ ^ n
      = Real.exp ((2 * ρ) ^ 2 * hsNormSq K / 2) * (1 / 2) ^ n := by
    have hρn : ρ ^ n ≠ 0 := by positivity
    rw [mul_pow, div_pow, one_pow]
    field_simp
    rw [mul_comm, ← mul_pow]
  calc ‖detCoeff K n‖ * ρ ^ n
      ≤ (Real.exp ((2 * ρ) ^ 2 * hsNormSq K / 2) / (2 * ρ) ^ n) * ρ ^ n :=
        mul_le_mul_of_nonneg_right (norm_detCoeff_le hK hR n) (by positivity)
    _ = _ := hkey

theorem norm_detCoeff_truncKernel_mul_pow_le {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι)
    {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ‖detCoeff (truncKernel K s) n‖ * ρ ^ n
      ≤ Real.exp ((2 * ρ) ^ 2 * hsNormSq K / 2) * (1 / 2) ^ n := by
  have hR : (0 : ℝ) < 2 * ρ := by positivity
  have hkey : (Real.exp ((2 * ρ) ^ 2 * hsNormSq K / 2) / (2 * ρ) ^ n) * ρ ^ n
      = Real.exp ((2 * ρ) ^ 2 * hsNormSq K / 2) * (1 / 2) ^ n := by
    have hρn : ρ ^ n ≠ 0 := by positivity
    rw [mul_pow, div_pow, one_pow]
    field_simp
    rw [mul_comm, ← mul_pow]
  calc ‖detCoeff (truncKernel K s) n‖ * ρ ^ n
      ≤ (Real.exp ((2 * ρ) ^ 2 * hsNormSq K / 2) / (2 * ρ) ^ n) * ρ ^ n :=
        mul_le_mul_of_nonneg_right (norm_detCoeff_truncKernel_le hK s hR n) (by positivity)
    _ = _ := hkey

/-- **The coefficient distance tends to zero**, summed against `ρⁿ`. -/
theorem tendsto_tsum_norm_detCoeff_sub {K : ι × ι → ℂ} (hK : IsHS K) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun s : Finset ι =>
      ∑' n : ℕ, ‖detCoeff (truncKernel K s) n - detCoeff K n‖ * ρ ^ n) atTop (nhds 0) := by
  set E : ℝ := Real.exp ((2 * ρ) ^ 2 * hsNormSq K / 2) with hE
  have hsumbnd : Summable fun n : ℕ => 2 * E * (1 / 2) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hbound : ∀ (s : Finset ι) (n : ℕ),
      ‖‖detCoeff (truncKernel K s) n - detCoeff K n‖ * ρ ^ n‖ ≤ 2 * E * (1 / 2) ^ n := by
    intro s n
    have h1 := norm_detCoeff_truncKernel_mul_pow_le hK s hρ n
    have h2 := norm_detCoeff_mul_pow_le hK hρ n
    have hsplit : ‖detCoeff (truncKernel K s) n - detCoeff K n‖ * ρ ^ n
        ≤ ‖detCoeff (truncKernel K s) n‖ * ρ ^ n + ‖detCoeff K n‖ * ρ ^ n := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hlim : ∀ n : ℕ, Tendsto
      (fun s : Finset ι => ‖detCoeff (truncKernel K s) n - detCoeff K n‖ * ρ ^ n) atTop
      (nhds ((0 : ℝ) * ρ ^ n)) := by
    intro n
    have h0 : Tendsto (fun s : Finset ι => ‖detCoeff (truncKernel K s) n - detCoeff K n‖) atTop
        (nhds 0) := tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_detCoeff_truncKernel hK n)
    exact h0.mul_const (ρ ^ n)
  have := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter (Finset ι)))
    (f := fun (s : Finset ι) (n : ℕ) => ‖detCoeff (truncKernel K s) n - detCoeff K n‖ * ρ ^ n)
    (g := fun _ : ℕ => (0 : ℝ)) hsumbnd (by simpa using hlim)
    (Eventually.of_forall hbound)
  simpa using this

/-- **Locally uniform convergence.**  The finite block determinants converge to the entire
regularized determinant uniformly on every closed disc — the hypothesis every Hurwitz-type argument
about the zeros needs. -/
theorem tendstoUniformlyOn_finiteDet2_entireDet2 {K : ι × ι → ℂ} (hK : IsHS K) {ρ : ℝ}
    (hρ : 0 < ρ) :
    TendstoUniformlyOn (fun (s : Finset ι) (z : ℂ) => finiteDet2 (-(blockMatrix K s)) z)
      (entireDet2 K) atTop (closedBall (0 : ℂ) ρ) := by
  set E : ℝ := Real.exp ((2 * ρ) ^ 2 * hsNormSq K / 2) with hE
  have hsumbnd : Summable fun n : ℕ => 2 * E * (1 / 2) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsum_s : ∀ (s : Finset ι),
      Summable fun n : ℕ => ‖detCoeff (truncKernel K s) n - detCoeff K n‖ * ρ ^ n := by
    intro s
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsumbnd
    have h1 := norm_detCoeff_truncKernel_mul_pow_le hK s hρ n
    have h2 := norm_detCoeff_mul_pow_le hK hρ n
    have hsplit : ‖detCoeff (truncKernel K s) n - detCoeff K n‖ * ρ ^ n
        ≤ ‖detCoeff (truncKernel K s) n‖ * ρ ^ n + ‖detCoeff K n‖ * ρ ^ n := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
    linarith
  have hpt : ∀ (s : Finset ι) (z : ℂ), z ∈ closedBall (0 : ℂ) ρ →
      dist (entireDet2 K z) (finiteDet2 (-(blockMatrix K s)) z)
        ≤ ∑' n : ℕ, ‖detCoeff (truncKernel K s) n - detCoeff K n‖ * ρ ^ n := by
    intro s z hz
    have hzρ : ‖z‖ ≤ ρ := by simpa using mem_closedBall_zero_iff.mp hz
    have hfin : finiteDet2 (-(blockMatrix K s)) z
        = ∑' n : ℕ, detCoeff (truncKernel K s) n * z ^ n := by
      have h := hasSum_taylorCoeff (differentiable_finiteDet2 (-(blockMatrix K s))) z
      rw [← h.tsum_eq]
      exact tsum_congr fun n => by rw [detCoeff_truncKernel hK s n]
    have hsA : Summable fun n : ℕ => detCoeff (truncKernel K s) n * z ^ n :=
      summable_of_orderTwo_bound (c := hsNormSq K)
        (fun R hR n => norm_detCoeff_truncKernel_le hK s hR n) z
    have hsB : Summable fun n : ℕ => detCoeff K n * z ^ n :=
      summable_of_orderTwo_bound (c := hsNormSq K) (fun R hR n => norm_detCoeff_le hK hR n) z
    have hnorms : Summable fun n : ℕ =>
        ‖detCoeff (truncKernel K s) n * z ^ n - detCoeff K n * z ^ n‖ := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hsum_s s)
      rw [← sub_mul, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hzρ n) (norm_nonneg _)
    rw [entireDet2, entireOfCoeffs, hfin, Complex.dist_eq, ← hsB.tsum_sub hsA]
    refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
    · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hsum_s s)
      rw [← sub_mul, norm_mul, norm_pow, norm_sub_rev]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hzρ n) (norm_nonneg _)
    · refine Summable.tsum_le_tsum (fun n => ?_) ?_ (hsum_s s)
      · rw [← sub_mul, norm_mul, norm_pow, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hzρ n) (norm_nonneg _)
      · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hsum_s s)
        rw [← sub_mul, norm_mul, norm_pow, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hzρ n) (norm_nonneg _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hdrop := (tendsto_tsum_norm_detCoeff_sub hK hρ).eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε from hε))
  filter_upwards [hdrop] with s hs z hz
  exact lt_of_le_of_lt (hpt s z hz) hs

end GaloisForLFunctions.HTGeometry
