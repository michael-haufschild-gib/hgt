import GaloisForLFunctions.RHTower.GaussianFormationUndampedLimit

/-!
# Height-uniform archimedean renormalization

Removing the endpoint factor `exp (-y)` from the Gaussian archimedean current
leaves an error bounded by `y * exp (-y) / re s` throughout the right half-plane.
One incomplete-Mellin recursion turns the full trivial-zero expansion into a
series with a telescoping positive majorant. This normalization is unique among
scalars leaving a bounded error on a positive vertical line.
-/

open Complex Filter Topology MeasureTheory Set RHTower

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Retaining the damping at the lower endpoint sharpens the negative-exponent
Mellin bound uniformly in the imaginary part. -/
theorem norm_gaussianIncompleteMellin_le_endpoint {y : ℝ} (hy : 0 < y)
    {a : ℂ} (ha : a.re < 0) :
    ‖gaussianIncompleteMellin y a‖ ≤ Real.exp (-y) / (-a.re) := by
  rw [gaussianIncompleteMellin, integral_Ici_eq_integral_Ioi]
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : a.re - 1 < -1)
    one_pos).const_mul (Real.exp (-y))
  calc
    ‖∫ u in Ioi (1 : ℝ), (Real.exp (-y * u ^ 2) : ℂ) * (u : ℂ) ^ (a - 1)‖
        ≤ ∫ u in Ioi (1 : ℝ), Real.exp (-y) * u ^ (a.re - 1) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      change 1 < u at hu
      have hu0 : 0 < u := one_pos.trans hu
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      simp only [Complex.sub_re, Complex.one_re]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hu0.le _)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hy.le (show 0 ≤ u ^ 2 - 1 by nlinarith)]
    _ = Real.exp (-y) / (-a.re) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith : a.re - 1 < -1) one_pos]
      simp only [sub_add_cancel, Real.one_rpow, neg_div, div_neg]
      ring

/-- The complete trivial-zero field after endpoint renormalization. -/
theorem hasSum_archimedeanDampingError {y c : ℝ} (hy : 0 < y) (hc : 0 < c)
    {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => (2 * y / (s + 2 * n + 2)) *
      gaussianIncompleteMellin y (-s - 2 * n))
      (gaussianArchimedeanMB y c s -
        (Real.exp (-y) : ℂ) * gaussianArchimedeanCurrent s) := by
  have h := (hasSum_archimedeanMBTerm hy hc (by linarith : 0 < s.re + c)).sub
    ((hasSum_archimedeanSeriesTerm hs).mul_left (Real.exp (-y) : ℂ))
  have heq : ∀ n : ℕ, archimedeanMBTerm y s (n + 1) -
      (Real.exp (-y) : ℂ) * archimedeanSeriesTerm s (n + 1) =
      (2 * y / (s + 2 * n + 2)) * gaussianIncompleteMellin y (-s - 2 * n) := by
    intro n
    have hn : s + 2 * (n : ℂ) + 2 ≠ 0 := by
      have hr : 0 < (s + 2 * (n : ℂ) + 2).re := by simp; positivity
      intro hz
      rw [hz] at hr
      simp at hr
    have ha : -s - 2 * (n : ℂ) - 2 ≠ 0 := by
      rw [show -s - 2 * (n : ℂ) - 2 = -(s + 2 * n + 2) by ring]
      exact neg_ne_zero.mpr hn
    simp only [archimedeanMBTerm, archimedeanSeriesTerm, trivialZeroPoleTerm]
    rw [gaussianIncompleteMellin_recursion hy ha,
      show -s - 2 * (n : ℂ) - 2 + 2 = -s - 2 * n by ring]
    rw [show -s - 2 * (n : ℂ) - 2 = -(s + 2 * n + 2) by ring]
    simp only [div_neg]
    ring
  have ht := (hasSum_nat_add_iff' 1).mpr h
  have hz : archimedeanMBTerm y s 0 -
      (Real.exp (-y) : ℂ) * archimedeanSeriesTerm s 0 = 0 := sub_self _
  rw [Finset.sum_range_one, hz, sub_zero] at ht
  simpa only [heq] using ht

private theorem archimedeanDampingError_term_bound {y : ℝ} (hy : 0 < y)
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖(2 * y / (s + 2 * n + 2)) * gaussianIncompleteMellin y (-s - 2 * n)‖ ≤
      y * Real.exp (-y) * (1 / (s.re + 2 * n) - 1 / (s.re + 2 * n + 2)) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : 0 < s.re + 2 * n := by positivity
  have hre : (-s - 2 * (n : ℂ)).re = -(s.re + 2 * n) := by simp; ring
  have hE := norm_gaussianIncompleteMellin_le_endpoint hy
    (show (-s - 2 * (n : ℂ)).re < 0 by rw [hre]; linarith)
  rw [hre, neg_neg] at hE
  have hden : s.re + 2 * n + 2 ≤ ‖s + 2 * (n : ℂ) + 2‖ := by
    simpa using Complex.re_le_norm (s + 2 * (n : ℂ) + 2)
  rw [norm_mul, norm_div]
  have hnum : ‖(2 : ℂ) * y‖ = 2 * y := by
    simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  rw [hnum]
  calc
    2 * y / ‖s + 2 * (n : ℂ) + 2‖ * ‖gaussianIncompleteMellin y (-s - 2 * n)‖
        ≤ (2 * y / (s.re + 2 * n + 2)) * (Real.exp (-y) / (s.re + 2 * n)) := by
      exact mul_le_mul (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
        hE (norm_nonneg _) (by positivity)
    _ = y * Real.exp (-y) * (1 / (s.re + 2 * n) - 1 / (s.re + 2 * n + 2)) := by
      field_simp
      ring

private theorem sum_reciprocal_step (σ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / (σ + 2 * n) - 1 / (σ + 2 * n + 2)) =
      1 / σ - 1 / (σ + 2 * N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- A height-independent bound for the actual Mellin–Barnes transform, with
the entire infinite trivial-zero field retained. -/
theorem norm_archimedeanDampingError_le {y c : ℝ} (hy : 0 < y) (hc : 0 < c)
    {s : ℂ} (hs : 0 < s.re) :
    ‖gaussianArchimedeanMB y c s -
      (Real.exp (-y) : ℂ) * gaussianArchimedeanCurrent s‖ ≤
      y * Real.exp (-y) / s.re := by
  have ht := (hasSum_archimedeanDampingError hy hc hs).tendsto_sum_nat.norm
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro N
  calc
    ‖∑ n ∈ Finset.range N, (2 * (y : ℂ) / (s + 2 * n + 2)) *
        gaussianIncompleteMellin y (-s - 2 * n)‖
        ≤ ∑ n ∈ Finset.range N,
          ‖(2 * (y : ℂ) / (s + 2 * n + 2)) * gaussianIncompleteMellin y (-s - 2 * n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, y * Real.exp (-y) *
        (1 / (s.re + 2 * n) - 1 / (s.re + 2 * n + 2)) := by
      exact Finset.sum_le_sum fun n _ => archimedeanDampingError_term_bound hy hs n
    _ = y * Real.exp (-y) * (1 / s.re - 1 / (s.re + 2 * N)) := by
      rw [← Finset.mul_sum, sum_reciprocal_step]
    _ ≤ y * Real.exp (-y) / s.re := by
      rw [mul_sub, mul_one_div]
      exact sub_le_self _ (by positivity)

/-- The renormalized error vanishes uniformly on a whole half-plane, so height
may escape without any restriction on its relation to the damping scale. -/
theorem tendstoUniformlyOn_archimedeanDampingError {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
    TendstoUniformlyOn (fun y : ℝ => fun s : ℂ => gaussianArchimedeanMB y c s -
      (Real.exp (-y) : ℂ) * gaussianArchimedeanCurrent s)
      (fun _ => 0) (𝓝[>] 0) {s : ℂ | σ ≤ s.re} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (mul_pos hε hσ)).filter_mono nhdsWithin_le_nhds] with y hy hyε
  change 0 < y at hy
  intro s hs
  rw [dist_zero_left]
  have hs0 : 0 < s.re := hσ.trans_le hs
  have hexp : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith : -y ≤ 0)
  calc
    ‖gaussianArchimedeanMB y c s -
        (Real.exp (-y) : ℂ) * gaussianArchimedeanCurrent s‖
        ≤ y * Real.exp (-y) / s.re := norm_archimedeanDampingError_le hy hc hs0
    _ ≤ y / σ := by
      apply (div_le_div_of_nonneg_left (by positivity) hσ hs).trans
      exact div_le_div_of_nonneg_right (by nlinarith) hσ.le
    _ < ε := (div_lt_iff₀ hσ).mpr hyε

private theorem exists_large_archimedeanCurrent {σ : ℝ} (hσ : 0 < σ) (M : ℝ) :
    ∃ t : ℝ, M ≤ ‖gaussianArchimedeanCurrent ((σ : ℂ) + t * I)‖ := by
  let q : ℝ := 2 * (M + 1 + Real.log Real.pi / 2)
  let t : ℝ := 4 + 2 * Real.exp q
  have ht : 4 ≤ t := by dsimp [t]; linarith [Real.exp_pos q]
  have ht0 : 0 < t := by linarith
  have hs : 0 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have him : |((σ : ℂ) + t * I).im| = t := by simp [abs_of_pos ht0]
  have hA := re_logDeriv_gaussianArchimedeanHalfFactor_ge hs (by rw [him]; exact ht)
  rw [him, logDeriv_gaussianArchimedeanHalfFactor_eq_gammaReal hs] at hA
  have hlog : q ≤ Real.log (t / 2) := by
    rw [← Real.log_exp q]
    exact Real.log_le_log (Real.exp_pos _) (by dsimp [t]; linarith)
  have hfrac : 3 / t ≤ 1 := (div_le_iff₀ ht0).mpr (by linarith)
  refine ⟨t, ?_⟩
  have hM : M ≤ (gaussianArchimedeanCurrent ((σ : ℂ) + t * I)).re := by
    change M ≤ (((σ : ℂ) + t * I)⁻¹ + logDeriv Gammaℝ ((σ : ℂ) + t * I)).re
    dsimp [q] at hlog
    linarith
  exact hM.trans (Complex.re_le_norm _)

/-- Endpoint damping is the unique scalar normalization with bounded vertical
error. Every other scalar leaves the logarithmic archimedean drift. -/
theorem archimedeanDampingError_bounded_iff {y c σ : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hσ : 0 < σ) (z : ℂ) :
    (∃ C : ℝ, ∀ t : ℝ, ‖gaussianArchimedeanMB y c ((σ : ℂ) + t * I) -
      z * gaussianArchimedeanCurrent ((σ : ℂ) + t * I)‖ ≤ C) ↔
      z = (Real.exp (-y) : ℂ) := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hz
    let d : ℂ := (Real.exp (-y) : ℂ) - z
    have hd : 0 < ‖d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))
    let B : ℝ := y * Real.exp (-y) / σ
    obtain ⟨t, ht⟩ := exists_large_archimedeanCurrent hσ ((C + B) / ‖d‖ + 1)
    let s : ℂ := (σ : ℂ) + t * I
    have hs : 0 < s.re := by simpa [s] using hσ
    have hB : ‖gaussianArchimedeanMB y c s -
        (Real.exp (-y) : ℂ) * gaussianArchimedeanCurrent s‖ ≤ B := by
      simpa [s, B] using norm_archimedeanDampingError_le hy hc hs
    have heq : d * gaussianArchimedeanCurrent s =
        (gaussianArchimedeanMB y c s - z * gaussianArchimedeanCurrent s) -
        (gaussianArchimedeanMB y c s -
          (Real.exp (-y) : ℂ) * gaussianArchimedeanCurrent s) := by dsimp [d]; ring
    have hbound : ‖d‖ * ‖gaussianArchimedeanCurrent s‖ ≤ C + B := by
      rw [← norm_mul, heq]
      exact (norm_sub_le _ _).trans (add_le_add (hC t) hB)
    have hmul := mul_le_mul_of_nonneg_left ht hd.le
    have hdiv : ‖d‖ * ((C + B) / ‖d‖ + 1) = C + B + ‖d‖ := by
      field_simp
    change ‖d‖ * ((C + B) / ‖d‖ + 1) ≤ ‖d‖ * ‖gaussianArchimedeanCurrent s‖ at hmul
    rw [hdiv] at hmul
    linarith
  · rintro rfl
    refine ⟨y * Real.exp (-y) / σ, fun t => ?_⟩
    simpa using norm_archimedeanDampingError_le hy hc
      (show 0 < ((σ : ℂ) + t * I).re by simpa using hσ)

#print axioms hasSum_archimedeanDampingError
#print axioms norm_archimedeanDampingError_le
#print axioms tendstoUniformlyOn_archimedeanDampingError
#print axioms archimedeanDampingError_bounded_iff

end GaloisForLFunctions.EulerFETransportTheory
