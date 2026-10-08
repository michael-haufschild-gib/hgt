import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCenteredMellin
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCenteredEnergy

/-!
# Residue-free signed contour of the actual centered source

Uniform source bounds justify the radial limit at every height and Gaussian
suppression justifies the contour shift. The resulting kernel sum uses the
literal centered Dirichlet convolution, with no omitted polar correction.
-/

open Complex Set Filter MeasureTheory Topology
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSpectral GaussZeroSum
variable {lam : ℕ → ℝ}

private theorem exists_chi_reflected_strip_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      ‖zetaChi (1 - s)‖ ≤ C * (1 + |s.im|) := by
  let K : Set ℂ := Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-2 : ℝ) 2
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn (fun s : ℂ => zetaChi (1 - s)) K := by
    intro s hs
    have hr := (Complex.mem_reProdIm.mp hs).1.1
    have hg : Gammaℝ (1 - (1 - s)) ≠ 0 := by
      rw [sub_sub_cancel]
      exact Gammaℝ_ne_zero_of_re_pos (by linarith)
    exact ((zetaChi_analyticAt hg).continuousAt.comp
      (continuousAt_const.sub continuousAt_id)).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max (Real.exp 2) (max B 0), by positivity, fun s hs hs' => ?_⟩
  by_cases ht : 2 ≤ |s.im|
  · have hh := norm_zetaChi_le_half_strip (σ := 1 - s.re) (t := -s.im)
      (by linarith) (by linarith) (by simpa using ht)
    have he : ((1 - s.re : ℝ) : ℂ) + ((-s.im : ℝ) : ℂ) * I = 1 - s := by
      push_cast
      linear_combination -s.re_add_im
    rw [he, abs_neg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hm : s ∈ K := Complex.mem_reProdIm.mpr
      ⟨⟨hs, hs'⟩, abs_le.mp (lt_of_not_ge ht).le⟩
    calc
      _ ≤ B := hB s hm
      _ ≤ max (Real.exp 2) (max B 0) := (le_max_left _ _).trans (le_max_right _ _)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg s.im])

def centeredGaussianInterior (hW : WeilPositiveFull lam) (T : ℝ) (s : ℂ) : ℂ :=
  zetaChi (1 - s) * quantizationCenteredProdF hW s ^ 2 * gaussWeight T s

theorem differentiableAt_centeredGaussianInterior (hW : WeilPositiveFull lam)
    (T : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (centeredGaussianInterior hW T) s := by
  have hG : Gammaℝ (1 - (1 - s)) ≠ 0 := by
    rw [sub_sub_cancel]
    exact Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hH := (differentiableOn_quantizationCenteredProdF hW).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  exact (((zetaChi_analyticAt hG).differentiableAt.comp s (by fun_prop)).mul
    (hH.pow 2)).mul (differentiable_gaussWeight T s)

private theorem centered_gaussian_decay {T A B : ℝ} {s v : ℂ}
    (hT : 1 ≤ T) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2)
    (hchi : ‖zetaChi (1 - s)‖ ≤ B * (1 + |s.im|))
    (hv : ‖v‖ ≤ A * (1 + |s.im|)) :
    ‖zetaChi (1 - s) * v ^ 2 * gaussWeight T s‖ ≤
      (B * A ^ 2 * Real.exp 1 * (Nat.factorial 5 * Real.exp (3 / 2) * T ^ 5)) *
        (1 + s.im ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + s.im ^ 2)]
  rw [norm_mul, norm_mul, norm_pow]
  have hg := norm_gaussWeight_le_of_re hT (s := s)
    (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hp : 1 + s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by
    nlinarith [sq_abs s.im, abs_nonneg s.im]
  have hm := one_add_abs_pow_mul_exp_le 5 hT s.im
  have he : Real.exp (-(s.im ^ 2 / (2 * T ^ 2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  calc
    _ ≤ (B * (1 + |s.im|)) * (A * (1 + |s.im|)) ^ 2 *
        (Real.exp 1 * Real.exp (-(s.im ^ 2 / T ^ 2))) * (1 + |s.im|) ^ 2 := by gcongr
    _ = B * A ^ 2 * Real.exp 1 *
        ((1 + |s.im|) ^ 5 * Real.exp (-(s.im ^ 2 / T ^ 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hm.trans (mul_le_of_le_one_right (by positivity) he)) (by positivity)

theorem exists_centeredGaussianInterior_decay (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 3 / 2 → 2 ≤ |s.im| →
      ‖centeredGaussianInterior hW T s‖ ≤ C * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨A, hA, hb⟩ := exists_quantizationCenteredProdF_tail hW
  obtain ⟨B, hB, hc⟩ := exists_chi_reflected_strip_bound
  refine ⟨B * A ^ 2 * Real.exp 1 * (Nat.factorial 5 * Real.exp (3 / 2) * T ^ 5),
    by positivity, fun s hs hs' ht => ?_⟩
  apply centered_gaussian_decay hT hA hB hs.le hs' (hc s hs.le hs')
  simpa only [Complex.re_add_im] using hb s.re s.im hs hs' ht

theorem centeredGaussian_open_shift (hW : WeilPositiveFull lam)
    {T η : ℝ} (hT : 1 ≤ T) (hη0 : 0 < η) (hη1 : η < 1 / 4) :
    (∫ t : ℝ, centeredGaussianInterior hW T (tracePoint η t)) =
      ∫ t : ℝ, centeredGaussianInterior hW T ((3 / 2 : ℂ) + t * I) := by
  obtain ⟨C, _, hC⟩ := exists_centeredGaussianInterior_decay hW hT
  have hres : Tendsto (fun s : ℂ => (s - 1) * centeredGaussianInterior hW T s)
      (𝓝[≠] 1) (𝓝 0) := by
    have hm : ContinuousAt (fun s : ℂ => (s - 1) * centeredGaussianInterior hW T s) 1 :=
      (continuousAt_id.sub continuousAt_const).mul
        (differentiableAt_centeredGaussianInterior hW T (s := 1) (by norm_num)).continuousAt
    have hh := hm.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    simpa using hh
  have hh := GaloisForLFunctions.HTGeometry.integral_line_sub_integral_line_eq
    (F := centeredGaussianInterior hW T) (a := 1 / 2 + η) (b := 3 / 2) (p := 1)
    (by norm_num; linarith) (by norm_num)
    (fun s hs _ _ => differentiableAt_centeredGaussianInterior hW T (by linarith))
    hres (fun s hs hs' ht => hC s (by linarith) hs' ht)
  rw [mul_zero, sub_eq_zero] at hh
  simpa only [tracePoint, ofReal_add, ofReal_div, ofReal_one, ofReal_ofNat] using hh.symm

theorem exists_centeredGaussian_radial_majorant (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η ∈ Ioo (0 : ℝ) (1 / 4), ∀ t : ℝ,
      ‖centeredGaussianInterior hW T (tracePoint η t)‖ ≤ C * (1 + t ^ 2)⁻¹ := by
  obtain ⟨A, hA, hb⟩ := exists_quantizationCenteredProdF_radial_bound hW
  obtain ⟨B, hB, hc⟩ := exists_chi_reflected_strip_bound
  refine ⟨B * A ^ 2 * Real.exp 1 * (Nat.factorial 5 * Real.exp (3 / 2) * T ^ 5),
    by positivity, fun η hη t => ?_⟩
  have hr : (tracePoint η t).re = 1 / 2 + η := by simp [tracePoint]
  have hi : (tracePoint η t).im = t := by simp [tracePoint]
  have hs : 1 / 2 ≤ (tracePoint η t).re := by rw [hr]; linarith [hη.1]
  have hs' : (tracePoint η t).re ≤ 3 / 2 := by rw [hr]; linarith [hη.2]
  simpa only [centeredGaussianInterior, hi] using centered_gaussian_decay hT hA hB hs hs'
    (hc _ hs hs') (by simpa only [hi] using hb η hη t)

private theorem gaussWeight_on_line (T t : ℝ) :
    gaussWeight T (tracePoint 0 t) = (quantizationGaussianWeight T t : ℂ) := by
  unfold gaussWeight quantizationGaussianWeight
  rw [Complex.ofReal_exp]
  congr 1
  unfold tracePoint
  push_cast
  simp only [add_zero, add_sub_cancel_left, mul_pow, Complex.I_sq, mul_neg_one]
  ring

theorem tendsto_centeredGaussianSignedTrace (hW : WeilPositiveFull lam) (T t : ℝ) :
    Tendsto (fun η : ℝ => centeredGaussianInterior hW T (tracePoint η t)) (𝓝[>] 0)
      (𝓝 (centeredGaussianSignedTrace hW T t)) := by
  have hp : Continuous (fun η : ℝ => tracePoint η t) := by unfold tracePoint; fun_prop
  have ht : Tendsto (fun η : ℝ => tracePoint η t) (𝓝[>] 0) (𝓝 (tracePoint 0 t)) :=
    (hp.tendsto 0).mono_left nhdsWithin_le_nhds
  have hG : Gammaℝ (1 - (1 - tracePoint 0 t)) ≠ 0 := by
    rw [sub_sub_cancel]
    exact Gammaℝ_ne_zero_of_re_pos (by norm_num [tracePoint])
  have hc := (zetaChi_analyticAt hG).continuousAt.tendsto.comp (tendsto_const_nhds.sub ht)
  have hg := (differentiable_gaussWeight T (tracePoint 0 t)).continuousAt.tendsto.comp ht
  rw [gaussWeight_on_line] at hg
  exact (hc.mul ((tendsto_quantizationCenteredTrace hW t).pow 2)).mul hg

theorem centeredGaussian_boundary_shift (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, centeredGaussianSignedTrace hW T t) =
      ∫ t : ℝ, centeredGaussianInterior hW T ((3 / 2 : ℂ) + t * I) := by
  have hlim : Tendsto (fun η : ℝ => ∫ t : ℝ, centeredGaussianInterior hW T (tracePoint η t))
      (𝓝[>] 0) (𝓝 (∫ t : ℝ, centeredGaussianSignedTrace hW T t)) := by
    obtain ⟨C, _, hb⟩ := exists_centeredGaussian_radial_majorant hW hT
    have hη := Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)
    apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => C * (1 + t ^ 2)⁻¹)
    · filter_upwards [hη] with η hη
      have hc : Continuous (fun t : ℝ => centeredGaussianInterior hW T (tracePoint η t)) := by
        rw [continuous_iff_continuousAt]
        intro t
        exact (differentiableAt_centeredGaussianInterior hW T
          (by simp [tracePoint]; linarith [hη.1])).continuousAt.comp (by unfold tracePoint; fun_prop)
      exact hc.aestronglyMeasurable
    · filter_upwards [hη] with η hη
      exact Eventually.of_forall (hb η hη)
    · exact _root_.integrable_inv_one_add_sq.const_mul C
    · exact Eventually.of_forall (tendsto_centeredGaussianSignedTrace hW T)
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with η hη
  exact (centeredGaussian_open_shift hW hT hη.1 hη.2).symm

/-- Literal centered arithmetic extraction, with zero polar term. -/
theorem centeredGaussianSignedTrace_eq_kernelSum (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, centeredGaussianSignedTrace hW T t) =
      2 * Real.pi * ∑' n : ℕ, centeredSquareCoeff hW n * leftKernel T n := by
  rw [centeredGaussian_boundary_shift hW hT]
  have hi := integral_zetaChi_mul_LSeries
    (centeredSquareCoeff_summable hW (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num))
    hT (r := 1) (by norm_num)
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul, mul_one] at hi
  rw [← integral_neg_eq_self (fun t : ℝ => centeredGaussianInterior hW T ((3 / 2 : ℂ) + t * I))]
  have hr (t : ℝ) : centeredGaussianInterior hW T ((3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I) =
      zetaChi (leftPt t) * LSeries (centeredSquareCoeff hW) (1 - leftPt t) *
        gaussWeight T (leftPt t) := by
    have hp : (3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - leftPt t := by
      simp only [leftPt, Complex.ofReal_neg]
      ring
    rw [hp, centeredGaussianInterior, sub_sub_cancel,
      ← centeredSquareCoeff_LSeries hW (by simp [leftPt]; norm_num),
      WeilSingularArithmetic.gaussWeight_one_sub]
  simp_rw [hr]
  rw [hi]
  congr 1
  apply tsum_congr
  intro n
  split_ifs with hn
  · simp [hn]
  · rfl

end RHTower.WeilWorkSettledPhase
