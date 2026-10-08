import GaloisForLFunctions.RHTower.WeilWorkQuantizationCenteredSource
import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianShift

/-!
# Gaussian Fourier contours of the actual centered source

Removing the matching zeta pole makes every exponentially twisted Gaussian
contour residue-free. Uniform radial domination identifies its left edge with
the actual measurable critical trace, rather than an assumed continuous edge.
-/

open Complex Set Filter MeasureTheory Topology
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial GaussZeroSum WeilWorkSettledPhase
variable {lam : ℕ → ℝ}

def quantizationCenteredGaussianIntegrand (hW : WeilPositiveFull lam)
    (T ℓ : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (ℓ * (s - 1 / 2)) * quantizationCenteredProdF hW s * gaussWeight T s

def quantizationCenteredGaussianTrace (hW : WeilPositiveFull lam)
    (T ℓ t : ℝ) : ℂ :=
  Complex.exp (ℓ * ((t : ℂ) * I)) * quantizationCenteredTrace hW t *
    (quantizationGaussianWeight T t : ℂ)

theorem differentiableAt_quantizationCenteredGaussianIntegrand (hW : WeilPositiveFull lam)
    (T ℓ : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (quantizationCenteredGaussianIntegrand hW T ℓ) s := by
  have hA := (differentiableOn_quantizationCenteredProdF hW).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  exact ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ =>
    Complex.exp (ℓ * (z - 1 / 2))) s).mul hA).mul (differentiable_gaussWeight T s)

private theorem norm_centeredGaussian_twist (ℓ : ℝ) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖Complex.exp (ℓ * (s - 1 / 2))‖ ≤ Real.exp |ℓ| := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : ((ℓ : ℂ) * (s - 1 / 2)).re = ℓ * (s.re - 1 / 2) := by simp
  rw [hre]
  have hd : |s.re - 1 / 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    ℓ * (s.re - 1 / 2) ≤ |ℓ * (s.re - 1 / 2)| := le_abs_self _
    _ = |ℓ| * |s.re - 1 / 2| := abs_mul _ _
    _ ≤ |ℓ| := by nlinarith [abs_nonneg ℓ]

private theorem centeredGaussian_decay {T ℓ C : ℝ} {s v : ℂ}
    (hT : 1 ≤ T) (hC : 0 ≤ C) (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2)
    (hv : ‖v‖ ≤ C * (1 + |s.im|)) :
    ‖Complex.exp (ℓ * (s - 1 / 2)) * v * gaussWeight T s‖ ≤
      (Real.exp |ℓ| * C * Real.exp 1 * (Nat.factorial 3 * Real.exp (3 / 2) * T ^ 3)) *
        (1 + s.im ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + s.im ^ 2)]
  rw [norm_mul, norm_mul]
  have hg := norm_gaussWeight_le_of_re hT (s := s)
    (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hp : 1 + s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by
    nlinarith [sq_abs s.im, abs_nonneg s.im]
  have hm := one_add_abs_pow_mul_exp_le 3 hT s.im
  have he : Real.exp (-(s.im ^ 2 / (2 * T ^ 2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  calc
    _ ≤ (Real.exp |ℓ| * (C * (1 + |s.im|))) *
        (Real.exp 1 * Real.exp (-(s.im ^ 2 / T ^ 2))) * (1 + |s.im|) ^ 2 := by
      gcongr
      exact norm_centeredGaussian_twist ℓ hs hs'
    _ = Real.exp |ℓ| * C * Real.exp 1 *
        ((1 + |s.im|) ^ 3 * Real.exp (-(s.im ^ 2 / T ^ 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hm.trans (mul_le_of_le_one_right (by positivity) he)) (by positivity)

theorem exists_quantizationCenteredGaussian_decay (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) (ℓ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 3 / 2 → 2 ≤ |s.im| →
      ‖quantizationCenteredGaussianIntegrand hW T ℓ s‖ ≤ C * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨C, hC, hb⟩ := exists_quantizationCenteredProdF_tail hW
  refine ⟨Real.exp |ℓ| * C * Real.exp 1 *
    (Nat.factorial 3 * Real.exp (3 / 2) * T ^ 3), by positivity, fun s hs hs' ht => ?_⟩
  apply centeredGaussian_decay hT hC hs.le hs'
  simpa only [Complex.re_add_im] using hb s.re s.im hs hs' ht

theorem quantizationCenteredGaussian_open_shift (hW : WeilPositiveFull lam)
    {T η : ℝ} (hT : 1 ≤ T) (hη0 : 0 < η) (hη1 : η < 1 / 4) (ℓ : ℝ) :
    (∫ t : ℝ, quantizationCenteredGaussianIntegrand hW T ℓ (tracePoint η t)) =
      ∫ t : ℝ, quantizationCenteredGaussianIntegrand hW T ℓ ((3 / 2 : ℂ) + t * I) := by
  obtain ⟨C, _, hC⟩ := exists_quantizationCenteredGaussian_decay hW hT ℓ
  have hres : Tendsto (fun s : ℂ => (s - 1) * quantizationCenteredGaussianIntegrand hW T ℓ s)
      (𝓝[≠] 1) (𝓝 0) := by
    have hc := (differentiableAt_quantizationCenteredGaussianIntegrand hW T ℓ
      (s := 1) (by norm_num)).continuousAt
    have hm : ContinuousAt (fun s : ℂ =>
        (s - 1) * quantizationCenteredGaussianIntegrand hW T ℓ s) 1 := by fun_prop
    have hh := hm.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    simpa only [sub_self, zero_mul] using hh
  have hh := GaloisForLFunctions.HTGeometry.integral_line_sub_integral_line_eq
    (F := quantizationCenteredGaussianIntegrand hW T ℓ)
    (a := 1 / 2 + η) (b := 3 / 2) (p := 1)
    (by norm_num; linarith) (by norm_num)
    (fun s hs _ _ => differentiableAt_quantizationCenteredGaussianIntegrand hW T ℓ
      (by linarith)) hres (fun s hs hs' ht => hC s (by linarith) hs' ht)
  rw [mul_zero, sub_eq_zero] at hh
  simpa only [tracePoint, ofReal_add, ofReal_div, ofReal_one, ofReal_ofNat] using hh.symm

theorem exists_quantizationCenteredGaussian_radial_majorant (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) (ℓ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η ∈ Ioo (0 : ℝ) (1 / 4), ∀ t : ℝ,
      ‖quantizationCenteredGaussianIntegrand hW T ℓ (tracePoint η t)‖ ≤
        C * (1 + t ^ 2)⁻¹ := by
  obtain ⟨C, hC, hb⟩ := exists_quantizationCenteredProdF_radial_bound hW
  refine ⟨Real.exp |ℓ| * C * Real.exp 1 *
    (Nat.factorial 3 * Real.exp (3 / 2) * T ^ 3), by positivity, fun η hη t => ?_⟩
  have hr : (tracePoint η t).re = 1 / 2 + η := by simp [tracePoint]
  have hi : (tracePoint η t).im = t := by simp [tracePoint]
  simpa only [quantizationCenteredGaussianIntegrand, hi] using centeredGaussian_decay (ℓ := ℓ) hT hC
    (s := tracePoint η t) (by rw [hr]; linarith [hη.1])
    (by rw [hr]; linarith [hη.2]) (by simpa only [hi] using hb η hη t)

private theorem gaussWeight_critical (T t : ℝ) :
    gaussWeight T (tracePoint 0 t) = (quantizationGaussianWeight T t : ℂ) := by
  unfold gaussWeight quantizationGaussianWeight
  rw [Complex.ofReal_exp]
  congr 1
  unfold tracePoint
  push_cast
  simp only [add_zero, add_sub_cancel_left, mul_pow, Complex.I_sq, mul_neg_one]
  ring

theorem tendsto_quantizationCenteredGaussianTrace (hW : WeilPositiveFull lam)
    (T ℓ t : ℝ) :
    Tendsto (fun η : ℝ => quantizationCenteredGaussianIntegrand hW T ℓ (tracePoint η t))
      (𝓝[>] 0) (𝓝 (quantizationCenteredGaussianTrace hW T ℓ t)) := by
  have hp : Continuous (fun η : ℝ => tracePoint η t) := by unfold tracePoint; fun_prop
  have ht : Tendsto (fun η : ℝ => tracePoint η t) (𝓝[>] 0) (𝓝 (tracePoint 0 t)) :=
    (hp.tendsto 0).mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun η : ℝ => Complex.exp ((ℓ : ℂ) * (tracePoint η t - 1 / 2)))
      (𝓝[>] 0) (𝓝 (Complex.exp ((ℓ : ℂ) * (tracePoint 0 t - 1 / 2)))) :=
    (Complex.continuous_exp.tendsto _).comp
    ((tendsto_const_nhds.mul (ht.sub tendsto_const_nhds)))
  have hg := (differentiable_gaussWeight T (tracePoint 0 t)).continuousAt.tendsto.comp ht
  rw [gaussWeight_critical] at hg
  simpa only [quantizationCenteredGaussianIntegrand, quantizationCenteredGaussianTrace,
    Function.comp_def, tracePoint, add_zero, ofReal_div, ofReal_one, ofReal_ofNat,
    add_sub_cancel_left] using (he.mul (tendsto_quantizationCenteredTrace hW t)).mul hg

theorem tendsto_integral_quantizationCenteredGaussian (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) (ℓ : ℝ) :
    Tendsto (fun η : ℝ => ∫ t : ℝ,
      quantizationCenteredGaussianIntegrand hW T ℓ (tracePoint η t)) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, quantizationCenteredGaussianTrace hW T ℓ t)) := by
  obtain ⟨C, _, hb⟩ := exists_quantizationCenteredGaussian_radial_majorant hW hT ℓ
  have hη := Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => C * (1 + t ^ 2)⁻¹)
  · filter_upwards [hη] with η hη
    have hc : Continuous (fun t : ℝ =>
        quantizationCenteredGaussianIntegrand hW T ℓ (tracePoint η t)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (differentiableAt_quantizationCenteredGaussianIntegrand hW T ℓ
        (by simp [tracePoint]; linarith [hη.1])).continuousAt.comp (by unfold tracePoint; fun_prop)
    exact hc.aestronglyMeasurable
  · filter_upwards [hη] with η hη
    exact Eventually.of_forall (hb η hη)
  · exact _root_.integrable_inv_one_add_sq.const_mul C
  · exact Eventually.of_forall (tendsto_quantizationCenteredGaussianTrace hW T ℓ)

/-- The actual centered Fourier moment is exactly its absolutely convergent right-line contour. -/
theorem quantizationCenteredGaussian_boundary_shift (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) (ℓ : ℝ) :
    (∫ t : ℝ, quantizationCenteredGaussianTrace hW T ℓ t) =
      ∫ t : ℝ, quantizationCenteredGaussianIntegrand hW T ℓ ((3 / 2 : ℂ) + t * I) := by
  apply tendsto_nhds_unique (tendsto_integral_quantizationCenteredGaussian hW hT ℓ)
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with η hη
  exact (quantizationCenteredGaussian_open_shift hW hT hη.1 hη.2 ℓ).symm

end RHTower.WeilSpectral
