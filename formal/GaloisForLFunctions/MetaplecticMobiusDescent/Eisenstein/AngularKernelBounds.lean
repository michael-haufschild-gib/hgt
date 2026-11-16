import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularKernelData

/-!
# Rapid decay of angular cubic reflection kernels

Vertical contour shifts give arbitrary polynomial decay for every logarithmic derivative
of the angular reflected kernel. On each bounded logarithmic interval, the bounds are
uniform in the positive radial scale. Angular weight affects constants only.
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped ContDiff ComplexConjugate Classical Topology FourierTransform SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
noncomputable section

def angularInverseMellinIntegrand (k : ℕ) (V : ℝ → ℂ) (j : ℕ) (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ (-s) * angularMellinEulerData k V j s

lemma angularInverseMellinIntegrand_differentiableAt (k : ℕ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (angularInverseMellinIntegrand k V j y) s :=
  (differentiableAt_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    (angularMellinEulerData_differentiableAt k V a b ha hVs hV j s hs)

theorem angularMellinEulerData_vertical_integrable (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
    Integrable (fun t : ℝ => angularMellinEulerData k V j ((σ : ℂ) + t * Complex.I)) := by
  obtain ⟨C, hC, hb⟩ := angularMellinEulerData_strip_bound k V a b ha hsupp hV A j
  have hc : Continuous (fun t : ℝ => angularMellinEulerData k V j ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (angularMellinEulerData_differentiableAt k V a b ha hsupp hV j _ ?_).continuousAt.comp
    · fun_prop
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
      linarith [hσ.1]
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa only [div_eq_mul_inv] using hb σ hσ t)

theorem angularInverseMellinIntegrand_vertical_integrable (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    Integrable (fun t : ℝ => angularInverseMellinIntegrand k V j y ((σ : ℂ) + t * Complex.I)) := by
  apply (angularMellinEulerData_vertical_integrable k V a b ha hsupp hV A j σ hσ).bdd_mul
    (c := y ^ (-σ))
  · exact ((show Continuous (fun t : ℝ => -((σ : ℂ) + t * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp

theorem angularInverseMellinIntegrand_strip_bound (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (y : ℝ) (hy : 0 < y) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖angularInverseMellinIntegrand k V j y ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := angularMellinEulerData_strip_bound k V a b ha hsupp hV A j
  have hc : Continuous (fun σ : ℝ => y ^ (-σ)) :=
    (Real.continuous_const_rpow hy.ne').comp continuous_neg
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))).bddAbove_image hc.continuousOn
  refine ⟨(|B| + 1) * C, by positivity, ?_⟩
  intro σ hσ t
  have hby : y ^ (-σ) ≤ |B| + 1 :=
    (hB (Set.mem_image_of_mem _ hσ)).trans (by linarith [le_abs_self B])
  rw [angularInverseMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ (|B| + 1) * (C / (1 + t ^ 2)) :=
      mul_le_mul hby (hb σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem angularMellinInv_euler_shift (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    mellinInv 0 (angularMellinEulerData k V j) y = mellinInv σ (angularMellinEulerData k V j) y := by
  obtain ⟨C, hC, hb⟩ := angularInverseMellinIntegrand_strip_bound k V a b ha hsupp hV A j y hy
  have h0 : (0 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · norm_num
    · exact Nat.cast_nonneg A
  have hshift (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      (∫ t : ℝ, angularInverseMellinIntegrand k V j y ((-(1 / 4) : ℝ) + t * Complex.I)) =
      ∫ t : ℝ, angularInverseMellinIntegrand k V j y ((ρ : ℂ) + t * Complex.I) := by
    apply VerticalContourShift.integral_eq_of_strip_decay
      (angularInverseMellinIntegrand k V j y) (-(1 / 4)) ρ C hρ.1
    · intro z hzlo hzhi
      apply angularInverseMellinIntegrand_differentiableAt k V a b ha hsupp hV j y hy z
      linarith
    · apply angularInverseMellinIntegrand_vertical_integrable k V a b ha hsupp hV A j
        (-(1 / 4)) ⟨le_rfl, hρ.1.trans hρ.2⟩ y hy
    · exact angularInverseMellinIntegrand_vertical_integrable k V a b ha hsupp hV A j ρ hρ y hy
    · intro r hr t
      exact hb r ⟨hr.1, hr.2.trans hρ.2⟩ t
  have heq := (hshift 0 h0).symm.trans (hshift σ hσ)
  simpa only [mellinInv, smul_eq_mul, angularInverseMellinIntegrand] using
    congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℝ) • z) heq

theorem angularMellinInv_euler_line_bound (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ),
      ∀ y : ℝ, 0 < y → ‖mellinInv σ (angularMellinEulerData k V j) y‖ ≤ C * y ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := angularMellinEulerData_strip_bound k V a b ha hsupp hV A j
  refine ⟨C / 2, by positivity, ?_⟩
  intro σ hσ y hy
  have hint : ‖∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        angularMellinEulerData k V j ((σ : ℂ) + t * Complex.I)‖ ≤ (y ^ (-σ) * C) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, (y ^ (-σ) * C) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        filter_upwards [] with t
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb σ hσ t) (Real.rpow_nonneg hy.le (-σ))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  simp only [smul_eq_mul]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((y ^ (-σ) * C) * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by field_simp

theorem angularPaperKernelLogDerivative_power_bound (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (N j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      ‖angularPaperKernelLogDerivative k V j x‖ ≤ C * x ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := angularMellinInv_euler_line_bound k V a b ha hs hV N j
  refine ⟨C * paperScale ^ (-(N : ℝ)), mul_pos hC (Real.rpow_pos_of_pos paperScale_pos _), ?_⟩
  intro x hx
  have hN : (N : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (N : ℝ) :=
    ⟨by linarith only [Nat.cast_nonneg (α := ℝ) N], le_rfl⟩
  rw [angularPaperKernelLogDerivative, angularMellinInv_euler_shift k V a b ha hs hV N j (N : ℝ) hN
    (paperScale * x) (mul_pos paperScale_pos hx)]
  simpa only [Real.mul_rpow paperScale_pos.le hx.le, mul_assoc] using
    hb (N : ℝ) hN (paperScale * x) (mul_pos paperScale_pos hx)

/-- Polynomially weighted logarithmic derivatives remain bounded on the positive axis. -/
theorem angularPaperKernelLogDerivative_weighted_bound (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (N j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      (1 + x) ^ N * ‖angularPaperKernelLogDerivative k V j x‖ ≤ C := by
  obtain ⟨C₀, hC₀, hb₀⟩ := angularPaperKernelLogDerivative_power_bound k V a b ha hs hV 0 j
  obtain ⟨Cₙ, hCₙ, hbₙ⟩ := angularPaperKernelLogDerivative_power_bound k V a b ha hs hV N j
  refine ⟨2 ^ N * (C₀ + Cₙ), by positivity, ?_⟩
  intro x hx
  have hzero : ‖angularPaperKernelLogDerivative k V j x‖ ≤ C₀ := by
    simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] using hb₀ x hx
  have hhigh : ‖angularPaperKernelLogDerivative k V j x‖ ≤ Cₙ / x ^ N := by
    simpa only [Real.rpow_neg hx.le, Real.rpow_natCast, div_eq_mul_inv] using hbₙ x hx
  by_cases hx1 : x ≤ 1
  · have hp : (1 + x) ^ N ≤ (2 : ℝ) ^ N := by gcongr; linarith
    calc
      _ ≤ 2 ^ N * C₀ := mul_le_mul hp hzero (norm_nonneg _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hp : (1 + x) ^ N ≤ (2 : ℝ) ^ N * x ^ N := by
      rw [← mul_pow]
      gcongr
      linarith
    calc
      _ ≤ (2 ^ N * x ^ N) * (Cₙ / x ^ N) :=
        mul_le_mul hp hhigh (norm_nonneg _) (by positivity)
      _ = 2 ^ N * Cₙ := by field_simp [hx.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- On any fixed logarithmic interval, all kernel derivatives have uniform decay in the radial parameter. -/
theorem angularPaperKernel_exp_local_derivative_bound (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (M : ℝ) (hM : 0 ≤ M) (N j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ u : ℝ, |u| ≤ M →
      (1 + R) ^ N * ‖iteratedDeriv j (fun v : ℝ => angularPaperKernel k V (R * Real.exp v)) u‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := angularPaperKernelLogDerivative_weighted_bound k V a b ha hs hV N j
  refine ⟨Real.exp M ^ N * C, by positivity, ?_⟩
  intro R hR u hu
  have hMu : 0 ≤ M + u := by linarith [(abs_le.mp hu).1]
  have hE : 1 ≤ Real.exp M := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hM
  have hEu : 1 ≤ Real.exp M * Real.exp u := by
    rw [← Real.exp_add]
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hMu
  have hbase : 1 + R ≤ Real.exp M * (1 + R * Real.exp u) := by
    have hRu := mul_le_mul_of_nonneg_left hEu hR.le
    nlinarith only [hE, hRu]
  have hp : (1 + R) ^ N ≤ Real.exp M ^ N * (1 + R * Real.exp u) ^ N := by
    rw [← mul_pow]
    gcongr
  rw [iteratedDeriv_angularPaperKernel_exp k V a b ha hs hV R hR j u]
  calc
    _ ≤ (Real.exp M ^ N * (1 + R * Real.exp u) ^ N) *
        ‖angularPaperKernelLogDerivative k V j (R * Real.exp u)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = Real.exp M ^ N * ((1 + R * Real.exp u) ^ N *
        ‖angularPaperKernelLogDerivative k V j (R * Real.exp u)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb _ (mul_pos hR (Real.exp_pos u))) (by positivity)


/-- The angular reflection kernel decays faster than every prescribed power. -/
theorem angularPaperKernel_power_bound (k : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → ‖angularPaperKernel k V x‖ ≤ C * x ^ (-(N : ℝ)) := by
  simpa only [angularPaperKernelLogDerivative_zero] using
    angularPaperKernelLogDerivative_power_bound k V a b ha hs hV N 0


end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
