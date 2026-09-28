import GaloisForLFunctions.RHTower.ProfileRenewalLogKernel
import GaloisForLFunctions.RHTower.ThetaRenewalAnalyticContinuation
import GaloisForLFunctions.HTGeometry.VolterraConvolutionCalculus

/-!
# Real-analytic continuation of a general renewal logarithmic kernel

Let the increment `ν` continue holomorphically to the strip `|Im z| < π/2` as `νC`.  The complex
convolution powers `ν^{⋆(m+1)}(z) = z ∫₀¹ ν(z(1 - u)) ν^{⋆m}(zu) du` are holomorphic there and
obey `|ν^{⋆(m+1)}(z)| ≤ C^{m+1}|z|^m/m!` on the boxes `|Re z| ≤ R`, `|Im z| ≤ π/4`, so the series
`Σ ν^{⋆(m+1)}/((m+1) c^{m+1})` is holomorphic on the open boxes.  On the real axis it is the
oriented kernel `Q`, which is therefore real-analytic on the whole line.  For an even profile
with `P' = aP - ν`, `P(0) = c`, the even reflection profile `e^{-at} + tQ(t)` then forces the
universal even seam jets `Q^{(2j)}(0) = a^{2j+1}/(2j+1)`.
-/
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

noncomputable section

namespace RHTower

variable {ν : ℝ → ℝ} {νC : ℂ → ℂ}

/-- The complex convolution powers of a holomorphic increment. -/
def complexRenewalPower (νC : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => νC
  | m + 1 => complexVolterraConv νC (complexRenewalPower νC m)

theorem differentiableOn_complexRenewalPower (hνC : DifferentiableOn ℂ νC thetaStrip) (m : ℕ) :
    DifferentiableOn ℂ (complexRenewalPower νC m) thetaStrip := by
  induction m with
  | zero => exact hνC
  | succ m ih =>
    exact differentiableOn_complexVolterraConv isOpen_thetaStrip convex_thetaStrip
      zero_mem_thetaStrip hνC ih

theorem complexRenewalPower_ofReal (hre : ∀ x : ℝ, νC x = ν x) (m : ℕ) (t : ℝ) :
    complexRenewalPower νC m t = (renewalPower ν m t : ℂ) := by
  induction m generalizing t with
  | zero => exact hre t
  | succ m ih => exact complexVolterraConv_ofReal hre ih t

/-- `|ν^{⋆(m+1)}(z)| ≤ C^{m+1} |z|^m/m!` on the box, where `|ν| ≤ C`. -/
theorem norm_complexRenewalPower_le {R C : ℝ} (hC : ∀ w ∈ thetaBox R, ‖νC w‖ ≤ C) (m : ℕ) {z : ℂ}
    (hz : z ∈ thetaBox R) : ‖complexRenewalPower νC m z‖ ≤ C ^ (m + 1) * ‖z‖ ^ m / m.factorial := by
  induction m generalizing z with
  | zero => simpa [complexRenewalPower] using hC z hz
  | succ m ih =>
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z hz)
    simp only [complexRenewalPower, complexVolterraConv]
    rw [norm_mul]
    have hbound : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioc (0 : ℝ) 1 →
        ‖νC (z * (1 - u)) * complexRenewalPower νC m (z * u)‖ ≤
          C * (C ^ (m + 1) * ‖z‖ ^ m * u ^ m / m.factorial) := by
      refine Eventually.of_forall fun u hu => ?_
      have h1 : z * (1 - (u : ℂ)) ∈ thetaBox R := by
        have := mul_ofReal_mem_thetaBox hz (s := 1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
        simpa using this
      have h2 := mul_ofReal_mem_thetaBox hz (s := u) ⟨hu.1.le, hu.2⟩
      rw [norm_mul]
      have h3 := ih h2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1, mul_pow] at h3
      exact mul_le_mul (hC _ h1) (h3.trans (le_of_eq (by ring))) (norm_nonneg _) hC0
    have hint := intervalIntegral.norm_integral_le_of_norm_le zero_le_one hbound
      ((by fun_prop : Continuous fun u : ℝ => C * (C ^ (m + 1) * ‖z‖ ^ m * u ^ m /
        m.factorial)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, integral_pow] at hint
    calc ‖z‖ * ‖∫ u in (0 : ℝ)..1, νC (z * (1 - u)) * complexRenewalPower νC m (z * u)‖
        ≤ ‖z‖ * (C * (C ^ (m + 1) * ‖z‖ ^ m * ((1 ^ (m + 1) - 0 ^ (m + 1)) / (m + 1)) /
          m.factorial)) := mul_le_mul_of_nonneg_left hint (norm_nonneg _)
      _ = C ^ (m + 1 + 1) * ‖z‖ ^ (m + 1) / (m + 1).factorial := by
          rw [Nat.factorial_succ]; push_cast; simp; field_simp; ring

/-- The holomorphic logarithmic kernel `Σ ν^{⋆(m+1)}/((m+1) c^{m+1})`. -/
def complexRenewalLogKernel (νC : ℂ → ℂ) (c : ℝ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, complexRenewalPower νC m z / ((m + 1) * (c : ℂ) ^ (m + 1))

theorem complexRenewalLogKernel_ofReal (hre : ∀ x : ℝ, νC x = ν x) (c t : ℝ) :
    complexRenewalLogKernel νC c t = (renewalLogKernel ν c t : ℂ) := by
  rw [complexRenewalLogKernel, renewalLogKernel, Complex.ofReal_tsum]
  refine tsum_congr fun m => ?_
  rw [complexRenewalPower_ofReal hre]; push_cast; ring

theorem differentiableOn_complexRenewalLogKernel (hνC : DifferentiableOn ℂ νC thetaStrip) {c : ℝ}
    (hc : 0 < c) (R : ℝ) : DifferentiableOn ℂ (complexRenewalLogKernel νC c) (thetaOpenBox R) := by
  obtain ⟨C, hC⟩ := (isCompact_thetaBox R).exists_bound_of_continuousOn
    (hνC.continuousOn.mono (thetaBox_subset_thetaStrip R))
  have hsub : thetaOpenBox R ⊆ thetaBox R := fun z hz => ⟨hz.1.le, hz.2.le⟩
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun m : ℕ => C / c * ((C / c * (R + 1)) ^ m / m.factorial))
    ((Real.summable_pow_div_factorial _).mul_left _)
    (fun m => ((differentiableOn_complexRenewalPower hνC m).mono
      ((hsub.trans (thetaBox_subset_thetaStrip R)))).div_const _)
    (isOpen_thetaOpenBox R) fun m z hz => ?_
  have hzb := hsub hz
  have h1 := norm_complexRenewalPower_le hC m hzb
  have h2 := norm_le_of_mem_thetaBox hzb
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
    show ‖((m : ℂ) + 1)‖ = (m : ℝ) + 1 by
      rw [show ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]]
  rw [div_le_iff₀ (by positivity)]
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hz' : ‖z‖ ^ m ≤ (R + 1) ^ m := pow_le_pow_left₀ (norm_nonneg _) h2 m
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z hzb)
  calc ‖complexRenewalPower νC m z‖ ≤ C ^ (m + 1) * ‖z‖ ^ m / m.factorial := h1
    _ ≤ C ^ (m + 1) * (R + 1) ^ m / m.factorial := by gcongr
    _ ≤ C / c * ((C / c * (R + 1)) ^ m / m.factorial) * (((m : ℝ) + 1) * c ^ (m + 1)) := by
        have e : C / c * ((C / c * (R + 1)) ^ m / m.factorial) * (((m : ℝ) + 1) * c ^ (m + 1)) =
            ((m : ℝ) + 1) * (C ^ (m + 1) * (R + 1) ^ m / m.factorial) := by
          rw [mul_pow, div_pow]; field_simp; ring
        rw [e]
        have : 0 ≤ C ^ (m + 1) * (R + 1) ^ m / m.factorial := by
          have hR : 0 ≤ R + 1 := le_trans (norm_nonneg _) h2
          positivity
        nlinarith

/-- **Real-analytic continuation.** If the increment continues holomorphically to the strip
`|Im z| < π/2`, the convolution series `Q`, continued to the whole real axis by oriented
convolutions, is real-analytic at every real point. -/
theorem analyticAt_renewalLogKernel (hνC : DifferentiableOn ℂ νC thetaStrip)
    (hre : ∀ x : ℝ, νC x = ν x) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    AnalyticAt ℝ (renewalLogKernel ν c) t := by
  have hopen : thetaOpenBox (|t| + 1) ∈ 𝓝 (t : ℂ) := by
    refine (isOpen_thetaOpenBox _).mem_nhds ⟨?_, ?_⟩
    · simp only [Complex.ofReal_re]; linarith
    · simp only [Complex.ofReal_im, abs_zero]; positivity
  have hC : AnalyticAt ℂ (complexRenewalLogKernel νC c) (t : ℂ) :=
    (differentiableOn_complexRenewalLogKernel hνC hc _).analyticAt hopen
  have hR : AnalyticAt ℝ (complexRenewalLogKernel νC c) (t : ℂ) := hC.restrictScalars
  have hcomp : AnalyticAt ℝ (fun x : ℝ => (complexRenewalLogKernel νC c (x : ℂ)).re) t :=
    (Complex.reCLM.analyticAt _).comp (hR.comp (Complex.ofRealCLM.analyticAt t))
  refine hcomp.congr (Eventually.of_forall fun x => ?_)
  simp only [complexRenewalLogKernel_ofReal hre, Complex.ofReal_re]

theorem contDiff_renewalLogKernel (hνC : DifferentiableOn ℂ νC thetaStrip)
    (hre : ∀ x : ℝ, νC x = ν x) {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (renewalLogKernel ν c) :=
  AnalyticOnNhd.contDiff fun t _ => analyticAt_renewalLogKernel hνC hre hc t

/-- **Even seam coefficients.** For an even profile `P` with `P' = aP - ν` and `P(0) = c`,
`Q^{(2j)}(0) = a^{2j+1}/(2j+1)`: the reflection profile `e^{-at} + t Q(t)` is even, so its odd
jets vanish. -/
theorem iteratedDeriv_even_renewalLogKernel_zero {P : ℝ → ℝ} {a c : ℝ}
    (hνC : DifferentiableOn ℂ νC thetaStrip) (hre : ∀ x : ℝ, νC x = ν x) (hc : 0 < c)
    (hP : ∀ t, HasDerivAt P (a * P t - ν t) t) (hP0 : P 0 = c) (hPe : ∀ t, P (-t) = P t) (j : ℕ) :
    iteratedDeriv (2 * j) (renewalLogKernel ν c) 0 = a ^ (2 * j + 1) / (2 * j + 1) := by
  have hν : Continuous ν := by
    have h : Continuous fun x : ℝ => (νC (x : ℂ)).re :=
      Complex.continuous_re.comp ((hνC.continuousOn.mono (fun x hx => hx)).comp_continuous
        Complex.continuous_ofReal fun x => by simp [thetaStrip, Real.pi_pos])
    simpa [hre] using h
  have hQ := contDiff_renewalLogKernel hνC hre hc
  have hw : ContDiff ℝ ∞ fun t => t * renewalLogKernel ν c t := contDiff_id.mul hQ
  have hexp : ContDiff ℝ ∞ fun t : ℝ => Real.exp (-a * t) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hy : ContDiff ℝ ∞ (renewalReflectionProfile ν a c) := by
    have : renewalReflectionProfile ν a c = fun t => Real.exp (-a * t) + t * renewalLogKernel ν c t := by
      funext t; simp only [renewalReflectionProfile, neg_mul]
    rw [this]; exact hexp.add hw
  have hodd : iteratedDeriv (2 * j + 1) (renewalReflectionProfile ν a c) 0 = 0 := by
    have h := iteratedDeriv_comp_neg (2 * j + 1) (renewalReflectionProfile ν a c) 0
    rw [show (fun x => renewalReflectionProfile ν a c (-x)) = renewalReflectionProfile ν a c from
      funext (renewalReflectionProfile_neg hν hc hP hP0 hPe), neg_zero, pow_succ, pow_mul] at h
    simp only [neg_one_sq, one_pow, one_mul, neg_smul, one_smul] at h
    linarith
  have hsplit : renewalReflectionProfile ν a c =
      (fun t => Real.exp (-a * t)) + fun t => t * renewalLogKernel ν c t := by
    funext t; simp only [Pi.add_apply, renewalReflectionProfile, neg_mul]
  have hmom := congrFun (iteratedDeriv_id_mul_real hQ (2 * j)) 0
  simp only [zero_mul, zero_add] at hmom
  rw [hsplit, iteratedDeriv_add (hexp.contDiffAt.of_le (natCast_lt_infty _).le)
    (hw.contDiffAt.of_le (natCast_lt_infty _).le), iteratedDeriv_exp_const_mul, hmom] at hodd
  simp only [mul_zero, Real.exp_zero, mul_one] at hodd
  have h2 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff h2]
  push_cast at hodd
  rw [Odd.neg_pow ⟨j, rfl⟩] at hodd
  linarith

end RHTower
