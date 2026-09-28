import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals
import GaloisForLFunctions.HTGeometry.LorentzianCosineIntegral

/-!
# Principal values as boundary values of Stieltjes integrals

For a continuous `g` with `∫₀^∞ |g(t)|/(1+t) dt < ∞`, the Stieltjes integral
`S(ζ) = ∫₀^∞ g(t)/(t - ζ) dt` is defined off `[0, ∞)`.  At `ζ = τ + iη` its real part is the
conjugate-Poisson average `∫₀^∞ g(t) (t - τ)/((t - τ)² + η²) dt`.  The difference from the
principal-value integral truncated at `|t - τ| > η` is `∫₀^∞ g(t) K_η(t - τ) dt` with the odd
defect kernel `K_η(d) = d/(η² + d²) - 1_{|d| > η}/d`, which satisfies

`|K_η(d)| ≤ η/(η² + d²)`,   `|d| |K_η(d)| ≤ η²/(η² + d²)`.

Splitting `g(t) = g(τ) + (g(t) - g(τ))`, oddness of `K_η` on the line and a Lipschitz bound at `τ`
give `|Re S(τ + iη) - PV_η| = O(η)`.  Hence the truncated principal value converges exactly when
the boundary value of `Re S` does, with the same limit.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory Complex Set Filter Topology

/-- The truncation defect kernel `K_η(d) = d/(η² + d²) - 1_{|d| > η} / d`: the difference between
the conjugate Poisson kernel at height `η` and the principal-value kernel truncated at `η`. -/
def truncationDefectKernel (η d : ℝ) : ℝ :=
  d * (η ^ 2 + d ^ 2)⁻¹ - {x : ℝ | η < |x|}.indicator (fun x => x⁻¹) d

theorem measurableSet_lt_abs (η : ℝ) : MeasurableSet {x : ℝ | η < |x|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

theorem measurable_truncationDefectKernel (η : ℝ) : Measurable (truncationDefectKernel η) :=
  (by fun_prop : Measurable fun d : ℝ => d * (η ^ 2 + d ^ 2)⁻¹).sub
    (measurable_inv.indicator (measurableSet_lt_abs η))

theorem truncationDefectKernel_neg (η d : ℝ) :
    truncationDefectKernel η (-d) = -truncationDefectKernel η d := by
  unfold truncationDefectKernel
  by_cases h : η < |d|
  · rw [indicator_of_mem (show -d ∈ {x : ℝ | η < |x|} by simpa using h),
      indicator_of_mem (show d ∈ {x : ℝ | η < |x|} from h)]
    rw [neg_sq, inv_neg]; ring
  · rw [indicator_of_notMem (show -d ∉ {x : ℝ | η < |x|} by simpa using h),
      indicator_of_notMem (show d ∉ {x : ℝ | η < |x|} from h)]
    rw [neg_sq]; ring

theorem truncationDefectKernel_of_lt {η d : ℝ} (hη : 0 < η) (h : η < |d|) :
    truncationDefectKernel η d = -(η ^ 2 * (d * (η ^ 2 + d ^ 2))⁻¹) := by
  have hd : d ≠ 0 := fun h0 => by rw [h0, abs_zero] at h; linarith
  have hp : η ^ 2 + d ^ 2 ≠ 0 := by positivity
  unfold truncationDefectKernel
  rw [indicator_of_mem (show d ∈ {x : ℝ | η < |x|} from h)]
  field_simp
  ring

theorem truncationDefectKernel_of_le {η d : ℝ} (h : |d| ≤ η) :
    truncationDefectKernel η d = d * (η ^ 2 + d ^ 2)⁻¹ := by
  unfold truncationDefectKernel
  rw [indicator_of_notMem (show d ∉ {x : ℝ | η < |x|} by simpa using h), sub_zero]

theorem abs_truncationDefectKernel_le {η : ℝ} (hη : 0 < η) (d : ℝ) :
    |truncationDefectKernel η d| ≤ η * (η ^ 2 + d ^ 2)⁻¹ := by
  have hp : 0 < η ^ 2 + d ^ 2 := by positivity
  rcases lt_or_ge η |d| with h | h
  · have hd : 0 < |d| := hη.trans h
    rw [truncationDefectKernel_of_lt hη h, abs_neg, abs_mul, abs_inv, abs_mul,
      abs_of_pos hp, abs_of_pos (by positivity : 0 < η ^ 2), ← div_eq_mul_inv,
      ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hp]
    have : η ^ 2 ≤ η * |d| := by nlinarith
    nlinarith
  · rw [truncationDefectKernel_of_le h, abs_mul, abs_inv, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hp.le)

theorem abs_mul_truncationDefectKernel_le {η : ℝ} (hη : 0 < η) (d : ℝ) :
    |d| * |truncationDefectKernel η d| ≤ η ^ 2 * (η ^ 2 + d ^ 2)⁻¹ := by
  have hp : 0 < η ^ 2 + d ^ 2 := by positivity
  rcases lt_or_ge η |d| with h | h
  · have hd : 0 < |d| := hη.trans h
    rw [truncationDefectKernel_of_lt hη h, abs_neg, abs_mul, abs_inv, abs_mul,
      abs_of_pos hp, abs_of_pos (by positivity : 0 < η ^ 2), mul_inv]
    field_simp
    rfl
  · rw [truncationDefectKernel_of_le h, abs_mul, abs_inv, abs_of_pos hp, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hp.le)
    calc |d| * |d| ≤ η * η := mul_le_mul h h (abs_nonneg _) hη.le
      _ = η ^ 2 := by ring

theorem abs_truncationDefectKernel_le_of_le {η τ d : ℝ} (hη : 0 < η) (hητ : η < τ)
    (hd : τ ≤ |d|) : |truncationDefectKernel η d| ≤ η ^ 2 / τ * (η ^ 2 + d ^ 2)⁻¹ := by
  have hp : 0 < η ^ 2 + d ^ 2 := by positivity
  have hτ : 0 < τ := hη.trans hητ
  have hd0 : 0 < |d| := hτ.trans_le hd
  rw [truncationDefectKernel_of_lt hη (hητ.trans_le hd), abs_neg, abs_mul, abs_inv, abs_mul,
    abs_of_pos hp, abs_of_pos (by positivity : 0 < η ^ 2), ← div_eq_mul_inv,
    ← div_eq_mul_inv, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : η ^ 2 * τ ≤ η ^ 2 * |d| := by gcongr
  nlinarith

theorem integrable_poissonShift {η : ℝ} (hη : 0 < η) (τ : ℝ) :
    Integrable fun t : ℝ => (η ^ 2 + (t - τ) ^ 2)⁻¹ := by
  have h := (integrable_inv_sq_add_sq hη).comp_sub_right τ
  simpa using h

theorem integral_poissonShift {η : ℝ} (hη : 0 < η) (τ : ℝ) :
    ∫ t : ℝ, (η ^ 2 + (t - τ) ^ 2)⁻¹ = Real.pi / η := by
  rw [integral_sub_right_eq_self (fun t : ℝ => (η ^ 2 + t ^ 2)⁻¹) τ]
  simpa using integral_inv_sq_add_sq hη

theorem integrable_truncationDefectKernel_shift {η : ℝ} (hη : 0 < η) (τ : ℝ) :
    Integrable fun t : ℝ => truncationDefectKernel η (t - τ) :=
  ((integrable_poissonShift hη τ).const_mul η).mono'
    ((measurable_truncationDefectKernel η).comp (measurable_id.sub_const τ)).aestronglyMeasurable
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact abs_truncationDefectKernel_le hη _)

theorem integral_truncationDefectKernel_shift (η τ : ℝ) :
    ∫ t : ℝ, truncationDefectKernel η (t - τ) = 0 := by
  rw [integral_sub_right_eq_self (truncationDefectKernel η) τ]
  have h := integral_neg_eq_self (truncationDefectKernel η) volume
  simp_rw [truncationDefectKernel_neg, integral_neg] at h
  linarith

/-- A function with `∫₀^∞ |g(t)| / (1 + t) dt < ∞` has an integrable Stieltjes integrand off the
closed positive half-line. -/
theorem integrableOn_div_sub_of_integrableOn_div_one_add {g : ℝ → ℝ} (hg : Continuous g)
    (hgi : IntegrableOn (fun t => g t / (1 + t)) (Ioi 0)) {ζ : ℂ} (hζ : -ζ ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (g t : ℂ) / ((t : ℂ) - ζ)) (Ioi 0) := by
  obtain ⟨c, hc, hcle⟩ := exists_mul_one_add_le_norm_sub hζ
  have hne : ∀ t : ℝ, 0 ≤ t → (t : ℂ) - ζ ≠ 0 := fun t ht h0 => by
    have := hcle t ht
    rw [h0, norm_zero] at this
    nlinarith
  refine (hgi.norm.const_mul c⁻¹).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (by fun_prop : Continuous fun t : ℝ => (g t : ℂ)).continuousOn.div
      (by fun_prop) fun t ht => hne t (le_of_lt ht)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 ≤ t := le_of_lt ht
    have hpos : 0 < c * (1 + t) := by positivity
    rw [norm_div, Complex.norm_real, div_le_iff₀ (lt_of_lt_of_le hpos (hcle t ht0)),
      norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ 1 + t)]
    calc ‖g t‖ = c⁻¹ * (‖g t‖ / (1 + t)) * (c * (1 + t)) := by field_simp
      _ ≤ c⁻¹ * (‖g t‖ / (1 + t)) * ‖(t : ℂ) - ζ‖ := by gcongr; exact hcle t ht0

theorem re_div_sub_upper (a t τ η : ℝ) :
    ((a : ℂ) / ((t : ℂ) - (τ + η * I))).re = a * ((t - τ) * (η ^ 2 + (t - τ) ^ 2)⁻¹) := by
  rw [Complex.div_re]
  simp only [ofReal_re, ofReal_im, sub_re, add_re, mul_re, I_re, I_im, sub_im, add_im, mul_im,
    zero_mul, mul_zero, sub_zero, add_zero, mul_one, zero_add, normSq_apply]
  ring

/-- **Poisson versus truncation.** Let `g` be continuous with `∫₀^∞ |g(t)|/(1+t) dt < ∞` and
`|g(t) - g(τ)| ≤ L |t - τ|` for `t > 0`, `τ > 0`. Then the real part of the Stieltjes integral at
`τ + iη` and the truncated principal-value integral differ by `O(η)`:
`Re ∫₀^∞ g(t)/(t - τ - iη) dt - ∫_{t>0, |t-τ|>η} g(t)/(t - τ) dt → 0` as `η → 0⁺`. -/
theorem tendsto_re_stieltjes_sub_truncated {g : ℝ → ℝ} (hg : Continuous g)
    (hgi : IntegrableOn (fun t => g t / (1 + t)) (Ioi 0)) {τ L : ℝ} (hτ : 0 < τ)
    (hL : ∀ t, 0 < t → |g t - g τ| ≤ L * |t - τ|) :
    Tendsto (fun η : ℝ => (∫ t in Ioi (0 : ℝ), (g t : ℂ) / ((t : ℂ) - (τ + η * I))).re -
      ∫ t in Ioi (0 : ℝ) \ Icc (τ - η) (τ + η), g t / (t - τ)) (𝓝[>] 0) (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun η => (|g τ| * Real.pi / τ + L * Real.pi) * η) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT hτ] with η hη
    obtain ⟨hη0, hητ⟩ := hη
    set P : ℝ → ℝ := fun t => (η ^ 2 + (t - τ) ^ 2)⁻¹ with hPdef
    set K : ℝ → ℝ := fun t => truncationDefectKernel η (t - τ) with hKdef
    have hsl : -((τ : ℂ) + η * I) ∈ slitPlane := Or.inr (by simp; exact hη0.ne')
    have hS := integrableOn_div_sub_of_integrableOn_div_one_add hg hgi hsl
    have hre := integral_re hS
    simp only [RCLike.re_to_complex, re_div_sub_upper] at hre
    have hPint : IntegrableOn (fun t => g t * ((t - τ) * P t)) (Ioi 0) := by
      refine IntegrableOn.congr_fun hS.re (fun t _ => ?_) measurableSet_Ioi
      simp only [RCLike.re_to_complex, re_div_sub_upper, P]
    have hKint : Integrable K := integrable_truncationDefectKernel_shift hη0 τ
    have hK1 : IntegrableOn (fun t => g τ * K t) (Ioi 0) := (hKint.const_mul _).integrableOn
    have hKmeas : Measurable K :=
      (measurable_truncationDefectKernel η).comp (measurable_id.sub_const τ)
    have hL0 : 0 ≤ L := by
      have := hL (τ + 1) (by linarith)
      simp only [add_sub_cancel_left, abs_one, mul_one] at this
      exact (abs_nonneg _).trans this
    have hK2 : IntegrableOn (fun t => (g t - g τ) * K t) (Ioi 0) := by
      refine (((integrable_poissonShift hη0 τ).const_mul (L * η ^ 2)).integrableOn).mono'
        ((hg.measurable.sub_const _).mul hKmeas).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_mul_truncationDefectKernel_le hη0 (t - τ)
      have h2 := hL t ht
      calc |g t - g τ| * |K t| ≤ L * |t - τ| * |K t| := by gcongr
        _ = L * (|t - τ| * |truncationDefectKernel η (t - τ)|) := by simp only [K]; ring
        _ ≤ L * (η ^ 2 * (η ^ 2 + (t - τ) ^ 2)⁻¹) := by gcongr
        _ = L * η ^ 2 * (η ^ 2 + (t - τ) ^ 2)⁻¹ := by ring
    have hT : ∫ t in Ioi (0 : ℝ) \ Icc (τ - η) (τ + η), g t / (t - τ) =
        ∫ t in Ioi (0 : ℝ), (g t * ((t - τ) * P t) - (g τ * K t + (g t - g τ) * K t)) := by
      rw [sdiff_eq, ← setIntegral_indicator measurableSet_Icc.compl]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [K, P, truncationDefectKernel]
      have hmem : t ∈ (Icc (τ - η) (τ + η))ᶜ ↔ t - τ ∈ {x : ℝ | η < |x|} := by
        simp only [mem_compl_iff, mem_Icc, mem_setOf_eq, not_and_or, not_le]
        constructor
        · rintro (h | h)
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        · intro h
          rcases le_or_gt 0 (t - τ) with h' | h'
          · rw [abs_of_nonneg h'] at h; right; linarith
          · rw [abs_of_neg h'] at h; left; linarith
      by_cases h : t - τ ∈ {x : ℝ | η < |x|}
      · rw [indicator_of_mem (hmem.mpr h), indicator_of_mem h]
        ring
      · rw [indicator_of_notMem (fun h' => h (hmem.mp h')), indicator_of_notMem h]
        ring
    have hsum : IntegrableOn (fun t => g τ * K t + (g t - g τ) * K t) (Ioi 0) := hK1.add hK2
    rw [hT, integral_sub hPint hsum, integral_add hK1 hK2, ← hre]
    simp only [P]
    rw [show ∀ a b c : ℝ, a - (a - (b + c)) = b + c from fun a b c => by ring]
    rw [Real.norm_eq_abs]
    have hbound1 : |∫ t in Ioi (0 : ℝ), g τ * K t| ≤ |g τ| * Real.pi / τ * η := by
      rw [integral_const_mul, abs_mul]
      have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := 0) hKint.integrableOn
        hKint.integrableOn
      rw [integral_truncationDefectKernel_shift] at hsplit
      have hIoi : ∫ t in Ioi (0 : ℝ), K t = -∫ t in Iic (0 : ℝ), K t := by linarith
      rw [hIoi, abs_neg]
      have hIic : |∫ t in Iic (0 : ℝ), K t| ≤ η ^ 2 / τ * (Real.pi / η) := by
        rw [← integral_poissonShift hη0 τ, ← integral_const_mul]
        refine (abs_integral_le_integral_abs).trans ?_
        refine (setIntegral_mono_on hKint.integrableOn.abs
          ((integrable_poissonShift hη0 τ).const_mul _).integrableOn measurableSet_Iic
          fun t ht => ?_).trans (setIntegral_le_integral
            ((integrable_poissonShift hη0 τ).const_mul _)
            (Eventually.of_forall fun t => by positivity))
        refine abs_truncationDefectKernel_le_of_le hη0 hητ ?_
        rw [abs_of_nonpos (by linarith [mem_Iic.mp ht])]
        linarith [mem_Iic.mp ht]
      calc |g τ| * |∫ t in Iic (0 : ℝ), K t| ≤ |g τ| * (η ^ 2 / τ * (Real.pi / η)) := by gcongr
        _ = |g τ| * Real.pi / τ * η := by field_simp
    have hbound2 : |∫ t in Ioi (0 : ℝ), (g t - g τ) * K t| ≤ L * Real.pi * η := by
      calc |∫ t in Ioi (0 : ℝ), (g t - g τ) * K t|
          ≤ ∫ t in Ioi (0 : ℝ), |(g t - g τ) * K t| := abs_integral_le_integral_abs
        _ ≤ ∫ t in Ioi (0 : ℝ), L * η ^ 2 * (η ^ 2 + (t - τ) ^ 2)⁻¹ := by
            refine setIntegral_mono_on hK2.abs
              ((integrable_poissonShift hη0 τ).const_mul _).integrableOn measurableSet_Ioi
              fun t ht => ?_
            rw [abs_mul]
            have h1 := abs_mul_truncationDefectKernel_le hη0 (t - τ)
            calc |g t - g τ| * |K t| ≤ L * |t - τ| * |K t| := by gcongr; exact hL t ht
              _ = L * (|t - τ| * |truncationDefectKernel η (t - τ)|) := by simp only [K]; ring
              _ ≤ L * (η ^ 2 * (η ^ 2 + (t - τ) ^ 2)⁻¹) := by gcongr
              _ = L * η ^ 2 * (η ^ 2 + (t - τ) ^ 2)⁻¹ := by ring
        _ ≤ ∫ t : ℝ, L * η ^ 2 * (η ^ 2 + (t - τ) ^ 2)⁻¹ :=
            setIntegral_le_integral ((integrable_poissonShift hη0 τ).const_mul _)
              (Eventually.of_forall fun t => by positivity)
        _ = L * Real.pi * η := by
            rw [integral_const_mul, integral_poissonShift hη0 τ]; field_simp
    calc |(∫ t in Ioi (0 : ℝ), g τ * K t) + ∫ t in Ioi (0 : ℝ), (g t - g τ) * K t|
        ≤ |∫ t in Ioi (0 : ℝ), g τ * K t| + |∫ t in Ioi (0 : ℝ), (g t - g τ) * K t| :=
          abs_add_le _ _
      _ ≤ |g τ| * Real.pi / τ * η + L * Real.pi * η := add_le_add hbound1 hbound2
      _ = (|g τ| * Real.pi / τ + L * Real.pi) * η := by ring
  · have h : Tendsto (fun η : ℝ => (|g τ| * Real.pi / τ + L * Real.pi) * η) (𝓝 0) (𝓝 0) := by
      have := (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (|g τ| * Real.pi / τ + L * Real.pi)
      simpa using this
    exact h.mono_left nhdsWithin_le_nhds

end

end GaloisForLFunctions.HTGeometry
