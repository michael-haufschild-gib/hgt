import GaloisForLFunctions.HTGeometry.HalfPlaneGapApproximation

/-!
# The truncated Mellin transform is entire

For `0 < a ≤ b < ∞` and `φ` integrable on `(a, b)`, the truncated right Mellin transform

`s ↦ ∫_a^b φ(t) t^{-s} dt`

is an entire function of `s`.  Away from the origin the kernel `t ↦ t^{-s}` and its `s`-derivative
`-log t · t^{-s}` are bounded uniformly on the interval and locally uniformly in `s`, so
differentiation under the integral applies with no decay hypothesis on `φ` whatsoever.

This is the first brick of Burnol's route to the de Branges entirety theorem
(*Two complete and minimal systems associated with the zeros of the Riemann zeta function*,
arXiv:math/0203120, Thm. 2.1): the truncations `∫_a^T f(t)t^{-s}dt` of the Mellin transform of a
Sonine function are entire, and the entirety of the limit comes from locally uniform convergence.

## Main results

* `differentiable_truncatedMellin`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

noncomputable section

/-- The clamp of a real number into `[a, b]`, used to make the Mellin kernel globally bounded. -/
def mellinClamp (a b t : ℝ) : ℝ := max a (min t b)

theorem mellinClamp_pos {a b : ℝ} (ha : 0 < a) (t : ℝ) : 0 < mellinClamp a b t :=
  lt_of_lt_of_le ha (le_max_left _ _)

theorem le_mellinClamp (a b t : ℝ) : a ≤ mellinClamp a b t := le_max_left _ _

theorem mellinClamp_le {a b : ℝ} (hab : a ≤ b) (t : ℝ) : mellinClamp a b t ≤ b :=
  max_le hab (min_le_right _ _)

theorem mellinClamp_eq_self {a b t : ℝ} (ht : t ∈ Ioo a b) : mellinClamp a b t = t := by
  rw [mellinClamp, min_eq_left ht.2.le, max_eq_right ht.1.le]

theorem continuous_mellinClamp (a b : ℝ) : Continuous (mellinClamp a b) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The clamped Mellin kernel, globally bounded on `ℝ`. -/
def mellinClampKernel (a b t : ℝ) (s : ℂ) : ℂ := ((mellinClamp a b t : ℝ) : ℂ) ^ (-s)

/-- The `s`-derivative of the clamped Mellin kernel. -/
def mellinClampKernelDeriv (a b t : ℝ) (s : ℂ) : ℂ :=
  -((Real.log (mellinClamp a b t) : ℝ) : ℂ) * ((mellinClamp a b t : ℝ) : ℂ) ^ (-s)

/-- **The truncated Mellin transform is entire.**  No decay hypothesis on `φ` is needed: the
interval is bounded and bounded away from the origin. -/
theorem differentiable_truncatedMellin {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : IntegrableOn φ (Ioo a b)) :
    Differentiable ℂ fun s : ℂ => ∫ t in Ioo a b, φ t * (t : ℂ) ^ (-s) := by
  classical
  set L : ℝ := max |Real.log a| |Real.log b| with hL
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (le_max_left _ _)
  have hclampLog : ∀ t : ℝ, |Real.log (mellinClamp a b t)| ≤ L := by
    intro t
    have hc0 : 0 < mellinClamp a b t := mellinClamp_pos ha t
    have h1 : Real.log a ≤ Real.log (mellinClamp a b t) :=
      Real.log_le_log ha (le_mellinClamp a b t)
    have h2 : Real.log (mellinClamp a b t) ≤ Real.log b :=
      Real.log_le_log hc0 (mellinClamp_le hab t)
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have hna : -|Real.log a| ≤ Real.log a := neg_abs_le _
      have hle : |Real.log a| ≤ L := le_max_left _ _
      linarith
    · have hnb : Real.log b ≤ |Real.log b| := le_abs_self _
      have hle : |Real.log b| ≤ L := le_max_right _ _
      linarith
  have hcont : ∀ s : ℂ, Continuous fun t : ℝ => mellinClampKernel a b t s := by
    intro s
    refine Continuous.cpow ?_ continuous_const ?_
    · exact Complex.continuous_ofReal.comp (continuous_mellinClamp a b)
    · intro t
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using mellinClamp_pos ha t
  have hcont' : ∀ s : ℂ, Continuous fun t : ℝ => mellinClampKernelDeriv a b t s := by
    intro s
    refine Continuous.mul ?_ (hcont s)
    refine Continuous.neg (Complex.continuous_ofReal.comp ?_)
    exact (continuous_mellinClamp a b).log fun t => (mellinClamp_pos ha t).ne'
  have hderiv : ∀ (t : ℝ) (s : ℂ),
      HasDerivAt (mellinClampKernel a b t) (mellinClampKernelDeriv a b t s) s := by
    intro t s
    have hc0 : 0 < mellinClamp a b t := mellinClamp_pos ha t
    have hne : ((mellinClamp a b t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have h := ((hasDerivAt_id s).neg).const_cpow
      (c := ((mellinClamp a b t : ℝ) : ℂ)) (Or.inl hne)
    rw [← Complex.ofReal_log hc0.le] at h
    refine h.congr_deriv ?_
    simp only [mellinClampKernelDeriv, Pi.neg_apply, id_eq]
    ring
  have hnormK : ∀ (t : ℝ) (s : ℂ),
      ‖mellinClampKernel a b t s‖ = mellinClamp a b t ^ (-s.re) := by
    intro t s
    simp only [mellinClampKernel]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mellinClamp_pos ha t), Complex.neg_re]
  have hbddK : ∀ (R : ℝ), 0 ≤ R → ∀ (t : ℝ) (s : ℂ), |s.re| ≤ R →
      ‖mellinClampKernel a b t s‖ ≤ Real.exp (R * L) := by
    intro R hR t s hs
    rw [hnormK, Real.rpow_def_of_pos (mellinClamp_pos ha t)]
    refine Real.exp_le_exp.2 ?_
    calc Real.log (mellinClamp a b t) * -s.re
        ≤ |Real.log (mellinClamp a b t) * -s.re| := le_abs_self _
      _ = |Real.log (mellinClamp a b t)| * |s.re| := by rw [abs_mul, abs_neg]
      _ ≤ L * R := mul_le_mul (hclampLog t) hs (abs_nonneg _) hL0
      _ = R * L := by ring
  have hfun : (fun s : ℂ => ∫ t in Ioo a b, φ t * (t : ℂ) ^ (-s))
      = fun s : ℂ => ∫ t in Ioo a b, φ t * mellinClampKernel a b t s := by
    funext s
    refine setIntegral_congr_fun measurableSet_Ioo ?_
    intro t ht
    simp only [mellinClampKernel, mellinClamp_eq_self ht]
  rw [hfun]
  refine differentiable_integral_kernel (μ := (volume : Measure ℝ).restrict (Ioo a b))
    (φ := φ) hφ _ _ (fun s => (hcont s).measurable) (fun s => (hcont' s).measurable)
    hderiv ?_
  intro s₀
  refine ⟨max (Real.exp ((‖s₀‖ + 1) * L)) (L * Real.exp ((‖s₀‖ + 1) * L)), ?_⟩
  intro t s hs
  have hR : |s.re| ≤ ‖s₀‖ + 1 := by
    have h1 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
    have hd : ‖s - s₀‖ < 1 := by
      simpa [dist_eq_norm] using Metric.mem_ball.1 hs
    have h3 : ‖s‖ - ‖s₀‖ ≤ ‖s - s₀‖ := norm_sub_norm_le s s₀
    linarith
  have hR0 : (0 : ℝ) ≤ ‖s₀‖ + 1 := by positivity
  have hKb := hbddK (‖s₀‖ + 1) hR0 t s hR
  refine ⟨le_trans hKb (le_max_left _ _), ?_⟩
  simp only [mellinClampKernelDeriv]
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hKb' : ‖((mellinClamp a b t : ℝ) : ℂ) ^ (-s)‖ ≤ Real.exp ((‖s₀‖ + 1) * L) := hKb
  refine le_trans (mul_le_mul (hclampLog t) hKb' (norm_nonneg _) hL0) (le_max_right _ _)

end

end GaloisForLFunctions.HTGeometry
