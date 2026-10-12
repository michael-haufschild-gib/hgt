import GaloisForLFunctions.HTGeometry.PaperHalfLineCalkin
import GaloisForLFunctions.HTGeometry.LpContinuousMultiplierNorm
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Exact spectrum of continuous multiplication on the half-line

Every value of a continuous symbol is an approximate eigenvalue on restricted Lebesgue L².
Outside the closure of its range, bounded inverse multiplication gives the resolvent.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

private abbrev H := Lp ℂ 2 halfLineMeasure

instance paperHalfLineLp_nontrivial : Nontrivial (Lp ℂ 2 halfLineMeasure) := by
  have hsub : Metric.ball (1 : ℝ) 1 ⊆ Ici (0 : ℝ) := by
    intro x hx
    have h := (abs_lt.mp (show |x - 1| < 1 by simpa [Real.dist_eq] using hx)).1
    change 0 ≤ x
    linarith
  have hvol : halfLineMeasure (Metric.ball (1 : ℝ) 1) = 2 := by
    rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hsub, Real.volume_ball]
    norm_num
  have hfin : halfLineMeasure (Metric.ball (1 : ℝ) 1) ≠ ∞ := by rw [hvol]; norm_num
  let f : H := indicatorConstLp 2 measurableSet_ball hfin (1 : ℂ)
  have hf : 0 < ‖f‖ := by
    dsimp only [f]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul,
      measureReal_def, hvol]
    apply Real.rpow_pos_of_pos
    norm_num
  exact ⟨⟨f, 0, fun h => by simp [h] at hf⟩⟩

private theorem shifted_mul_ae {ψ : ℝ → ℂ} {T : H →L[ℂ] H}
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x) (z : ℂ) (f : H) :
    ((algebraMap ℂ (H →L[ℂ] H) z - T) f : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => (z - ψ x) * f x := by
  change ((z • f - T f : H) : ℝ → ℂ) =ᵐ[halfLineMeasure] _
  filter_upwards [Lp.coeFn_sub (z • f) (T f), Lp.coeFn_smul z f, hT f] with x hsub hsm hTx
  rw [hsub, Pi.sub_apply, hsm, Pi.smul_apply, smul_eq_mul, hTx]
  ring

/-- Every actual continuous symbol value belongs to the continuum operator spectrum. -/
theorem paperHalfLine_value_mem_spectrum {ψ : ℝ → ℂ} {T : H →L[ℂ] H}
    (hψ : Continuous ψ)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ψ x₀ ∈ spectrum ℂ T := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  let M : ℝ := ‖(↑(u⁻¹) : H →L[ℂ] H)‖
  let ε : ℝ := 1 / (2 * (M + 1))
  have hM : 0 ≤ M := norm_nonneg _
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : M * ε < 1 := by
    dsimp [ε]
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    linarith
  have he : ∀ᶠ y in 𝓝 x₀, ‖ψ x₀ - ψ y‖ < ε := by
    have he := ((continuous_const.sub hψ).norm.tendsto x₀).eventually
      (eventually_lt_nhds (show ‖ψ x₀ - ψ x₀‖ < ε by simpa using hε))
    exact he
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.eventually_nhds_iff.mp he
  let r := min r₀ x₀
  have hr : 0 < r := lt_min hr₀ hx₀
  have hball : ∀ y ∈ Metric.ball x₀ r, ‖ψ x₀ - ψ y‖ < ε :=
    fun y hy => hball₀ (lt_of_lt_of_le hy (min_le_left _ _))
  have hsub : Metric.ball x₀ r ⊆ Ici (0 : ℝ) := by
    intro y hy
    have hy' := (abs_lt.mp (show |y - x₀| < r by simpa [Real.dist_eq] using hy)).1
    have hrx : r ≤ x₀ := min_le_right _ _
    change 0 ≤ y
    linarith
  have hvol : halfLineMeasure (Metric.ball x₀ r) = ENNReal.ofReal (2 * r) := by
    rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hsub, Real.volume_ball]
  have hfin : halfLineMeasure (Metric.ball x₀ r) ≠ ∞ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  let f : H := indicatorConstLp 2 measurableSet_ball hfin (1 : ℂ)
  have hfpos : 0 < ‖f‖ := by
    dsimp only [f]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul,
      measureReal_def, hvol, ENNReal.toReal_ofReal (by positivity)]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hlocal : ‖((u : H →L[ℂ] H) f)‖ ≤ ε * ‖f‖ := by
    have hbound : ‖((u : H →L[ℂ] H) f)‖ ≤ ‖(ε : ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      rw [hu]
      filter_upwards [shifted_mul_ae hT (ψ x₀) f, Lp.coeFn_smul (ε : ℂ) f,
        indicatorConstLp_coeFn (p := 2) (hs := measurableSet_ball) (hμs := hfin) (c := (1 : ℂ))]
        with y hAy hsm hfy
      rw [hAy, hsm, Pi.smul_apply, norm_smul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hε]
      by_cases hy : y ∈ Metric.ball x₀ r
      · exact mul_le_mul_of_nonneg_right (hball y hy).le (norm_nonneg _)
      · change f y = _ at hfy
        rw [hfy, indicator_of_notMem hy]
        simp
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] using hbound
  have hnorm : ‖f‖ ≤ M * (ε * ‖f‖) := by
    calc
      ‖f‖ = ‖(↑(u⁻¹) : H →L[ℂ] H) ((u : H →L[ℂ] H) f)‖ := by
        exact (congrArg (fun A : H →L[ℂ] H => ‖A f‖) u.inv_mul).symm
      _ ≤ M * ‖(u : H →L[ℂ] H) f‖ := (↑(u⁻¹) : H →L[ℂ] H).le_opNorm _
      _ ≤ M * (ε * ‖f‖) := mul_le_mul_of_nonneg_left hlocal hM
  nlinarith [mul_lt_mul_of_pos_right hsmall hfpos]

/-- Every boundary value is retained, since the spectrum is closed. -/
theorem paperHalfLine_nonneg_value_mem_spectrum {ψ : ℝ → ℂ} {T : H →L[ℂ] H}
    (hψ : Continuous ψ)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x)
    {x : ℝ} (hx : 0 ≤ x) : ψ x ∈ spectrum ℂ T := by
  have hsub : ψ '' Ioi (0 : ℝ) ⊆ spectrum ℂ T := by
    rintro _ ⟨y, hy, rfl⟩
    exact paperHalfLine_value_mem_spectrum hψ hT hy
  apply closure_minimal hsub (spectrum.isClosed T)
  apply image_closure_subset_closure_image hψ
  exact ⟨x, by simpa only [closure_Ioi, mem_Ici] using hx, rfl⟩

theorem paperHalfLine_norm_symbol_le {ψ : ℝ → ℂ} {T : H →L[ℂ] H}
    (hψ : Continuous ψ)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x)
    {x : ℝ} (hx : 0 ≤ x) : ‖ψ x‖ ≤ ‖T‖ :=
  spectrum.norm_le_norm_of_mem (paperHalfLine_nonneg_value_mem_spectrum hψ hT hx)

/-- The spectrum retains all and only the closure of the full half-line symbol range. -/
theorem paperHalfLine_spectrum {ψ : ℝ → ℂ} {T : H →L[ℂ] H}
    (hψ : Continuous ψ)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ψ x * f x) :
    spectrum ℂ T = closure (ψ '' Ici (0 : ℝ)) := by
  classical
  apply Subset.antisymm
  · intro z hz
    by_contra hc
    obtain ⟨ε, hε, hsep⟩ : ∃ ε > (0 : ℝ), ∀ x ≥ 0, ε ≤ ‖z - ψ x‖ := by
      by_contra! h
      apply hc
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨x, hx, hdist⟩ := h ε hε
      exact ⟨ψ x, ⟨x, hx, rfl⟩, by simpa only [dist_eq_norm] using hdist⟩
    let φ : ℝ → ℂ := fun x => (z - ψ (max 0 x))⁻¹
    have hne : ∀ x, z - ψ (max 0 x) ≠ 0 := fun x =>
      norm_pos_iff.mp (lt_of_lt_of_le hε (hsep _ (le_max_left _ _)))
    have hinv : Continuous φ :=
      (continuous_const.sub (hψ.comp (continuous_const.max continuous_id))).inv₀ hne
    have hbound : ∀ x, ‖φ x‖ ≤ ε⁻¹ := by
      intro x
      dsimp only [φ]
      rw [norm_inv]
      simpa only [one_div] using one_div_le_one_div_of_le hε (hsep _ (le_max_left _ _))
    let S : H →L[ℂ] H := lpBoundedMulCLM hinv.measurable (inv_nonneg.mpr hε.le) hbound
    have hS (f : H) : (S f : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => (z - ψ x)⁻¹ * f x := by
      filter_upwards [lpBoundedMulCLM_coeFn hinv.measurable (inv_nonneg.mpr hε.le) hbound f,
        ae_restrict_mem measurableSet_Ici] with x hSf hx
      have hx0 : (0 : ℝ) ≤ x := hx
      simpa only [φ, max_eq_right hx0] using hSf
    have hright : (algebraMap ℂ (H →L[ℂ] H) z - T) * S = 1 := by
      apply ContinuousLinearMap.ext
      intro f
      apply Lp.ext
      filter_upwards [shifted_mul_ae hT z (S f), hS f,
        ae_restrict_mem measurableSet_Ici] with x hA hSf hx
      change ((algebraMap ℂ (H →L[ℂ] H) z - T) (S f) : ℝ → ℂ) x = f x
      have hx0 : (0 : ℝ) ≤ x := hx
      have hn : z - ψ x ≠ 0 := by simpa only [max_eq_right hx0] using hne x
      rw [hA, hSf, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
    have hleft : S * (algebraMap ℂ (H →L[ℂ] H) z - T) = 1 := by
      apply ContinuousLinearMap.ext
      intro f
      apply Lp.ext
      filter_upwards [hS ((algebraMap ℂ (H →L[ℂ] H) z - T) f), shifted_mul_ae hT z f,
        ae_restrict_mem measurableSet_Ici] with x hSf hA hx
      change (S ((algebraMap ℂ (H →L[ℂ] H) z - T) f) : ℝ → ℂ) x = f x
      have hx0 : (0 : ℝ) ≤ x := hx
      have hn : z - ψ x ≠ 0 := by simpa only [max_eq_right hx0] using hne x
      rw [hSf, hA, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    exact hz (spectrum.mem_resolventSet_of_left_right_inverse hright hleft)
  · apply closure_minimal _ (spectrum.isClosed T)
    rintro _ ⟨x, hx, rfl⟩
    exact paperHalfLine_nonneg_value_mem_spectrum hψ hT hx

end
end GaloisForLFunctions.HTGeometry
