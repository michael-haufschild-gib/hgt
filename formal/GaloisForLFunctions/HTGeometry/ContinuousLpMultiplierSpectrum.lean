import GaloisForLFunctions.HTGeometry.LpContinuousMultiplierNorm
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Spectrum of continuous multiplication on the real-height continuum

Every value of a continuous symbol is an approximate eigenvalue on Lebesgue L².
Outside the closure of its range, bounded inverse multiplication gives the resolvent.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

private abbrev H := Lp ℂ 2 (volume : Measure ℝ)

private theorem shifted_mul_ae {ψ : ℝ → ℂ} {T : H →L[ℂ] H}
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun x => ψ x * f x) (z : ℂ) (f : H) :
    ((algebraMap ℂ (H →L[ℂ] H) z - T) f : ℝ → ℂ) =ᵐ[volume]
      fun x => (z - ψ x) * f x := by
  change ((z • f - T f : H) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (z • f) (T f), Lp.coeFn_smul z f, hT f] with x hsub hsm hTx
  rw [hsub, Pi.sub_apply, hsm, Pi.smul_apply, smul_eq_mul, hTx]
  ring

/-- Every actual continuous symbol value belongs to the continuum operator spectrum. -/
theorem value_mem_spectrum_of_ae_mul_continuous {ψ : ℝ → ℂ} {T : H →L[ℂ] H}
    (hψ : Continuous ψ)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun x => ψ x * f x) (x₀ : ℝ) :
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
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  have hfin : volume (Metric.ball x₀ r) ≠ ∞ := by
    rw [Real.volume_ball]
    exact ENNReal.ofReal_ne_top
  let f : H := indicatorConstLp 2 measurableSet_ball hfin (1 : ℂ)
  have hfpos : 0 < ‖f‖ := by
    dsimp only [f]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul,
      measureReal_def, Real.volume_ball, ENNReal.toReal_ofReal (by positivity)]
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
      · exact mul_le_mul_of_nonneg_right (hball hy).le (norm_nonneg _)
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

/-- The full spectrum is the closure of the literal continuous symbol range. -/
theorem spectrum_eq_closure_range_of_ae_mul_continuous {ψ : ℝ → ℂ} {T : H →L[ℂ] H}
    (hψ : Continuous ψ)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun x => ψ x * f x) :
    spectrum ℂ T = closure (range ψ) := by
  classical
  apply Subset.antisymm
  · intro z hz
    by_contra hc
    obtain ⟨ε, hε, hsep⟩ : ∃ ε > (0 : ℝ), ∀ x, ε ≤ ‖z - ψ x‖ := by
      by_contra! h
      apply hc
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨x, hx⟩ := h ε hε
      exact ⟨ψ x, mem_range_self x, by simpa only [dist_eq_norm] using hx⟩
    have hne : ∀ x, z - ψ x ≠ 0 := fun x =>
      norm_pos_iff.mp (lt_of_lt_of_le hε (hsep x))
    have hinv : Continuous fun x => (z - ψ x)⁻¹ := (continuous_const.sub hψ).inv₀ hne
    have hbound : ∀ x, ‖(z - ψ x)⁻¹‖ ≤ ε⁻¹ := by
      intro x
      rw [norm_inv]
      simpa only [one_div] using one_div_le_one_div_of_le hε (hsep x)
    let S : H →L[ℂ] H := lpBoundedMulCLM hinv.measurable (inv_nonneg.mpr hε.le) hbound
    have hS (f : H) : (S f : ℝ → ℂ) =ᵐ[volume] fun x => (z - ψ x)⁻¹ * f x :=
      lpBoundedMulCLM_coeFn _ _ _ f
    have hright : (algebraMap ℂ (H →L[ℂ] H) z - T) * S = 1 := by
      apply ContinuousLinearMap.ext
      intro f
      apply Lp.ext
      filter_upwards [shifted_mul_ae hT z (S f), hS f] with x hA hSf
      change ((algebraMap ℂ (H →L[ℂ] H) z - T) (S f) : ℝ → ℂ) x = f x
      rw [hA, hSf, ← mul_assoc, mul_inv_cancel₀ (hne x), one_mul]
    have hleft : S * (algebraMap ℂ (H →L[ℂ] H) z - T) = 1 := by
      apply ContinuousLinearMap.ext
      intro f
      apply Lp.ext
      filter_upwards [hS ((algebraMap ℂ (H →L[ℂ] H) z - T) f), shifted_mul_ae hT z f]
        with x hSf hA
      change (S ((algebraMap ℂ (H →L[ℂ] H) z - T) f) : ℝ → ℂ) x = f x
      rw [hSf, hA, ← mul_assoc, inv_mul_cancel₀ (hne x), one_mul]
    exact hz (spectrum.mem_resolventSet_of_left_right_inverse hright hleft)
  · exact closure_minimal (range_subset_iff.mpr
      (value_mem_spectrum_of_ae_mul_continuous hψ hT)) (spectrum.isClosed T)

end
end GaloisForLFunctions.HTGeometry
