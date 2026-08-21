import GaloisForLFunctions.RHTower.ConnesLogShiftKernel
import GaloisForLFunctions.RHTower.ConnesSUnitSupBound

/-!
# The cutoff commutator estimate

§VII (42)-(46) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The error term of the local trace formula is controlled by the commutator of the Besov
convolution `C_{α,v}` with multiplication by the cutoff excess `ε_Λ(x) = (log|x| − 2 log'Λ)^+`.
The commutator is *not* a derivative: the two leading terms cancel identically, leaving

  `(ε_Λ(x+ε) − ε_Λ(x)) η(x+ε)`,

and `|ε_Λ(x+ε) − ε_Λ(x)| ≤ | log|x+ε| − log|x| |` because `t ↦ t^+` is `1`-Lipschitz.  Connes'
scaling inequality (45) then bounds the whole convolution by `c'_α |x|^{-α} sup_{|ε|≤1}|η(x+ε)|`,
which is (46).
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Connes' cutoff excess `ε_Λ(x) = (log|x| − L)^+` with `L = 2 log' Λ`. -/
def connesCutoffExcess (L x : ℝ) : ℝ := max (Real.log |x| - L) 0

theorem connesCutoffExcess_nonneg (L x : ℝ) : 0 ≤ connesCutoffExcess L x := le_max_right _ _

/-- **§VII (43) applied to the cutoff.**  The cutoff excess is `1`-Lipschitz in `log|x|`. -/
theorem connes_cutoffExcess_diff_le (L x y : ℝ) :
    |connesCutoffExcess L y - connesCutoffExcess L x|
      ≤ abs (Real.log |y| - Real.log |x|) := by
  have h := connes_abs_posPart_sub_posPart_le (Real.log |y| - L) (Real.log |x| - L)
  have heq : (Real.log |y| - L) - (Real.log |x| - L) = Real.log |y| - Real.log |x| := by ring
  rwa [heq] at h

/-- **The commutator identity.**  The two leading terms of the commutator of the Besov kernel
with multiplication by `ε_Λ` cancel identically. -/
theorem connes_commutator_identity (L : ℝ) (η : ℝ → ℂ) (x ε : ℝ) :
    ((connesCutoffExcess L (x + ε) : ℂ) * η (x + ε) - (connesCutoffExcess L x : ℂ) * η x)
        - (connesCutoffExcess L x : ℂ) * (η (x + ε) - η x)
      = ((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε) := by
  push_cast
  ring

/-- Integrability of the cut-off logarithmic-difference kernel at a nonzero point. -/
theorem connes_integrable_logShift {x : ℝ} (hx : x ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {Ψ : ℝ → ℝ} (hΨc : Continuous Ψ) (hΨ0 : ∀ t, 0 ≤ Ψ t) (hΨ1 : ∀ t, Ψ t ≤ 1) :
    Integrable (fun ε : ℝ => Ψ (ε / x) *
      (abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹)) := by
  have hxpos : (0 : ℝ) < |x| := abs_pos.mpr hx
  set H : ℝ → ℝ := fun ε => Ψ (ε / x) *
      (abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹) with hH
  have hK : Integrable (connesLogShiftKernel α) := connes_integrable_logShiftKernel hα0 hα1
  have hKnn : ∀ y : ℝ, 0 ≤ connesLogShiftKernel α y := by
    intro y
    rw [connesLogShiftKernel]
    positivity
  have hΨK : Integrable (fun y : ℝ => Ψ y * connesLogShiftKernel α y) := by
    refine Integrable.mono' hK (hΨc.aestronglyMeasurable.mul hK.aestronglyMeasurable) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hΨ0 y) (hKnn y))]
    calc Ψ y * connesLogShiftKernel α y ≤ 1 * connesLogShiftKernel α y :=
          mul_le_mul_of_nonneg_right (hΨ1 y) (hKnn y)
      _ = connesLogShiftKernel α y := one_mul _
  have hae : ∀ᵐ y : ℝ, y ≠ 0 ∧ 1 + y ≠ 0 := by
    have h0 : (volume : Measure ℝ) {(0 : ℝ)} = 0 := Real.volume_singleton
    have h1 : (volume : Measure ℝ) {(-1 : ℝ)} = 0 := Real.volume_singleton
    filter_upwards [compl_mem_ae_iff.2 h0, compl_mem_ae_iff.2 h1] with y hy0 hy1
    refine ⟨by simpa using hy0, ?_⟩
    intro hc
    exact (by simpa using hy1 : y ≠ -1) (by linarith [hc])
  have hpt : ∀ y : ℝ, y ≠ 0 → 1 + y ≠ 0 →
      (|x| ^ (1 + α))⁻¹ * (Ψ y * connesLogShiftKernel α y) = H (x * y) := by
    intro y hy0 hy1
    have hdiv : x * y / x = y := by field_simp
    have habs : |x + x * y| = |x| * |1 + y| := by
      rw [show x + x * y = x * (1 + y) by ring, abs_mul]
    have hlog : Real.log |x + x * y| - Real.log |x| = Real.log |1 + y| := by
      rw [habs, Real.log_mul (ne_of_gt hxpos) (abs_ne_zero.mpr hy1)]
      ring
    have habsxy : |x * y| = |x| * |y| := abs_mul x y
    have hpow : (|x * y| ^ (1 + α))⁻¹ = (|x| ^ (1 + α))⁻¹ * (|y| ^ (1 + α))⁻¹ := by
      rw [habsxy, Real.mul_rpow (le_of_lt hxpos) (abs_nonneg y), mul_inv]
    simp only [hH, hdiv, hlog, hpow, connesLogShiftKernel]
    ring
  have hscaled : Integrable (fun y : ℝ => H (x * y)) := by
    refine (hΨK.const_mul ((|x| ^ (1 + α))⁻¹)).congr ?_
    filter_upwards [hae] with y hy
    exact hpt y hy.1 hy.2
  exact (integrable_comp_mul_left_iff H hx).mp hscaled

/-- **§VII (46).**  The cutoff commutator of the Besov kernel is bounded by
`c'_α |x|^{-α} · sup_{|ε| ≤ 1} ‖η(x+ε)‖`. -/
theorem connes_cutoff_commutator_bound {x : ℝ} (hx : x ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {Ψ : ℝ → ℝ} (hΨc : Continuous Ψ) (hΨ0 : ∀ t, 0 ≤ Ψ t) (hΨ1 : ∀ t, Ψ t ≤ 1)
    (L : ℝ) (η : ℝ → ℂ) {M : ℝ} (hM : ∀ ε : ℝ, ‖η (x + ε)‖ ≤ M) :
    (∫ ε : ℝ, Ψ (ε / x) *
        (‖((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε)‖
          * (|ε| ^ (1 + α))⁻¹))
      ≤ M * ((|x| ^ (-α)) * ∫ y : ℝ, connesLogShiftKernel α y) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hmaj : Integrable (fun ε : ℝ => M * (Ψ (ε / x) *
      (abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹))) :=
    (connes_integrable_logShift hx hα0 hα1 hΨc hΨ0 hΨ1).const_mul M
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume] fun ε : ℝ => Ψ (ε / x) *
      (‖((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε)‖
        * (|ε| ^ (1 + α))⁻¹) := by
    filter_upwards with ε
    have := hΨ0 (ε / x)
    have h2 : (0 : ℝ) ≤ (|ε| ^ (1 + α))⁻¹ := by positivity
    have h3 := norm_nonneg
      (((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε))
    exact mul_nonneg this (mul_nonneg h3 h2)
  have hle : (fun ε : ℝ => Ψ (ε / x) *
      (‖((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε)‖
        * (|ε| ^ (1 + α))⁻¹))
      ≤ᵐ[volume] fun ε : ℝ => M * (Ψ (ε / x) *
      (abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹)) := by
    filter_upwards with ε
    have hpow : (0 : ℝ) ≤ (|ε| ^ (1 + α))⁻¹ := by positivity
    have hnorm : ‖((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ)
        * η (x + ε)‖
        ≤ M * abs (Real.log |x + ε| - Real.log |x|) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |connesCutoffExcess L (x + ε) - connesCutoffExcess L x| * ‖η (x + ε)‖
          ≤ abs (Real.log |x + ε| - Real.log |x|) * M :=
            mul_le_mul (connes_cutoffExcess_diff_le L x (x + ε)) (hM ε) (norm_nonneg _)
              (abs_nonneg _)
        _ = M * abs (Real.log |x + ε| - Real.log |x|) := by ring
    have hstep : ‖((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ)
        * η (x + ε)‖ * (|ε| ^ (1 + α))⁻¹
        ≤ M * abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹ :=
      mul_le_mul_of_nonneg_right hnorm hpow
    calc Ψ (ε / x) * (‖((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ)
          * η (x + ε)‖ * (|ε| ^ (1 + α))⁻¹)
        ≤ Ψ (ε / x) * (M * abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹) :=
          mul_le_mul_of_nonneg_left hstep (hΨ0 _)
      _ = M * (Ψ (ε / x) *
            (abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹)) := by ring
  refine le_trans (integral_mono_of_nonneg hnn hmaj hle) ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (connes_logShift_bound hx hα0 hα1 hΨc hΨ0 hΨ1) hM0

end

end GaloisForLFunctions.RHTower
