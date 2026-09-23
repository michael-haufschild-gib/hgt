import GaloisForLFunctions.RHTower.SuzukiPolarConvolutionRate
import GaloisForLFunctions.HTGeometry.DigammaVerticalUniformLog
import GaloisForLFunctions.HTGeometry.GammaShiftExpIntegral
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The bounded part of Suzuki's exterior symbol

Suzuki's exact frequency symbol is

`p_a(ξ) = Re ψ(1/4 + iξ/2) - log π - 2 ∑_{n ≤ e^{2a}} Λ(n) n^{-1/2} cos(ξ log n) + 𝓕(r''_{0,a})(ξ)`.

Normalizing against the logarithmic weight `L(ξ) = log ⟨ξ⟩` leaves the archimedean remainder

`q_a(ξ) = Re ψ(1/4 + iξ/2) - L(ξ) - log π + 𝓕(r''_{0,a})(ξ)`,

which this module proves bounded on the whole frequency line.  Away from the origin the vertical
digamma asymptotic controls it; near the origin the abscissa `1/4` keeps the argument off the poles
of `ψ`, so continuity and compactness do; conjugation symmetry transports both to negative `ξ`.
The polar block contributes at most the `L¹` norm of the truncated kernel, which is finite because
the kernel is bounded on its compact support.
-/

open Set MeasureTheory Filter Topology Complex
open scoped FourierTransform

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The archimedean evaluation point `1/4 + iξ/2` of Suzuki's symbol. -/
def suzukiArchPoint (ξ : ℝ) : ℂ := ((1 / 4 : ℝ) : ℂ) + ((ξ / 2 : ℝ) : ℂ) * Complex.I

theorem suzukiArchPoint_re (ξ : ℝ) : (suzukiArchPoint ξ).re = 1 / 4 := by
  simp [suzukiArchPoint]

theorem continuous_suzukiArchPoint : Continuous suzukiArchPoint := by
  unfold suzukiArchPoint
  fun_prop

theorem suzukiArchPoint_conj (ξ : ℝ) :
    (starRingEnd ℂ) (suzukiArchPoint ξ) = suzukiArchPoint (-ξ) := by
  unfold suzukiArchPoint
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The logarithmic frequency weight `L(ξ) = log ⟨ξ⟩`. -/
def suzukiExteriorLogWeight (ξ : ℝ) : ℝ := (1 / 2) * Real.log (1 + ξ ^ (2 : ℕ))

theorem suzukiExteriorLogWeight_neg (ξ : ℝ) :
    suzukiExteriorLogWeight (-ξ) = suzukiExteriorLogWeight ξ := by
  simp [suzukiExteriorLogWeight]

/-- The archimedean part of the normalized symbol remainder. -/
def suzukiArchRemainder (ξ : ℝ) : ℝ :=
  (Complex.digamma (suzukiArchPoint ξ)).re - suzukiExteriorLogWeight ξ - Real.log Real.pi

theorem continuous_suzukiArchRemainder : Continuous suzukiArchRemainder := by
  have hdig : Continuous fun ξ : ℝ => Complex.digamma (suzukiArchPoint ξ) := by
    rw [continuous_iff_continuousAt]
    intro ξ
    have hre : suzukiArchPoint ξ ∈ {z : ℂ | 0 < z.re} := by
      simp [suzukiArchPoint_re]
    exact (continuousOn_digamma_rePos.continuousAt (isOpen_rePos.mem_nhds hre)).comp
      continuous_suzukiArchPoint.continuousAt
  have hlog : Continuous suzukiExteriorLogWeight := by
    unfold suzukiExteriorLogWeight
    have : ∀ ξ : ℝ, (0:ℝ) < 1 + ξ ^ (2 : ℕ) := fun ξ => by positivity
    fun_prop (disch := intro ξ; positivity)
  unfold suzukiArchRemainder
  exact ((Complex.continuous_re.comp hdig).sub hlog).sub continuous_const

/-- The archimedean remainder is even. -/
theorem suzukiArchRemainder_neg (ξ : ℝ) : suzukiArchRemainder (-ξ) = suzukiArchRemainder ξ := by
  unfold suzukiArchRemainder
  rw [suzukiExteriorLogWeight_neg]
  congr 2
  rw [← suzukiArchPoint_conj ξ, ReflectedDigammaAnomaly.digamma_conj]
  simp

/-- The logarithmic gap between the vertical asymptote and the frequency weight is bounded. -/
theorem abs_log_half_sub_logWeight_le {ξ : ℝ} (hξ : 2 ≤ ξ) :
    |Real.log (ξ / 2) - suzukiExteriorLogWeight ξ| ≤ Real.log 2 + Real.log 2 / 2 := by
  have hξpos : (0:ℝ) < ξ := by linarith
  have h1 : Real.log (ξ / 2) = Real.log ξ - Real.log 2 := by
    rw [Real.log_div (ne_of_gt hξpos) (by norm_num)]
  have hsq : suzukiExteriorLogWeight ξ - Real.log ξ =
      (1 / 2) * Real.log ((1 + ξ ^ (2 : ℕ)) / ξ ^ (2 : ℕ)) := by
    rw [suzukiExteriorLogWeight, Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hratio_le : (1 + ξ ^ (2 : ℕ)) / ξ ^ (2 : ℕ) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hratio_ge : (1:ℝ) ≤ (1 + ξ ^ (2 : ℕ)) / ξ ^ (2 : ℕ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hlogle : Real.log ((1 + ξ ^ (2 : ℕ)) / ξ ^ (2 : ℕ)) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) hratio_le
  have hlogge : 0 ≤ Real.log ((1 + ξ ^ (2 : ℕ)) / ξ ^ (2 : ℕ)) := Real.log_nonneg hratio_ge
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> [skip; skip] <;> rw [h1] <;> nlinarith [hsq, hlogle, hlogge]

/-- **`(17)`, archimedean half: the normalized digamma remainder is bounded on the whole line.** -/
theorem exists_bound_suzukiArchRemainder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, |suzukiArchRemainder ξ| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    exists_uniform_bound_digamma_sub_vertLog (M := (1 / 4 : ℝ)) (by norm_num)
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    continuous_suzukiArchRemainder.continuousOn
  refine ⟨max C₂ (2 * C₁ + Real.log 2 + Real.log 2 / 2 + |Real.log Real.pi|), ?_, ?_⟩
  · exact le_trans (le_max_of_le_left (le_trans (norm_nonneg _) (hC₂ 0 (by norm_num)))) le_rfl
  · intro ξ
    by_cases hsmall : |ξ| ≤ 2
    case pos =>
      refine le_trans ?_ (le_max_left _ _)
      have := hC₂ ξ (by rw [mem_Icc]; exact abs_le.mp hsmall)
      simpa [Real.norm_eq_abs] using this
    case neg =>
      have hbig : 2 < |ξ| := lt_of_not_ge hsmall
      -- reduce to `ξ ≥ 2` by evenness
      have key : ∀ η : ℝ, 2 ≤ η →
          |suzukiArchRemainder η|
            ≤ 2 * C₁ + Real.log 2 + Real.log 2 / 2 + |Real.log Real.pi| := by
        intro η hη
        have hηpos : (0:ℝ) < η := by linarith
        have ht : (1:ℝ) ≤ η / 2 := by linarith
        have htpos : (0:ℝ) < η / 2 := by linarith
        have hbound := hC₁ (1 / 4 : ℝ) (η / 2) (by norm_num) le_rfl ht
        have hre : |(Complex.digamma (suzukiArchPoint η)).re - Real.log (η / 2)|
            ≤ C₁ / (η / 2) := by
          have hz : suzukiArchPoint η
              = ((1 / 4 : ℝ) : ℂ) + ((η / 2 : ℝ) : ℂ) * Complex.I := rfl
          have hnorm := hbound
          rw [← hz] at hnorm
          have hred : (Complex.digamma (suzukiArchPoint η) - GaloisForLFunctions.vertLog (η / 2)).re
              = (Complex.digamma (suzukiArchPoint η)).re - Real.log (η / 2) := by
            simp [GaloisForLFunctions.vertLog]
          calc |(Complex.digamma (suzukiArchPoint η)).re - Real.log (η / 2)|
              = |(Complex.digamma (suzukiArchPoint η) - GaloisForLFunctions.vertLog (η / 2)).re| := by rw [hred]
            _ ≤ ‖Complex.digamma (suzukiArchPoint η) - GaloisForLFunctions.vertLog (η / 2)‖ :=
                Complex.abs_re_le_norm _
            _ ≤ C₁ / (η / 2) := hnorm
        have hdiv : C₁ / (η / 2) ≤ 2 * C₁ := by
          rw [div_le_iff₀ htpos]
          nlinarith
        have hgap := abs_log_half_sub_logWeight_le hη
        have hsplit : suzukiArchRemainder η
            = ((Complex.digamma (suzukiArchPoint η)).re - Real.log (η / 2))
              + (Real.log (η / 2) - suzukiExteriorLogWeight η) - Real.log Real.pi := by
          unfold suzukiArchRemainder
          ring
        rw [hsplit]
        have h1 := abs_le.mp hre
        have h2 := abs_le.mp hgap
        have h3 := abs_le.mp (le_refl |Real.log Real.pi|)
        rw [abs_le]
        constructor <;> [linarith [h1.1, h2.1, h3.1, hdiv]; linarith [h1.2, h2.2, h3.2, hdiv]]
      refine le_trans ?_ (le_max_right _ _)
      rcases abs_cases ξ with ⟨heq, hpos⟩ | ⟨heq, hneg⟩
      · exact key ξ (by rw [heq] at hbig; linarith)
      · have hneg2 : 2 ≤ -ξ := by rw [heq] at hbig; linarith
        rw [← suzukiArchRemainder_neg ξ]
        exact key (-ξ) hneg2

/-- Suzuki's polar kernel truncated to the compact aperture collar. -/
def suzukiTruncatedPolarKernel (a : ℝ) : ℝ → ℂ :=
  Set.indicator (Set.Icc (-(2 * a)) (2 * a)) fun t => (suzukiWeilRemainderKernel t : ℂ)

theorem integrable_suzukiTruncatedPolarKernel (a : ℝ) :
    Integrable (suzukiTruncatedPolarKernel a) volume := by
  rw [suzukiTruncatedPolarKernel, integrable_indicator_iff measurableSet_Icc]
  exact ContinuousOn.integrableOn_compact isCompact_Icc
    (Complex.continuous_ofReal.comp continuous_suzukiWeilRemainderKernel).continuousOn

/-- **`(17)`, polar half: the truncated polar block has a bounded Fourier transform.** -/
theorem norm_fourier_suzukiTruncatedPolarKernel_le (a ξ : ℝ) :
    ‖𝓕 (suzukiTruncatedPolarKernel a) ξ‖
      ≤ ∫ t, ‖suzukiTruncatedPolarKernel a t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- The exact bounded remainder of Suzuki's normalized symbol. -/
def suzukiSymbolRemainder (a : ℝ) (ξ : ℝ) : ℂ :=
  ((suzukiArchRemainder ξ : ℝ) : ℂ) + 𝓕 (suzukiTruncatedPolarKernel a) ξ

/-- **`(17)`: the normalized symbol remainder is uniformly bounded in frequency.** -/
theorem exists_bound_suzukiSymbolRemainder (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ‖suzukiSymbolRemainder a ξ‖ ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_suzukiArchRemainder
  refine ⟨C₁ + ∫ t, ‖suzukiTruncatedPolarKernel a t‖, ?_, ?_⟩
  · have : 0 ≤ ∫ t, ‖suzukiTruncatedPolarKernel a t‖ :=
      integral_nonneg fun t => norm_nonneg _
    linarith
  · intro ξ
    have h1 : ‖((suzukiArchRemainder ξ : ℝ) : ℂ)‖ ≤ C₁ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hC₁ ξ
    have h2 := norm_fourier_suzukiTruncatedPolarKernel_le a ξ
    calc ‖suzukiSymbolRemainder a ξ‖
        ≤ ‖((suzukiArchRemainder ξ : ℝ) : ℂ)‖
            + ‖𝓕 (suzukiTruncatedPolarKernel a) ξ‖ := norm_add_le _ _
      _ ≤ C₁ + ∫ t, ‖suzukiTruncatedPolarKernel a t‖ := by linarith

end

end RHTower
