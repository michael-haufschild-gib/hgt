import GaloisForLFunctions.HTGeometry.VerticalEdgeVanishing
import GaloisForLFunctions.RHTower.XiCDerivStripDecay
import GaloisForLFunctions.RHTower.XiQuotientRealDecay
import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# Vertical-edge vanishing for the single-pole eigen integrand

The concrete boundary estimate of the eigen-pair assembly: on the right vertical edge the
single-pole integrand `deriv XiC · sharp F_β · (z − p)⁻¹` is dominated, for large abscissa, by
the product of the certified `deriv XiC` substrip bound, the (18a) bound of the reflected
quotient, and the inverse-linear factor `1` (once the edge has passed the pole).  The vanishing
engine then kills the edge in the widening limit; an eventual-bound variant of the engine is
provided for exactly this use.
-/

namespace RHTower

noncomputable section

open MeasureTheory Complex Filter

/-- Eventual-bound variant of the right vertical-edge vanishing engine. -/
theorem tendsto_vertical_edge_zero_right_eventually {G : ℂ → ℂ} {Y C δ : ℝ}
    (hY : 0 ≤ Y) (hδ : 0 < δ)
    (hbound : ∀ᶠ X : ℝ in atTop, ∀ y : ℝ, |y| ≤ Y →
      ‖G ((X : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(δ * X))) :
    Tendsto (fun X : ℝ => ∫ y in (-Y)..Y, G ((X : ℂ) + (y : ℂ) * Complex.I))
      atTop (nhds 0) := by
  refine squeeze_zero_norm'
    (a := fun X : ℝ => C * |Y - (-Y)| * Real.exp (-(δ * X))) ?_ ?_
  · filter_upwards [hbound] with X hX
    have hseg : ∀ y ∈ Set.uIoc (-Y) Y,
        ‖G ((X : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(δ * X)) := by
      intro y hy
      have hy' : |y| ≤ Y := by
        rcases Set.mem_uIoc.mp hy with h | h
        · rw [abs_le]; constructor <;> linarith [h.1, h.2]
        · exact absurd (lt_of_lt_of_le h.1 h.2) (by linarith)
      exact hX y hy'
    calc ‖∫ y in (-Y)..Y, G ((X : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ C * Real.exp (-(δ * X)) * |Y - (-Y)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hseg
      _ = C * |Y - (-Y)| * Real.exp (-(δ * X)) := by ring
  · have hexp : Tendsto (fun X : ℝ => Real.exp (-(δ * X))) atTop (nhds 0) := by
      have h1 : Tendsto (fun X : ℝ => δ * X) atTop atTop :=
        Tendsto.const_mul_atTop hδ tendsto_id
      have h2 : Tendsto (fun X : ℝ => -(δ * X)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp h1
      exact Real.tendsto_exp_atBot.comp h2
    simpa using hexp.const_mul (C * |Y - (-Y)|)

/-- **Right vertical edge of the single-pole eigen integrand vanishes.**  With the certified
`deriv XiC` substrip bound, the (18a) bound for the reflected quotient, and the inverse-linear
pole factor, the right-edge segment integrals tend to zero as the aperture widens. -/
theorem tendsto_vertical_eigen_right {β p : ℂ} (hβ : XiC β = 0)
    {A δ Y : ℝ} (hA1 : A < 1) (hδ0 : 0 < δ)
    (hδ4 : 2 * δ < Real.pi / 2) (hA0 : 0 ≤ A) (hY0 : 0 ≤ Y) (hYA : Y ≤ A) :
    Tendsto (fun X : ℝ => ∫ y in (-Y)..Y,
        deriv XiC ((X : ℂ) + (y : ℂ) * Complex.I) *
          xiWeilSharp (xiThetaEigenFourier β) ((X : ℂ) + (y : ℂ) * Complex.I) *
          (((X : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹)
      atTop (nhds 0) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_XiC_deriv_horizontal_le hA1 hδ0.le hδ4
  obtain ⟨C₂, hC₂, h₂⟩ :=
    exists_norm_xiThetaEigenFourier_horizontal_le hβ hA0 hA1 hδ0.le hδ4
  have hδ2 : (0 : ℝ) < 2 * δ := by linarith
  refine tendsto_vertical_edge_zero_right_eventually
    (G := fun z : ℂ => deriv XiC z * xiWeilSharp (xiThetaEigenFourier β) z * (z - p)⁻¹)
    (C := C₁ * C₂) (δ := 2 * δ) hY0 hδ2 ?_
  filter_upwards [eventually_ge_atTop (‖p‖ + 1), eventually_ge_atTop (0 : ℝ)] with X hXp hX0
  intro y hy
  have hyA : |y| ≤ A := le_trans hy hYA
  have hb₁ := h₁ X y hyA
  have hb₂c : ‖xiWeilSharp (xiThetaEigenFourier β) ((X : ℂ) + (y : ℂ) * Complex.I)‖ =
      ‖xiThetaEigenFourier β ((X : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)‖ := by
    rw [xiWeilSharp]
    rw [RCLike.norm_conj]
    congr 1
    push_cast
    simp [map_add, map_mul, Complex.conj_I]
  have hb₂ : ‖xiWeilSharp (xiThetaEigenFourier β) ((X : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      C₂ * Real.exp (-(δ * |X|)) := by
    rw [hb₂c]
    exact h₂ X (-y) (by rwa [abs_neg])
  have hinv : ‖(((X : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have hre : X - p.re ≤ |(((X : ℂ) + (y : ℂ) * Complex.I) - p).re| := by
      have : (((X : ℂ) + (y : ℂ) * Complex.I) - p).re = X - p.re := by simp
      rw [this, abs_of_nonneg]
      have hpre : p.re ≤ ‖p‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm p)
      linarith
    have hnorm : 1 ≤ ‖((X : ℂ) + (y : ℂ) * Complex.I) - p‖ := by
      have hpre : p.re ≤ ‖p‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm p)
      calc (1 : ℝ) ≤ X - p.re := by linarith
        _ ≤ |(((X : ℂ) + (y : ℂ) * Complex.I) - p).re| := hre
        _ ≤ ‖((X : ℂ) + (y : ℂ) * Complex.I) - p‖ := Complex.abs_re_le_norm _
    exact inv_le_one_of_one_le₀ hnorm
  have hXabs : |X| = X := abs_of_nonneg hX0
  calc ‖deriv XiC ((X : ℂ) + (y : ℂ) * Complex.I) *
        xiWeilSharp (xiThetaEigenFourier β) ((X : ℂ) + (y : ℂ) * Complex.I) *
        (((X : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹‖
      = ‖deriv XiC ((X : ℂ) + (y : ℂ) * Complex.I)‖ *
        ‖xiWeilSharp (xiThetaEigenFourier β) ((X : ℂ) + (y : ℂ) * Complex.I)‖ *
        ‖(((X : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ (C₁ * Real.exp (-(δ * |X|))) * (C₂ * Real.exp (-(δ * |X|))) * 1 := by
        gcongr
    _ = C₁ * C₂ * Real.exp (-(2 * δ * X)) := by
        rw [hXabs, mul_one,
          show (-(2 * δ * X) : ℝ) = -(δ * X) + -(δ * X) by ring, Real.exp_add]
        ring

end

end RHTower
