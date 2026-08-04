import GaloisForLFunctions.HTGeometry.ClockTubeStep
import GaloisForLFunctions.HTGeometry.ClockParametricIntegralHolomorphy

/-!
# Slice holomorphy on a tube

In one transverse variable the iteration carries holomorphy on a strip, and holomorphy of a
parametric integral follows from the fact that a function differentiable on an open subset of the
plane is analytic there. In several variables that implication is Hartogs's theorem, which is not
available; so the iteration carries instead the property the estimates actually use:

*holomorphy along every coordinate slice through every point of the tube.*

This is weaker than joint analyticity, it is implied by it, and — the point of this file — it passes
through a parametric integral for free, because along a fixed slice the integral is a one-variable
parametric integral of a family holomorphic on a strip.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- Holomorphy along every coordinate slice through every point of the tube. -/
def SliceHolo (w : (Fin k → ℂ) → ℂ) (ρ : ℝ) : Prop :=
  ∀ z ∈ tube k ρ, ∀ i : Fin k,
    DifferentiableOn ℂ (fun ζ : ℂ => w (Function.update z i ζ)) (imStrip ρ)

theorem sliceHolo_of_differentiableOn {ρ : ℝ} {w : (Fin k → ℂ) → ℂ}
    (hw : DifferentiableOn ℂ w (tube k ρ)) : SliceHolo w ρ :=
  fun _ hz i => differentiableOn_updateSlice hw hz i

theorem sliceHolo_mono {ρ ρ' : ℝ} {w : (Fin k → ℂ) → ℂ} (h : SliceHolo w ρ') (hρ : ρ ≤ ρ') :
    SliceHolo w ρ :=
  fun z hz i => (h z (tube_mono hρ hz) i).mono (imStrip_mono hρ)

/-! ## The Cauchy estimates from slice holomorphy alone -/

/-- **The first partial derivative, from slice holomorphy.** -/
theorem norm_cpartial_le_of_sliceHolo {ρ ρ' M : ℝ} (hρ : ρ < ρ') {w : (Fin k → ℂ) → ℂ}
    (hw : SliceHolo w ρ') (hM : ∀ z ∈ tube k ρ', ‖w z‖ ≤ M) {z : Fin k → ℂ}
    (hz : ∀ i, |(z i).im| ≤ ρ) (i : Fin k) : ‖cpartial i w z‖ ≤ 2 * M / (ρ' - ρ) := by
  have hzt : z ∈ tube k ρ' := fun j => lt_of_le_of_lt (hz j) hρ
  exact norm_deriv_le_on_imStrip hρ (hw z hzt i)
    (fun ζ hζ => hM _ (update_mem_tube hzt i hζ)) (hz i)

/-- **The second partial derivative, from slice holomorphy.** -/
theorem norm_cpartial_cpartial_le_of_sliceHolo {ρ ρ' M : ℝ} (hρ : ρ < ρ')
    {w : (Fin k → ℂ) → ℂ} (hw : SliceHolo w ρ') (hM : ∀ z ∈ tube k ρ', ‖w z‖ ≤ M)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) (i : Fin k) :
    ‖cpartial i (cpartial i w) z‖ ≤ 16 * M / (ρ' - ρ) ^ 2 := by
  have hzt : z ∈ tube k ρ' := fun j => lt_of_le_of_lt (hz j) hρ
  rw [cpartial_cpartial_eq]
  exact norm_deriv_deriv_le_on_imStrip hρ (hw z hzt i)
    (fun ζ hζ => hM _ (update_mem_tube hzt i hζ)) (hz i)

/-- **The estimate of the step operator, from slice holomorphy.** -/
theorem norm_tubeStep_le_of_sliceHolo {ρ ρ' Mv Mw : ℝ} (hρ : ρ < ρ') (hMv0 : 0 ≤ Mv)
    {V w : (Fin k → ℂ) → ℂ} (hw : SliceHolo w ρ')
    (hMw : ∀ z ∈ tube k ρ', ‖w z‖ ≤ Mw) (hMv : ∀ z ∈ tube k ρ', ‖V z‖ ≤ Mv)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    ‖tubeStep V w z‖ ≤ (4 * k / (ρ' - ρ) ^ 2 + Mv / 4) * Mw := by
  have hgap : (0 : ℝ) < ρ' - ρ := by linarith
  have hzt : z ∈ tube k ρ' := fun j => lt_of_le_of_lt (hz j) hρ
  have hMw0 : (0 : ℝ) ≤ Mw := le_trans (norm_nonneg _) (hMw z hzt)
  have hterm : ∀ i : Fin k, ‖cpartial i (cpartial i w) z‖ ≤ 16 * Mw / (ρ' - ρ) ^ 2 :=
    fun i => norm_cpartial_cpartial_le_of_sliceHolo hρ hw hMw hz i
  have hsum : ‖∑ i, cpartial i (cpartial i w) z‖ ≤ k * (16 * Mw / (ρ' - ρ) ^ 2) := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ i : Fin k, ‖cpartial i (cpartial i w) z‖
        ≤ ∑ _i : Fin k, 16 * Mw / (ρ' - ρ) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = k * (16 * Mw / (ρ' - ρ) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpot : ‖V z * w z‖ ≤ Mv * Mw := by
    rw [norm_mul]
    exact mul_le_mul (hMv z hzt) (hMw z hzt) (norm_nonneg _) hMv0
  have hdiv : ‖tubeStep V w z‖
      = ‖(∑ i, cpartial i (cpartial i w) z) + V z * w z‖ / 4 := by
    rw [tubeStep, norm_div]
    norm_num
  have htri : ‖(∑ i, cpartial i (cpartial i w) z) + V z * w z‖
      ≤ k * (16 * Mw / (ρ' - ρ) ^ 2) + Mv * Mw :=
    le_trans (norm_add_le _ _) (add_le_add hsum hpot)
  have hfinal : (k * (16 * Mw / (ρ' - ρ) ^ 2) + Mv * Mw) / 4
      = (4 * k / (ρ' - ρ) ^ 2 + Mv / 4) * Mw := by
    field_simp
    ring
  rw [hdiv]
  calc ‖(∑ i, cpartial i (cpartial i w) z) + V z * w z‖ / 4
      ≤ (k * (16 * Mw / (ρ' - ρ) ^ 2) + Mv * Mw) / 4 := by linarith
    _ = (4 * k / (ρ' - ρ) ^ 2 + Mv / 4) * Mw := hfinal

/-! ## Slice holomorphy of a parametric integral -/

/-- **Slice holomorphy passes through a parametric integral.** Along a fixed slice the integral is a
one-variable parametric integral of a family holomorphic on a strip. -/
theorem sliceHolo_intervalIntegral {ρ : ℝ} {F : ℝ → (Fin k → ℂ) → ℂ} (a b : ℝ)
    (hFc : ∀ z ∈ tube k ρ, ∀ i : Fin k,
      ContinuousOn (fun q : ℝ × ℂ => F q.1 (Function.update z i q.2)) (univ ×ˢ imStrip ρ))
    (hFh : ∀ t : ℝ, SliceHolo (F t) ρ) :
    SliceHolo (fun z => ∫ t in a..b, F t z) ρ := by
  intro z hz i
  exact differentiableOn_intervalIntegral_of_holomorphic_on
    (F := fun t ζ => F t (Function.update z i ζ)) (hFc z hz i) fun t => hFh t z hz i

end GaloisForLFunctions.HTGeometry
