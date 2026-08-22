import GaloisForLFunctions.RHTower.ConnesCutoffTailDecay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The fractional kernel of §VII (39): `∫_0^∞ (1 − cos(tε)) ε^{-1-α} dε = C_α t^α`

§VII (39)-(41) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes' convolution operator `C_{α,v}` of (39) has, on the archimedean place, Fourier multiplier
whose real part is `−∫ ψ(|ε|)(1 − cos(2πxε))|ε|^{-1-α} dε`.  His assertion that this multiplier
*"behaves like `|x_v|^α`"* rests on the exact scaling law proved here: the untruncated kernel
integral is a positive constant times `t^α`, because the measure `ε^{-1-α}dε` is homogeneous of
degree `−α`.

Everything is one-sided (`Ioi 0`); the kernel is even, so the two-sided integral is twice this.
-/

open MeasureTheory Real Set

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The α-stable kernel `(1 − cos ε) ε^{-1-α}`. -/
def connesLevyKernel (α ε : ℝ) : ℝ := (1 - Real.cos ε) * ε ^ (-1 - α)

theorem connesLevyKernel_nonneg (α : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ connesLevyKernel α ε := by
  refine mul_nonneg (by linarith [Real.cos_le_one ε]) (Real.rpow_nonneg hε _)

theorem connesLevyKernel_continuousOn (α : ℝ) :
    ContinuousOn (connesLevyKernel α) (Ioi (0 : ℝ)) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
  · exact continuousAt_const.sub (Real.continuous_cos.continuousAt)
  · exact Real.continuousAt_rpow_const x (-1 - α) (Or.inl hx0)

theorem connes_levy_integrableOn_Ioc {α : ℝ} (hα : α < 2) :
    IntegrableOn (connesLevyKernel α) (Ioc (0 : ℝ) 1) volume := by
  have hmaj : IntegrableOn (fun ε : ℝ => ε ^ (1 - α) / 2) (Ioc (0 : ℝ) 1) volume := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := (1:ℝ)) (r := 1 - α)
      (by linarith)).1
    exact h.div_const 2
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact (connesLevyKernel_continuousOn α).mono Ioc_subset_Ioi_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with ε hε
    have hε0 : (0 : ℝ) < ε := hε.1
    have hnn := connesLevyKernel_nonneg α hε0.le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hcos : 1 - Real.cos ε ≤ ε ^ 2 / 2 := by
      have := Real.one_sub_sq_div_two_le_cos (x := ε)
      linarith
    have hpow : (0 : ℝ) < ε ^ (-1 - α) := Real.rpow_pos_of_pos hε0 _
    have hprod : ε ^ (2 : ℕ) * ε ^ (-1 - α) = ε ^ (1 - α) := by
      rw [← Real.rpow_natCast ε 2, ← Real.rpow_add hε0]
      congr 1
      push_cast
      ring
    calc (1 - Real.cos ε) * ε ^ (-1 - α)
        ≤ (ε ^ 2 / 2) * ε ^ (-1 - α) := by
          exact mul_le_mul_of_nonneg_right hcos hpow.le
      _ = ε ^ (1 - α) / 2 := by
          rw [div_mul_eq_mul_div, hprod]

theorem connes_levy_integrableOn_Ioi_one {α : ℝ} (hα : 0 < α) :
    IntegrableOn (connesLevyKernel α) (Ioi (1 : ℝ)) volume := by
  have hmaj : IntegrableOn (fun ε : ℝ => 2 * ε ^ (-1 - α)) (Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_of_lt (a := -1 - α) (by linarith) one_pos).const_mul 2
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (connesLevyKernel_continuousOn α).mono (Set.Ioi_subset_Ioi (by norm_num))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ε hε
    have hε0 : (0 : ℝ) < ε := lt_trans one_pos hε
    have hnn := connesLevyKernel_nonneg α hε0.le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hcos : 1 - Real.cos ε ≤ 2 := by
      have := Real.neg_one_le_cos ε
      linarith
    have hpow : (0 : ℝ) < ε ^ (-1 - α) := Real.rpow_pos_of_pos hε0 _
    exact mul_le_mul_of_nonneg_right hcos hpow.le

theorem connes_levy_integrableOn {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    IntegrableOn (connesLevyKernel α) (Ioi (0 : ℝ)) volume := by
  have hu := (connes_levy_integrableOn_Ioc hα2).union (connes_levy_integrableOn_Ioi_one hα0)
  rwa [show Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 from Ioc_union_Ioi_eq_Ioi (by norm_num)] at hu

/-- **The Lévy constant** `C_α = ∫_0^∞ (1 − cos ε) ε^{-1-α} dε`. -/
def connesLevyConstant (α : ℝ) : ℝ := ∫ ε in Ioi (0 : ℝ), connesLevyKernel α ε

theorem connes_levyConstant_pos {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    0 < connesLevyConstant α := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  set c : ℝ := (π ^ (1 + α))⁻¹ with hc
  have hcpos : 0 < c := by
    have : (0 : ℝ) < π ^ (1 + α) := Real.rpow_pos_of_pos hπ _
    positivity
  have hsub : Ioo (π / 2) π ⊆ Ioi (0 : ℝ) := fun x hx => lt_trans (by positivity) hx.1
  have hlow : ∀ x ∈ Ioo (π / 2) π, c ≤ connesLevyKernel α x := by
    intro x hx
    have hx1 : π / 2 < x := hx.1
    have hx2 : x < π := hx.2
    have hx0 : (0 : ℝ) < x := lt_trans (by positivity) hx1
    have hcosnp : Real.cos x ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hx1.le (by linarith)
    have hone : (1 : ℝ) ≤ 1 - Real.cos x := by linarith
    have hxp : x ^ (1 + α) ≤ π ^ (1 + α) :=
      Real.rpow_le_rpow hx0.le hx2.le (by linarith)
    have hxppos : (0 : ℝ) < x ^ (1 + α) := Real.rpow_pos_of_pos hx0 _
    have hπp : (0 : ℝ) < π ^ (1 + α) := Real.rpow_pos_of_pos hπ _
    have hinv : (π ^ (1 + α))⁻¹ ≤ (x ^ (1 + α))⁻¹ := by
      have h1 : (π ^ (1 + α))⁻¹ * (x ^ (1 + α)) ≤ (π ^ (1 + α))⁻¹ * (π ^ (1 + α)) :=
        mul_le_mul_of_nonneg_left hxp (by positivity)
      rw [inv_mul_cancel₀ (ne_of_gt hπp)] at h1
      calc (π ^ (1 + α))⁻¹
          = (π ^ (1 + α))⁻¹ * (x ^ (1 + α)) * (x ^ (1 + α))⁻¹ := by
            field_simp
        _ ≤ 1 * (x ^ (1 + α))⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (x ^ (1 + α))⁻¹ := one_mul _
    have hrw : x ^ (-1 - α) = (x ^ (1 + α))⁻¹ := by
      rw [show (-1 - α : ℝ) = -(1 + α) by ring, Real.rpow_neg hx0.le]
    calc c ≤ (x ^ (1 + α))⁻¹ := hinv
      _ = x ^ (-1 - α) := hrw.symm
      _ = 1 * x ^ (-1 - α) := (one_mul _).symm
      _ ≤ (1 - Real.cos x) * x ^ (-1 - α) :=
          mul_le_mul_of_nonneg_right hone (Real.rpow_nonneg hx0.le _)
  have hIoo : IntegrableOn (connesLevyKernel α) (Ioo (π / 2) π) volume :=
    (connes_levy_integrableOn hα0 hα2).mono_set hsub
  have hge : c * (volume (Ioo (π / 2) π)).toReal
      ≤ ∫ x in Ioo (π / 2) π, connesLevyKernel α x :=
    setIntegral_ge_of_const_le_real measurableSet_Ioo (by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) hlow hIoo
  have hvol : (volume (Ioo (π / 2) π)).toReal = π / 2 := by
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol] at hge
  have hmono : (∫ x in Ioo (π / 2) π, connesLevyKernel α x) ≤ connesLevyConstant α := by
    refine MeasureTheory.setIntegral_mono_set (connes_levy_integrableOn hα0 hα2) ?_
      (Filter.Eventually.of_forall (fun x (hx : x ∈ Ioo (π / 2) π) => hsub hx))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact connesLevyKernel_nonneg α (le_of_lt hx)
  have : 0 < c * (π / 2) := by positivity
  linarith

/-- **The scaling law.**  The kernel integral is homogeneous of degree `α`. -/
theorem connes_levy_scaling {α : ℝ} {t : ℝ} (ht : 0 < t) :
    (∫ ε in Ioi (0 : ℝ), (1 - Real.cos (t * ε)) * ε ^ (-1 - α))
      = connesLevyConstant α * t ^ α := by
  have hpt : ∀ ε ∈ Ioi (0 : ℝ),
      (1 - Real.cos (t * ε)) * ε ^ (-1 - α)
        = t ^ (1 + α) * connesLevyKernel α (t * ε) := by
    intro ε hε
    have hε0 : (0 : ℝ) < ε := hε
    have hsplit : (t * ε) ^ (-1 - α) = t ^ (-1 - α) * ε ^ (-1 - α) :=
      Real.mul_rpow ht.le hε0.le
    have hcomb : t ^ (1 + α) * t ^ (-1 - α) = 1 := by
      rw [← Real.rpow_add ht]
      norm_num
    simp only [connesLevyKernel, hsplit]
    calc (1 - Real.cos (t * ε)) * ε ^ (-1 - α)
        = (t ^ (1 + α) * t ^ (-1 - α)) * ((1 - Real.cos (t * ε)) * ε ^ (-1 - α)) := by
          rw [hcomb, one_mul]
      _ = t ^ (1 + α) * ((1 - Real.cos (t * ε)) * (t ^ (-1 - α) * ε ^ (-1 - α))) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hcv := integral_comp_mul_left_Ioi (connesLevyKernel α) 0 ht
  rw [mul_zero] at hcv
  rw [smul_eq_mul] at hcv
  have hinner : (∫ u in Ioi (0 : ℝ), connesLevyKernel α (t * u))
      = t⁻¹ * connesLevyConstant α := hcv
  rw [hinner, ← mul_assoc]
  have hcomb2 : t ^ (1 + α) * t⁻¹ = t ^ α := by
    rw [show (t⁻¹ : ℝ) = t ^ (-1 : ℝ) by rw [Real.rpow_neg_one], ← Real.rpow_add ht]
    congr 1
    ring
  rw [hcomb2, mul_comm]

end

end GaloisForLFunctions.RHTower
