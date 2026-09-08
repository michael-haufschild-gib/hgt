import GaloisForLFunctions.RHTower.SelbergModularDomainSlices

/-!
# Circular substitution on the truncated modular domain

Shared geometric integration identities extracted from SelbergMaassTraceArea.
These contain no spectral input and apply to ordinary real boundary functions.
-/
open Set Filter Topology MeasureTheory UpperHalfPlane
namespace GaloisForLFunctions.RHTower.SelbergModularArcIntegration
open SelbergMaassTraceStokes SelbergModularDomainSlices
noncomputable section

/-- Reflection folds a continuous boundary integral into its paired half. -/
theorem fold_integral {B : ℝ → ℝ}
    (hB : ContinuousOn B (Icc (-(1 / 2 : ℝ)) (1 / 2))) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2), B x) =
      ∫ x in (0 : ℝ)..(1 / 2), B (-x) + B x := by
  have hleft : IntervalIntegrable B volume (-(1 / 2 : ℝ)) 0 :=
    (hB.mono (by
      intro x hx
      have hxI : x ∈ Icc (-(1 / 2 : ℝ)) 0 := by
        simpa [uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)] using hx
      exact ⟨hxI.1, hxI.2.trans (by norm_num)⟩)).intervalIntegrable
  have hright : IntervalIntegrable B volume 0 (1 / 2) :=
    (hB.mono (by
      intro x hx
      have hxI : x ∈ Icc 0 (1 / 2 : ℝ) := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
      exact ⟨by linarith [hxI.1], hxI.2⟩)).intervalIntegrable
  have hnegCont : ContinuousOn (fun x => B (-x)) (Icc (0 : ℝ) (1 / 2)) :=
    hB.comp continuous_neg.continuousOn (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hneg : IntervalIntegrable (fun x => B (-x)) volume 0 (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hnegCont
  rw [intervalIntegral.integral_add hneg hright,
    intervalIntegral.integral_comp_neg B]
  simp only [neg_zero]
  exact (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm

/-- The circular height has its literal negative-slope derivative. -/
theorem arcHeight_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt arcHeight (-x / arcHeight x) x := by
  have hpos : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_nonneg (x + 1 / 2)]
  have hi : HasDerivAt (fun q : ℝ => 1 - q ^ 2) (-2 * x) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
    have hfun : ((fun _ : ℝ => 1) - id ^ 2) = (fun q : ℝ => 1 - q ^ 2) := rfl
    rw [hfun] at h
    exact h.congr_deriv (by norm_num)
  have hs := hi.sqrt hpos.ne'
  unfold arcHeight
  convert hs using 1
  field_simp [Real.sqrt_ne_zero'.2 hpos]

/-- Exact change of variables between height and the circular boundary. -/
theorem arc_change_of_variables (g : ℝ → ℝ) :
    (∫ y in arcFloor..1, g y) =
      ∫ x in (0 : ℝ)..(1 / 2), (x / arcHeight x) * g (arcHeight x) := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := g) (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
    (f := arcHeight) (f' := fun x => -x / arcHeight x)
    continuous_arcHeight.continuousOn
    (by intro x hx; exact arcHeight_deriv (by simpa using hx))
    (by
      intro x hx
      have hxI : x ∈ Ioo (0 : ℝ) (1 / 2) := by simpa using hx
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hxI.1])
        (arcHeight_pos ⟨by linarith [hxI.1], hxI.2.le⟩).le)
  have hzero : arcHeight 0 = 1 := by norm_num [arcHeight]
  rw [hzero, show arcHeight (1 / 2) = arcFloor from rfl,
    intervalIntegral.integral_symm arcFloor 1] at h
  have he : (∫ x in (0 : ℝ)..(1 / 2), g (arcHeight x) * (-x / arcHeight x)) =
      -(∫ x in (0 : ℝ)..(1 / 2), (x / arcHeight x) * g (arcHeight x)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    ring
  simp only [Function.comp_apply] at h
  rw [he] at h
  exact (neg_inj.mp h).symm

/-- The circular side radius recovers the nonnegative horizontal coordinate. -/
theorem sideRadius_arcHeight {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    sideRadius (arcHeight x) = x := by
  unfold sideRadius
  rw [arcHeight_sq ⟨by linarith [hx.1], hx.2⟩]
  ring_nf
  exact Real.sqrt_sq hx.1

end
end GaloisForLFunctions.RHTower.SelbergModularArcIntegration
