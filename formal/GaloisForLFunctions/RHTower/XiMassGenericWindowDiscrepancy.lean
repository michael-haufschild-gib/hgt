import GaloisForLFunctions.RHTower.XiMassWindowDiscrepancyTail

/-!
# The window discrepancy estimate for an arbitrary exterior profile

The `(19.3)` window estimate uses nothing about the mass profile beyond one envelope: the profile
and its height derivative are at most `D·e^{-h/2}e^{-a√(h²−u²)}` on the window.  Stating it that way
makes it available to every modified receiver — in particular to the caustic-null jet, whose
envelope carries the extra power `u^{-(n+1)/2}` inside the constant `D`.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- The pointwise window bound for any profile with the exterior envelope. -/
theorem window_pointwise_bound_generic {a u H h CE cE D : ℝ} {X : ℂ}
    (ha : 1 / 2 < a) (hu : 0 < u) (hHu : u < H) (hH0 : 0 ≤ H)
    (hCE : 0 ≤ CE) (hcE : 0 ≤ cE) (hD : 0 ≤ D) (hHh : H ≤ h)
    (hEh : |xiMassThetaLogDiscrepancy h|
      ≤ CE * Real.exp h * Real.exp (-(cE * h ^ ((1 : ℝ) / 10))))
    (hX : ‖X‖ ≤ D * (Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))) :
    ‖((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * X‖
      ≤ CE * D * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))
          * Real.exp (-(cE * H ^ ((1 : ℝ) / 10)))
        * Real.exp (-((a - 1 / 2) * (h - H))) := by
  have hEnorm : ‖((xiMassThetaLogDiscrepancy h : ℝ) : ℂ)‖ = |xiMassThetaLogDiscrepancy h| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hcoef : (0 : ℝ) ≤ CE * D := mul_nonneg hCE hD
  rw [norm_mul, hEnorm]
  have hprod : |xiMassThetaLogDiscrepancy h| * ‖X‖
      ≤ (CE * Real.exp h * Real.exp (-(cE * h ^ ((1 : ℝ) / 10))))
        * (D * (Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))) := by
    refine mul_le_mul hEh hX (norm_nonneg _) ?_
    positivity
  refine hprod.trans ?_
  have hcollapse : (CE * Real.exp h * Real.exp (-(cE * h ^ ((1 : ℝ) / 10))))
      * (D * (Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))))
      = CE * D * Real.exp (h / 2 - a * Real.sqrt (h ^ 2 - u ^ 2))
        * Real.exp (-(cE * h ^ ((1 : ℝ) / 10))) := by
    rw [show Real.exp (h / 2 - a * Real.sqrt (h ^ 2 - u ^ 2))
        = Real.exp h * Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) from by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring]
    ring
  rw [hcollapse]
  have haction : Real.exp (h / 2 - a * Real.sqrt (h ^ 2 - u ^ 2))
      ≤ Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))
        * Real.exp (-((a - 1 / 2) * (h - H))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hstep2 := xiMassExteriorAction_le ha hu hHu hHh
    linarith
  have hpow : Real.exp (-(cE * h ^ ((1 : ℝ) / 10)))
      ≤ Real.exp (-(cE * H ^ ((1 : ℝ) / 10))) := by
    refine Real.exp_le_exp.2 ?_
    have hmono : H ^ ((1 : ℝ) / 10) ≤ h ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow hH0 hHh (by norm_num)
    nlinarith [hmono]
  have hfirst : CE * D * Real.exp (h / 2 - a * Real.sqrt (h ^ 2 - u ^ 2))
      ≤ CE * D * (Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))
        * Real.exp (-((a - 1 / 2) * (h - H)))) :=
    mul_le_mul_of_nonneg_left haction hcoef
  have hprod2 := mul_le_mul hfirst hpow (Real.exp_nonneg _) (by positivity)
  refine hprod2.trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 800000 in
/-- **(19.3), for an arbitrary exterior profile.**  The exterior decay of the action makes the bound
independent of the window width. -/
theorem norm_primeLogWindow_generic_quadratureDefect_le {G G' : ℝ → ℂ}
    {a u H T CE cE D : ℝ}
    (ha : 1 / 2 < a) (hu : 0 < u) (hHu : u < H) (hH0 : 0 ≤ H) (hHT : H ≤ T)
    (hCE : 0 ≤ CE) (hcE : 0 ≤ cE) (hD : 0 ≤ D)
    (hE : ∀ h : ℝ, H ≤ h → h ≤ T →
      |xiMassThetaLogDiscrepancy h| ≤ CE * Real.exp h * Real.exp (-(cE * h ^ ((1 : ℝ) / 10))))
    (henv : ∀ h : ℝ, H ≤ h → h ≤ T →
      ‖G h‖ ≤ D * (Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))))
    (henv' : ∀ h : ℝ, H ≤ h → h ≤ T →
      ‖G' h‖ ≤ D * (Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))))
    (hG : ∀ x ∈ Set.Icc H T, HasDerivAt G (G' x) x)
    (hG'int : IntervalIntegrable G' volume H T) :
    ‖(∑ p ∈ primeLogWindow H T, ((Real.log p : ℝ) : ℂ) * G (Real.log p))
        - ∫ h in H..T, G h * ((Real.exp h : ℝ) : ℂ)‖
      ≤ (2 + 1 / (a - 1 / 2)) * (CE * D
          * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))
          * Real.exp (-(cE * H ^ ((1 : ℝ) / 10)))) := by
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  set B : ℝ := CE * D * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))
    * Real.exp (-(cE * H ^ ((1 : ℝ) / 10))) with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  rw [primeLogWindow_quadrature_eq hHT hG hG'int]
  have hterm : ∀ h : ℝ, H ≤ h → h ≤ T →
      ‖((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * G h‖
        ≤ B * Real.exp (-((a - 1 / 2) * (h - H))) := by
    intro h hHh hhT
    rw [hB]
    exact window_pointwise_bound_generic ha hu hHu hH0 hCE hcE hD hHh (hE h hHh hhT)
      (henv h hHh hhT)
  have htermD : ∀ h : ℝ, H ≤ h → h ≤ T →
      ‖((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * G' h‖
        ≤ B * Real.exp (-((a - 1 / 2) * (h - H))) := by
    intro h hHh hhT
    rw [hB]
    exact window_pointwise_bound_generic ha hu hHu hH0 hCE hcE hD hHh (hE h hHh hhT)
      (henv' h hHh hhT)
  have hintegrable : IntervalIntegrable
      (fun h : ℝ => ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * G' h) volume H T :=
    intervalIntegrable_discrepancy_mul hHT hG'int
  have hintbound : ‖∫ h in H..T, ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * G' h‖
      ≤ B / (a - 1 / 2) := by
    refine (intervalIntegral.norm_integral_le_integral_norm hHT).trans ?_
    have hmono : (∫ h in H..T, ‖((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * G' h‖)
        ≤ ∫ h in H..T, B * Real.exp (-((a - 1 / 2) * (h - H))) := by
      refine intervalIntegral.integral_mono_on hHT hintegrable.norm
        ((by fun_prop : Continuous fun h : ℝ =>
          B * Real.exp (-((a - 1 / 2) * (h - H)))).intervalIntegrable H T) ?_
      intro x hx
      exact htermD x hx.1 hx.2
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hexpint := integral_exp_neg_shift_le (δ := a - 1 / 2) (b := H) (c := H) (e := T) hδ
    have hzero : Real.exp (-((a - 1 / 2) * (H - H))) / (a - 1 / 2) = 1 / (a - 1 / 2) := by
      norm_num
    rw [hzero] at hexpint
    have hfin := mul_le_mul_of_nonneg_left hexpint hBnn
    rw [mul_one_div] at hfin
    exact hfin
  have h1 : ‖((xiMassThetaLogDiscrepancy T : ℝ) : ℂ) * G T‖ ≤ B := by
    refine (hterm T hHT le_rfl).trans ?_
    have hle : Real.exp (-((a - 1 / 2) * (T - H))) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : (0 : ℝ) ≤ (a - 1 / 2) * (T - H) := by
        apply mul_nonneg hδ.le
        linarith
      linarith
    nlinarith [hle, hBnn]
  have h2 : ‖((xiMassThetaLogDiscrepancy H : ℝ) : ℂ) * G H‖ ≤ B := by
    refine (hterm H le_rfl hHT).trans ?_
    have hzero : Real.exp (-((a - 1 / 2) * (H - H))) = 1 := by norm_num
    rw [hzero, mul_one]
  have hsplit : ‖((xiMassThetaLogDiscrepancy T : ℝ) : ℂ) * G T
      - ((xiMassThetaLogDiscrepancy H : ℝ) : ℂ) * G H
      - ∫ h in H..T, ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * G' h‖
      ≤ B + B + B / (a - 1 / 2) := by
    refine (norm_sub_le _ _).trans ?_
    have hpair := norm_sub_le (((xiMassThetaLogDiscrepancy T : ℝ) : ℂ) * G T)
      (((xiMassThetaLogDiscrepancy H : ℝ) : ℂ) * G H)
    linarith [hpair, h1, h2, hintbound]
  refine hsplit.trans (le_of_eq ?_)
  field_simp
  ring

end

end RHTower
