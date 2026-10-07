import GaloisForLFunctions.HTGeometry.SmoothWeightInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The continuous main term in the source Perron formula

The pole `1/(s-1)` on the line `Re s = 2` contributes the integral of
the cutoff over `[1,infinity)`. Fubini is justified by `x^-2 |W(2+it)|`.
This permits a contour shift of the holomorphic source remainder alone.
-/

open Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilSingularArithmetic

/-- Mellin inversion integrated over the positive half-line above one. -/
theorem integral_pole_mul_mellin_smoothWeight {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    Integrable (fun y : ℝ => (1 / ((2 : ℂ) + y * I - 1)) *
      mellin (fun x : ℝ => (smoothWeight N H x : ℂ)) (2 + y * I)) ∧
    (∫ y : ℝ, (1 / ((2 : ℂ) + y * I - 1)) *
      mellin (fun x : ℝ => (smoothWeight N H x : ℂ)) (2 + y * I)) =
      (2 * Real.pi : ℝ) • ∫ x in Ioi (1 : ℝ), (smoothWeight N H x : ℂ) := by
  let W : ℝ → ℂ := fun y => mellin (fun x : ℝ => (smoothWeight N H x : ℂ)) (2 + y * I)
  let f : ℝ → ℝ → ℂ := fun x y => cexp (-((2 : ℂ) + y * I) * Real.log x) * W y
  have hf (x : ℝ) (hx : 1 < x) (y : ℝ) :
      f x y = (x : ℂ) ^ (-((2 : ℂ) + y * I)) * W y := by
    have hx0 : 0 < x := by linarith
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx0.ne'),
      ← Complex.ofReal_log hx0.le]
    dsimp [f]
    congr 2
    ring
  have hW := verticalIntegrable_mellin_smoothWeight hN hH (by norm_num : (0 : ℝ) < 2)
  have hWc : Continuous W := continuous_mellin_smoothWeight_line hH (by norm_num)
  have hmeas : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (Ioi (1 : ℝ))).prod volume) := by
    apply Measurable.aestronglyMeasurable
    have hs : Measurable (fun p : ℝ × ℝ => -((2 : ℂ) + p.2 * I)) := by fun_prop
    exact (Complex.measurable_exp.comp (hs.mul
      (Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_fst)))).mul
      (hWc.measurable.comp measurable_snd)
  have hprod : Integrable (Function.uncurry f)
      ((volume.restrict (Ioi (1 : ℝ))).prod volume) := by
    refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).mul_prod hW.norm).mono' hmeas ?_
    have hae : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi (1 : ℝ))).prod volume, 1 < p.1 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact Eventually.of_forall fun _ => hx
    filter_upwards [hae] with p hp
    rw [Function.uncurry_apply_pair, hf p.1 hp p.2, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hp] : 0 < p.1)]
    simp [W]
  have hpole (y : ℝ) :
      (∫ x in Ioi (1 : ℝ), f x y) = (1 / ((2 : ℂ) + y * I - 1)) * W y := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hf x hx y),
      integral_mul_const, integral_Ioi_cpow_of_lt (by simp) (by norm_num : (0 : ℝ) < 1)]
    simp only [Complex.ofReal_one, one_cpow]
    congr 1
    rw [show -((2 : ℂ) + y * I) + 1 = -((2 : ℂ) + y * I - 1) by ring]
    exact neg_div_neg_eq _ _
  have hinv (x : ℝ) (hx : 1 < x) :
      (∫ y : ℝ, f x y) = (2 * Real.pi : ℝ) • (smoothWeight N H x : ℂ) := by
    have hi := mellinInv_mellin_smoothWeight hN hH
      (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < x)
    rw [mellinInv] at hi
    rw [← hi, smul_smul, mul_one_div_cancel (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]
    exact integral_congr_ae (Eventually.of_forall (hf x hx))
  refine ⟨hprod.integral_prod_right.congr (Eventually.of_forall hpole), ?_⟩
  calc
    _ = ∫ y : ℝ, ∫ x in Ioi (1 : ℝ), f x y := by simp_rw [hpole]; rfl
    _ = ∫ x in Ioi (1 : ℝ), ∫ y : ℝ, f x y := (integral_integral_swap hprod).symm
    _ = ∫ x in Ioi (1 : ℝ), (2 * Real.pi : ℝ) • (smoothWeight N H x : ℂ) :=
      setIntegral_congr_fun measurableSet_Ioi hinv
    _ = _ := integral_smul _ _

/-- The continuous pole main term differs from the integer cutoff by at most two. -/
theorem norm_integral_halfWidth_sub_le {N : ℝ} (hN : 1 ≤ N) :
    ‖(∫ x in Ioi (1 : ℝ), (smoothWeight N (1 / 2) x : ℂ)) - N‖ ≤ 2 := by
  have hc := continuous_smoothWeight_ofReal N (1 / 2)
  have heq : (∫ x in Ioi (1 : ℝ), (smoothWeight N (1 / 2) x : ℂ)) =
      ∫ x in (1 : ℝ)..(N + 1 / 2), (smoothWeight N (1 / 2) x : ℂ) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Ioc_subset_Ioi_self
    intro x hx
    have hNx : N + 1 / 2 ≤ x := by
      have hx1 : 1 < x := hx.1
      have := hx.2
      simp only [mem_Ioc, not_and, not_le] at this
      exact (this hx1).le
    rw [smoothWeight_eq_zero (by norm_num : (0 : ℝ) < 1 / 2) hNx, Complex.ofReal_zero]
  have hhead : (∫ x in (1 : ℝ)..N, (smoothWeight N (1 / 2) x : ℂ)) = (N : ℂ) - 1 := by
    have he := intervalIntegral.integral_congr (μ := volume)
      (f := fun x => (smoothWeight N (1 / 2) x : ℂ))
      (g := fun _ => (1 : ℂ)) (fun x hx => by
        rw [uIcc_of_le hN] at hx
        change (smoothWeight N (1 / 2) x : ℂ) = 1
        rw [smoothWeight_eq_one (by norm_num : (0 : ℝ) < 1 / 2) hx.2, Complex.ofReal_one])
    simpa using he
  have htail : ‖∫ x in N..(N + 1 / 2), (smoothWeight N (1 / 2) x : ℂ)‖ ≤ 1 / 2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := N) (b := N + 1 / 2) (C := 1)
      (f := fun x => (smoothWeight N (1 / 2) x : ℂ)) (fun x _ => by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (smoothWeight_nonneg _ _ _)]
        exact smoothWeight_le_one _ _ _)
    norm_num at hb ⊢
    exact hb
  rw [heq, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 1 N) (hc.intervalIntegrable N (N + 1 / 2)), hhead]
  have hid : (N : ℂ) - 1 + (∫ x in N..(N + 1 / 2), (smoothWeight N (1 / 2) x : ℂ)) - N =
      (∫ x in N..(N + 1 / 2), (smoothWeight N (1 / 2) x : ℂ)) - 1 := by ring
  rw [hid]
  exact (norm_sub_le _ _).trans (by simpa using (show
    ‖∫ x in N..(N + 1 / 2), (smoothWeight N (1 / 2) x : ℂ)‖ + 1 ≤ 2 by linarith))

end RHTower.WeilSingularArithmetic
