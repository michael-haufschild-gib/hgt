import GaloisForLFunctions.HTGeometry.OrderOneEnvelope
import Mathlib.Analysis.Complex.RemovableSingularity


/-!
# Order-one envelopes under square roots and removable division

Exponential factors, square roots, and the entire quotient of a function vanishing
at zero by its coordinate remain within the explicit order-one growth envelope.
-/

open Complex Filter Topology Metric Set
namespace GaloisForLFunctions.HTGeometry


theorem orderOneEnvelope_exp_mul (a : ℂ) :
    OrderOneEnvelope (fun z : ℂ => Complex.exp (a * z)) := by
  have hl : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  have hg := (orderOneEnvelope_natCast_cpow_neg (n := 2) (by norm_num)).comp_affine
    (-a / (Real.log 2 : ℂ)) 0
  refine hg.congr fun z => ?_
  change (2 : ℂ) ^ _ = _
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  congr 1
  field_simp
  ring

theorem OrderOneEnvelope.of_sq {f g : ℂ → ℂ} (hf : OrderOneEnvelope f)
    (hgf : ∀ z, g z ^ 2 = f z) : OrderOneEnvelope g := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨C, hC, fun z => ?_⟩
  have hsq : ‖g z‖ ^ 2 ≤ Real.exp (orderOneWeight C z) := by
    rw [← norm_pow, hgf]
    exact hb z
  have hE : 1 ≤ Real.exp (orderOneWeight C z) :=
    Real.one_le_exp (orderOneWeight_nonneg hC.le z)
  by_cases hg : ‖g z‖ ≤ 1
  · exact hg.trans hE
  · have h1 : 1 ≤ ‖g z‖ := le_of_not_ge hg
    nlinarith

theorem OrderOneEnvelope.dslope_zero {f : ℂ → ℂ} (hf : OrderOneEnvelope f)
    (hd : Differentiable ℂ f) (hzero : f 0 = 0) : OrderOneEnvelope (dslope f 0) := by
  have hD : Differentiable ℂ (dslope f 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 (0 : ℂ))).mpr
      hd.differentiableOn
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hD.continuous.continuousOn
  obtain ⟨C, hC, hb⟩ := hf
  obtain ⟨D, hDpos, hDb⟩ := orderOneEnvelope_const (B : ℂ)
  refine ⟨C + D, by linarith, fun z => ?_⟩
  by_cases hz : ‖z‖ ≤ 1
  · have hmem : z ∈ closedBall (0 : ℂ) 1 := by simpa using hz
    have hBabs : B ≤ ‖(B : ℂ)‖ := by simpa using le_abs_self B
    exact (hB z hmem).trans (hBabs.trans ((hDb z).trans
      (Real.exp_le_exp.mpr (orderOneWeight_mono (by linarith : D ≤ C + D) z))))
  · have hid : z * dslope f 0 z = f z := by
      simpa [hzero, smul_eq_mul] using sub_smul_dslope f (0 : ℂ) z
    have hn := congrArg norm hid
    rw [norm_mul] at hn
    have hle : ‖dslope f 0 z‖ ≤ ‖f z‖ := by
      have hz1 : 1 ≤ ‖z‖ := le_of_not_ge hz
      nlinarith [norm_nonneg (dslope f 0 z)]
    exact hle.trans ((hb z).trans
      (Real.exp_le_exp.mpr (orderOneWeight_mono (by linarith : C ≤ C + D) z)))

end GaloisForLFunctions.HTGeometry
