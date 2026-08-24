import GaloisForLFunctions.HTGeometry.HardyDiskKernelContinuity

/-!
# Exact Cayley curvature of the rank-one Hardy leakage channel

The Cayley images of the two half-plane zeros at heights `a + ω` and `a - ω`
have exact Blaschke separation `-ω/a`.  Consequently the canonical rank-one
leakage realization has an exact `ω⁻²` Schur-curvature law at every positive
scale below the crossing.  This is the one-zero induction atom for finite-divisor
Toeplitz leakage.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Exact signed Cayley evaluation underlying the leakage norm. -/
theorem blaschkeFactor_cayley {a omega : ℝ} (h0 : 0 < omega) (h1 : omega < a) :
    blaschkeFactor (cayleyPoint (a + omega)) (cayleyPoint (a - omega))
      = ((-(omega / a) : ℝ) : ℂ) := by
  have ha : 0 < a := lt_trans h0 h1
  have hp : (0 : ℝ) < a + omega + 1 := by linarith
  have hm : (0 : ℝ) < a - omega + 1 := by linarith
  rw [blaschkeFactor, cayleyPoint, cayleyPoint]
  rw [map_div₀, Complex.conj_ofReal, Complex.conj_ofReal]
  have hpc : ((a + omega + 1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hp)
  have hmc : ((a - omega + 1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hm)
  have hac : ((a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  field_simp
  push_cast
  ring

/-- Canonical rank-one target realization of the Cayley leakage channel. -/
def cayleyLeakage (a omega : ℝ) (hminus : 0 < a - omega) :
    HardyDisk →L[ℂ] HardyDisk :=
  blaschkeFactor (cayleyPoint (a + omega)) (cayleyPoint (a - omega)) •
    (modelSpace (norm_cayleyPoint_lt_one hminus)).starProjection

theorem cayleyLeakage_apply {a omega : ℝ} (h0 : 0 < omega) (h1 : omega < a)
    (f : HardyDisk) :
    cayleyLeakage a omega (sub_pos.mpr h1) f =
      ((-(omega / a) : ℝ) : ℂ) •
        (modelSpace (norm_cayleyPoint_lt_one (sub_pos.mpr h1))).starProjection f := by
  rw [cayleyLeakage, blaschkeFactor_cayley h0 h1]
  rfl

/-- After division by `ω`, only the moving model-space projection remains. -/
theorem scaled_cayleyLeakage_apply {a omega : ℝ} (h0 : 0 < omega) (h1 : omega < a)
    (f : HardyDisk) :
    (((omega : ℂ)⁻¹) • cayleyLeakage a omega (sub_pos.mpr h1)) f =
      ((-(a⁻¹) : ℝ) : ℂ) •
        (modelSpace (norm_cayleyPoint_lt_one (sub_pos.mpr h1))).starProjection f := by
  rw [smul_apply, cayleyLeakage_apply h0 h1]
  rw [smul_smul]
  congr 1
  push_cast
  field_simp [ne_of_gt h0, ne_of_gt (lt_trans h0 h1)]

theorem cayleyLeakage_norm_sq {a omega : ℝ} (h0 : 0 < omega) (h1 : omega < a)
    (f : HardyDisk) :
    ‖cayleyLeakage a omega (sub_pos.mpr h1) f‖ ^ 2 =
      (omega / a) ^ 2 *
        ‖(modelSpace (norm_cayleyPoint_lt_one (sub_pos.mpr h1))).starProjection f‖ ^ 2 := by
  rw [cayleyLeakage_apply h0 h1, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos h0 (lt_trans h0 h1))]
  ring

/-- Exact second-order Schur defect for one displaced half-plane zero. -/
theorem scaled_hardyLeakage_cayley_curvature {a omega : ℝ}
    (h0 : 0 < omega) (h1 : omega < a) (f : HardyDisk) :
    (‖f‖ ^ 2 -
        ‖(ContinuousLinearMap.adjoint
          (blaschkeMul (norm_cayleyPoint_lt_one (sub_pos.mpr h1))))
          (blaschkeMul (norm_cayleyPoint_lt_one (by linarith : 0 < a + omega)) f)‖ ^ 2) /
        omega ^ 2 =
      (a⁻¹) ^ 2 *
        ‖(modelSpace (norm_cayleyPoint_lt_one (sub_pos.mpr h1))).starProjection f‖ ^ 2 := by
  rw [hardyLeakage_sq, norm_blaschkeFactor_cayley h0 h1]
  have ha : a ≠ 0 := ne_of_gt (lt_trans h0 h1)
  field_simp

/-! ## Operator-norm infinitesimal limit -/

/-- Globally positive depth path agreeing with `a - ω` near zero. -/
def safeCayleyDepth (a omega : ℝ) : ℝ := max (a - omega) (a / 2)

theorem safeCayleyDepth_pos {a : ℝ} (ha : 0 < a) (omega : ℝ) :
    0 < safeCayleyDepth a omega :=
  lt_of_lt_of_le (half_pos ha) (le_max_right _ _)

theorem safeCayleyDepth_eq_sub {a omega : ℝ} (h : omega < a / 2) :
    safeCayleyDepth a omega = a - omega := by
  rw [safeCayleyDepth, max_eq_left]
  linarith

/-- Moving one-zero model-space projection, extended harmlessly away from the endpoint. -/
def cayleyModelProjection (a omega : ℝ) (ha : 0 < a) :
    HardyDisk →L[ℂ] HardyDisk :=
  (modelSpace (norm_cayleyPoint_lt_one (safeCayleyDepth_pos ha omega))).starProjection

theorem tendsto_cayleyModelProjection_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun omega : ℝ => cayleyModelProjection a omega ha)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (modelSpace (norm_cayleyPoint_lt_one ha)).starProjection) := by
  have hdepth : Tendsto (fun omega : ℝ => safeCayleyDepth a omega)
      (nhdsWithin 0 (Ioi 0)) (𝓝 a) := by
    have hc : ContinuousAt (fun omega : ℝ => safeCayleyDepth a omega) 0 := by
      change ContinuousAt (fun omega : ℝ => max (a - omega) (a / 2)) 0
      fun_prop
    have hv : Tendsto (fun omega : ℝ => safeCayleyDepth a omega)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (safeCayleyDepth a 0)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    convert hv using 1
    rw [safeCayleyDepth, sub_zero, max_eq_left] <;> linarith
  have hcayley : Tendsto (fun omega : ℝ => cayleyPoint (safeCayleyDepth a omega))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (cayleyPoint a)) := by
    have hc : ContinuousAt cayleyPoint a := by
      change ContinuousAt
        (fun y : ℝ => ((y - 1 : ℝ) : ℂ) / ((y + 1 : ℝ) : ℂ)) a
      have hnum : ContinuousAt (fun y : ℝ => ((y - 1 : ℝ) : ℂ)) a :=
        Complex.continuous_ofReal.continuousAt.comp
          (continuousAt_id.sub continuousAt_const)
      have hden : ContinuousAt (fun y : ℝ => ((y + 1 : ℝ) : ℂ)) a :=
        Complex.continuous_ofReal.continuousAt.comp
          (continuousAt_id.add continuousAt_const)
      exact hnum.div hden (Complex.ofReal_ne_zero.mpr (by linarith))
    exact hc.tendsto.comp hdepth
  exact tendsto_modelSpace_starProjection
    (fun omega : ℝ => cayleyPoint (safeCayleyDepth a omega))
    (fun omega => norm_cayleyPoint_lt_one (safeCayleyDepth_pos ha omega))
    (norm_cayleyPoint_lt_one ha) hcayley

/-- Totalized normalized rank-one leakage family.  On `0 < ω < a/2` it is
literally `ω⁻¹ Lω`; the safe extension only supplies values away from the germ. -/
def scaledCayleyLeakageFamily (a omega : ℝ) (ha : 0 < a) :
    HardyDisk →L[ℂ] HardyDisk :=
  ((-(a⁻¹) : ℝ) : ℂ) • cayleyModelProjection a omega ha

/-- Infinitesimal rank-one leakage operator at depth `a`. -/
def infinitesimalCayleyLeakage (a : ℝ) (ha : 0 < a) :
    HardyDisk →L[ℂ] HardyDisk :=
  ((-(a⁻¹) : ℝ) : ℂ) •
    (modelSpace (norm_cayleyPoint_lt_one ha)).starProjection

/-- On a deleted right neighborhood, totalized family is literal normalized
leakage of the shifted Blaschke quotient. -/
theorem scaledCayleyLeakageFamily_eq_normalized_leakage
    {a omega : ℝ} (ha : 0 < a) (h0 : 0 < omega) (hhalf : omega < a / 2) :
    scaledCayleyLeakageFamily a omega ha =
      ((omega : ℂ)⁻¹) • cayleyLeakage a omega
        (sub_pos.mpr (lt_trans hhalf (half_lt_self ha))) := by
  have h1 : omega < a := lt_trans hhalf (half_lt_self ha)
  apply ContinuousLinearMap.ext
  intro f
  rw [scaledCayleyLeakageFamily, cayleyModelProjection, smul_apply,
    scaled_cayleyLeakage_apply h0 h1]
  simp only [safeCayleyDepth_eq_sub hhalf]

/-- The normalized leakage has an unconditional operator-norm limit. -/
theorem tendsto_scaledCayleyLeakageFamily_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (scaledCayleyLeakageFamily a · ha)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (infinitesimalCayleyLeakage a ha)) := by
  exact (tendsto_cayleyModelProjection_zero ha).const_smul
    (((-(a⁻¹) : ℝ) : ℂ))

end GaloisForLFunctions.HTGeometry
