import GaloisForLFunctions.RHTower.StaticChoiSubunitWeightedCrowdingLaw
import GaloisForLFunctions.RHTower.ReturnExcisedResidualOverlapFirstReturnLaw

/-!
# Residual optimal-design first-return law

A preselected determinant design converts the complete unnormalized
return-orthogonal target family into one weighted Gaussian moment. The
result excludes continuous post-return capture without a target union factor.
-/

open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem no_forward_staticChoiOverlapCapture_of_returnExcisedGaussianDesignWeightedCrowding_lt
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C]
    {energy : Fin d → ℝ} (hmax : MaximallyProjectiveEnergy energy)
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ ≤ 1)
    {r : ℕ}
    {T returnRadius thetaN thetaW delta : ℝ}
    (hTpos : 0 < T) (hreturnPos : 0 < returnRadius)
    (hthetaW : 0 < thetaW) (hgap : thetaW < thetaN)
    (hdelta : 0 < delta)
    (hmeshReturn : (thetaN - thetaW) / staticChoiSpeed energy ≤ returnRadius)
    (hreturnT : returnRadius ≤ T)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (hdesign : ∀ (psi : (Fin d × Fin d) → ℂ) (c : C),
      finitePureStateFidelity psi (target c).ofLp ^ r ≤
        (Module.finrank ℂ
          (replicaTargetSpan r (fun j => (target j).ofLp)) : ℝ) *
          ∑ j, w j * finitePureStateFidelity psi (target j).ofLp ^ r)
    (hbudget :
      (Module.finrank ℂ
          (replicaTargetSpan r (fun c => (target c).ofLp)) : ℝ) *
        ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
          ∑ c, w c * directStaticChoiTargetNearActionMass
            (target c) energy r delta +
          Real.exp (-((T * delta) ^ 2) / 2)) <
        gaussianFloorTwo *
          (((thetaN - thetaW) / staticChoiSpeed energy) / (2 * T)) *
            (thetaW ^ 2) ^ r) :
    ¬ ∃ t ∈ Icc
        (returnRadius + (thetaN - thetaW) / staticChoiSpeed energy) T,
      ∃ c, thetaN ≤ ‖inner ℂ
        (staticSpectralChoiVector d t energy) (target c)‖ := by
  let speed := staticChoiSpeed energy
  let mesh := (thetaN - thetaW) / speed
  let R : Set ℝ := Icc (-(returnRadius / T)) (returnRadius / T)
  let state : ℝ → (Fin d × Fin d) → ℂ :=
    fun x => (staticSpectralChoiVector d (T * x) energy).ofLp
  let E : Set ℝ := {x | ∃ c,
    thetaW ^ 2 ≤ finitePureStateFidelity (state x) (target c).ofLp}
  have hspeed : 0 < speed := staticChoiSpeed_pos energy
  have hmesh : 0 < mesh := div_pos (sub_pos.mpr hgap) hspeed
  rintro ⟨t, ht, c, hcap⟩
  let rho := mesh / (4 * T)
  let center := (t - mesh / 4) / T
  let I : Set ℝ := Icc ((t - mesh / 2) / T) (t / T)
  have hrho : 0 < rho := div_pos hmesh (by positivity)
  have hcenter_nonneg : 0 ≤ center := by
    dsimp [center]
    apply div_nonneg
    · have htLower : returnRadius + mesh ≤ t := by simpa [mesh] using ht.1
      nlinarith [hreturnPos, hmesh]
    · exact hTpos.le
  have hcenter_le : center ≤ 1 := by
    dsimp [center]
    rw [div_le_one hTpos]
    exact (sub_le_self t (by positivity)).trans ht.2
  have hcenter : |center| ≤ 1 := by
    rw [abs_of_nonneg hcenter_nonneg]
    exact hcenter_le
  have hmeshT : mesh ≤ T := by
    exact hmeshReturn.trans hreturnT
  have hrhoOne : rho ≤ 1 := by
    dsimp [rho]
    rw [div_le_one (by positivity : 0 < 4 * T)]
    nlinarith
  have hI : I = Icc (center - rho) (center + rho) := by
    dsimp [I, center, rho]
    congr 1 <;> field_simp <;> ring
  have hIR : I ⊆ Rᶜ := by
    intro x hx hxR
    have htLower : returnRadius + mesh ≤ t := by simpa [mesh] using ht.1
    have hxlower : (t - mesh / 2) / T ≤ x := by simpa [I] using hx.1
    have hxRupper : x ≤ returnRadius / T := by simpa [R] using hxR.2
    rw [div_le_iff₀ hTpos] at hxlower
    rw [le_div_iff₀ hTpos] at hxRupper
    nlinarith
  have hIE : I ⊆ E := by
    intro x hx
    refine ⟨c, ?_⟩
    have hxlower : t - mesh / 2 ≤ T * x := by
      have h := hx.1
      rw [div_le_iff₀ hTpos] at h
      simpa [mul_comm] using h
    have hxupper : T * x ≤ t := by
      have h := hx.2
      rw [le_div_iff₀ hTpos] at h
      simpa [mul_comm] using h
    have hxt : |T * x - t| ≤ mesh / 2 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxupper)]
      linarith
    let zt := inner ℂ (staticSpectralChoiVector d t energy) (target c)
    let zx := inner ℂ (staticSpectralChoiVector d (T * x) energy) (target c)
    have hnormDiff : ‖zt‖ - ‖zx‖ ≤ speed * |T * x - t| := by
      calc
        ‖zt‖ - ‖zx‖ ≤ ‖zt - zx‖ := norm_sub_norm_le zt zx
        _ = ‖inner ℂ
            (staticSpectralChoiVector d t energy -
              staticSpectralChoiVector d (T * x) energy) (target c)‖ := by
          rw [inner_sub_left]
        _ ≤ ‖staticSpectralChoiVector d t energy -
              staticSpectralChoiVector d (T * x) energy‖ * ‖target c‖ :=
          norm_inner_le_norm _ _
        _ ≤ ‖staticSpectralChoiVector d t energy -
              staticSpectralChoiVector d (T * x) energy‖ * 1 := by
          gcongr
          exact htarget c
        _ ≤ speed * |t - T * x| := by
          simpa [speed] using
            norm_staticSpectralChoiVector_time_sub_le hd energy t (T * x)
        _ = speed * |T * x - t| := by rw [abs_sub_comm]
    have hmove : ‖zt‖ - ‖zx‖ ≤ speed * (mesh / 2) :=
      hnormDiff.trans (mul_le_mul_of_nonneg_left hxt hspeed.le)
    have hover : thetaW ≤ ‖zx‖ := by
      have hmeshEq : speed * mesh = thetaN - thetaW := by
        dsimp [mesh]
        field_simp
      have hcapzt : thetaN ≤ ‖zt‖ := by simpa [zt] using hcap
      nlinarith
    rw [finitePureStateFidelity_eq_norm_inner_sq]
    rw [norm_inner_symm]
    simp only [state, WithLp.toLp_ofLp]
    exact pow_le_pow_left₀ hthetaW.le hover 2
  have hmuI := gaussianReal_Icc_shifted_lower
    (a := center) (rho := rho) hcenter hrho.le hrhoOne
  rw [← hI] at hmuI
  have hlowerI : gaussianFloorTwo * (mesh / (2 * T)) ≤
      (gaussianReal 0 1).real I := by
    have hnonneg : 0 ≤ 2 * gaussianFloorTwo * rho :=
      mul_nonneg (mul_nonneg (by norm_num) gaussianFloorTwo_pos.le) hrho.le
    have hreal : 2 * gaussianFloorTwo * rho ≤ (gaussianReal 0 1).real I := by
      rw [← ENNReal.toReal_ofReal hnonneg]
      exact ENNReal.toReal_mono (measure_ne_top _ _) hmuI
    convert hreal using 1
    dsimp [rho]
    field_simp
    ring
  have hrestrictI : ((gaussianReal 0 1).restrict Rᶜ).real I =
      (gaussianReal 0 1).real I := by
    rw [measureReal_restrict_apply' measurableSet_Icc.compl]
    rw [inter_eq_left.mpr hIR]
  have hmass : gaussianFloorTwo * (mesh / (2 * T)) ≤
      ((gaussianReal 0 1).restrict Rᶜ).real E := by
    calc
      gaussianFloorTwo * (mesh / (2 * T)) ≤ (gaussianReal 0 1).real I := hlowerI
      _ = ((gaussianReal 0 1).restrict Rᶜ).real I := hrestrictI.symm
      _ ≤ ((gaussianReal 0 1).restrict Rᶜ).real E :=
        measureReal_mono hIE (measure_ne_top _ _)
  let fixedMoment : ℝ :=
    (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
      ∑ c, w c * directStaticChoiTargetNearActionMass
        (target c) energy r delta +
      Real.exp (-((T * delta) ^ 2) / 2)
  have hint : ∀ c, Integrable
      (fun x => finitePureStateFidelity (state x) (target c).ofLp ^ r)
      ((gaussianReal 0 1).restrict Rᶜ) := by
    intro c
    simpa [state] using integrable_staticChoi_fidelity_pow_of_norm_le_one
      hd energy T (target c) (htarget c) r Rᶜ
  have hfull : ∀ c,
      (∫ x, finitePureStateFidelity (state x) (target c).ofLp ^ r
        ∂gaussianReal 0 1) ≤
        (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
          directStaticChoiTargetNearActionMass (target c) energy r delta +
          Real.exp (-((T * delta) ^ 2) / 2) := by
    intro c
    simpa [state] using
      integral_gaussian_staticChoi_fidelity_pow_le_weightedCrowding_of_norm_le_one
        hd hmax (target c) (htarget c) r hTpos hdelta
  have hrestricted : ∀ c,
      (∫ x, finitePureStateFidelity (state x) (target c).ofLp ^ r
        ∂((gaussianReal 0 1).restrict Rᶜ)) ≤
      ∫ x, finitePureStateFidelity (state x) (target c).ofLp ^ r
        ∂gaussianReal 0 1 := by
    intro c
    apply integral_mono_measure Measure.restrict_le_self
    · exact Filter.Eventually.of_forall fun x =>
        pow_nonneg (sq_nonneg _) r
    · simpa [state] using integrable_staticChoi_fidelity_pow_of_norm_le_one
        hd energy T (target c) (htarget c) r Set.univ
  have hweighted :
      (∑ c, w c * ∫ x,
        finitePureStateFidelity (state x) (target c).ofLp ^ r
          ∂((gaussianReal 0 1).restrict Rᶜ)) ≤ fixedMoment := by
    calc
      _ ≤ ∑ c, w c *
          (∫ x, finitePureStateFidelity (state x) (target c).ofLp ^ r
            ∂gaussianReal 0 1) :=
        Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hrestricted c) (hw.1 c)
      _ ≤ ∑ c, w c *
          ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
            directStaticChoiTargetNearActionMass (target c) energy r delta +
            Real.exp (-((T * delta) ^ 2) / 2)) :=
        Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hfull c) (hw.1 c)
      _ = fixedMoment := by
        dsimp [fixedMoment]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, ← Finset.sum_mul, hw.2]
        ring
  have hupper := measure_completeTargetCapture_restrict_le_designMoments
    (gaussianReal 0 1) (fun c => (target c).ofLp) state
      (thetaW ^ 2) (sq_pos_of_pos hthetaW) R w hw hdesign hint
  have hupper' :
      (thetaW ^ 2) ^ r *
          ((gaussianReal 0 1).restrict Rᶜ).real E ≤
        (Module.finrank ℂ
          (replicaTargetSpan r (fun c => (target c).ofLp)) : ℝ) *
          fixedMoment := by
    exact hupper.trans (mul_le_mul_of_nonneg_left hweighted (by positivity))
  have hthresholdPow : 0 < (thetaW ^ 2) ^ r :=
    pow_pos (sq_pos_of_pos hthetaW) r
  have hscaled :
      (thetaW ^ 2) ^ r * (gaussianFloorTwo * (mesh / (2 * T))) ≤
        (thetaW ^ 2) ^ r *
          ((gaussianReal 0 1).restrict Rᶜ).real E :=
    mul_le_mul_of_nonneg_left hmass hthresholdPow.le
  have hcontra := hscaled.trans hupper'
  apply (not_lt_of_ge ?_) hbudget
  simpa [fixedMoment, mesh, speed, mul_assoc, mul_left_comm, mul_comm] using hcontra

theorem staticChoiAnchorResidual_zero_eq_tracelessResidual
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    staticChoiAnchorResidual energy 0 target =
      staticChoiTracelessResidual energy target := by
  rfl

/-- Scalar recurrence is charged once, while a pre-draw design controls all
unnormalized traceless residuals without a circuit union. -/
theorem no_forward_staticChoiTargetCapture_of_scalarReturn_and_residualDesignWeightedCrowding_lt
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C]
    {energy : Fin d → ℝ} (hmax : MaximallyProjectiveEnergy energy)
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    {r : ℕ} {T returnRadius eta thetaN thetaW delta : ℝ}
    (hTpos : 0 < T) (hreturnPos : 0 < returnRadius)
    (hthetaW : 0 < thetaW) (hgap : thetaW < thetaN)
    (hdelta : 0 < delta)
    (hmeshReturn : (thetaN - thetaW) / staticChoiSpeed energy ≤ returnRadius)
    (hreturnT : returnRadius ≤ T)
    (hscalar : ∀ t ∈ Icc
        (returnRadius + (thetaN - thetaW) / staticChoiSpeed energy) T,
      ‖inner ℂ (staticSpectralChoiVector d t energy)
        (staticSpectralChoiVector d 0 energy)‖ < eta)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (hdesign : ∀ (psi : (Fin d × Fin d) → ℂ) (c : C),
      finitePureStateFidelity psi
          (staticChoiTracelessResidual energy (target c)).ofLp ^ r ≤
        (Module.finrank ℂ (replicaTargetSpan r (fun j =>
          (staticChoiTracelessResidual energy (target j)).ofLp)) : ℝ) *
          ∑ j, w j * finitePureStateFidelity psi
            (staticChoiTracelessResidual energy (target j)).ofLp ^ r)
    (hbudget :
      (Module.finrank ℂ (replicaTargetSpan r (fun c =>
          (staticChoiTracelessResidual energy (target c)).ofLp)) : ℝ) *
        ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
          ∑ c, w c * directStaticChoiTargetNearActionMass
            (staticChoiTracelessResidual energy (target c)) energy r delta +
          Real.exp (-((T * delta) ^ 2) / 2)) <
        gaussianFloorTwo *
          (((thetaN - thetaW) / staticChoiSpeed energy) / (2 * T)) *
            (thetaW ^ 2) ^ r) :
    ¬ ∃ t ∈ Icc
        (returnRadius + (thetaN - thetaW) / staticChoiSpeed energy) T,
      ∃ c, eta + thetaN ≤ ‖inner ℂ
        (staticSpectralChoiVector d t energy) (target c)‖ := by
  have hresidual :
      ¬ ∃ t ∈ Icc
          (returnRadius + (thetaN - thetaW) / staticChoiSpeed energy) T,
        ∃ c, thetaN ≤ ‖inner ℂ
          (staticSpectralChoiVector d t energy)
          (staticChoiTracelessResidual energy (target c))‖ := by
    exact no_forward_staticChoiOverlapCapture_of_returnExcisedGaussianDesignWeightedCrowding_lt
      hd hmax (fun c => staticChoiTracelessResidual energy (target c))
      (fun c => norm_staticChoiTracelessResidual_le_one hd energy (htarget c))
      hTpos hreturnPos hthetaW hgap hdelta hmeshReturn hreturnT
      w hw hdesign hbudget
  rintro ⟨t, ht, c, hcapture⟩
  rcases staticChoiTarget_capture_scalar_or_traceless_budget
      hd t energy (htarget c) (theta := eta + thetaN) (eta := eta) hcapture with
    hreturn | hresidualCapture
  · exact (not_lt_of_ge hreturn) (hscalar t ht)
  · apply hresidual
    refine ⟨t, ht, c, ?_⟩
    simpa only [add_sub_cancel_left] using hresidualCapture

end RHTower
