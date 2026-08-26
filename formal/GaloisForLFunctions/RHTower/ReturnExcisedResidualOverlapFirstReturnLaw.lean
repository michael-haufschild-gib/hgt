import GaloisForLFunctions.RHTower.StaticChoiReturnExcisedGaussianFirstReturnLaw
import GaloisForLFunctions.HTGeometry.ReturnExcisedResidualCoareaLaw
import GaloisForLFunctions.HTGeometry.ReplicaProjectionIncidenceLaw
import GaloisForLFunctions.RHTower.ScalarRecurrenceKrylovReplicaDichotomyLaw

open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A later high-overlap capture forces a positive Gaussian-time cell of
lower-overlap capture. Closed-unit-ball coarea therefore excludes the whole
continuous interval without normalizing return-orthogonal residuals. -/
theorem no_forward_staticChoiOverlapCapture_of_returnExcisedGaussianIncidenceAction_lt
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C]
    (energy : Fin d → ℝ)
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ ≤ 1)
    {r : ℕ} (hr : 0 < r)
    {T returnRadius thetaN thetaW : ℝ}
    (hTpos : 0 < T) (hreturnPos : 0 < returnRadius)
    (hthetaW : 0 < thetaW) (hgap : thetaW < thetaN)
    (hmeshReturn : (thetaN - thetaW) / staticChoiSpeed energy ≤ returnRadius)
    (hreturnT : returnRadius ≤ T)
    (haction :
      (returnExcisedReplicaIncidenceNumber r (fun c => (target c).ofLp)
          (fun x => (staticSpectralChoiVector d (T * x) energy).ofLp)
          (Icc (-(returnRadius / T)) (returnRadius / T)) : ℝ) *
        returnExcisedReplicaIncidenceAction (gaussianReal 0 1) r
          (fun c => (target c).ofLp)
          (fun x => (staticSpectralChoiVector d (T * x) energy).ofLp)
          (Icc (-(returnRadius / T)) (returnRadius / T)) <
      (gaussianFloorTwo *
        (((thetaN - thetaW) / staticChoiSpeed energy) / (2 * T)) *
          (thetaW ^ 2) ^ r) ^ 2) :
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
  have htargetReplica : ∀ c,
      ‖finitePureTensorPowerEuclidean r (target c).ofLp‖ ≤ 1 := by
    intro c
    apply norm_finitePureTensorPowerEuclidean_le_one
    simpa only [WithLp.toLp_ofLp] using htarget c
  have hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r (fun c => (target c).ofLp)
          state R) (state x) i)
      ((gaussianReal 0 1).restrict Rᶜ) := by
    intro i
    exact (continuous_replicaSubspaceCoordinate_comp
      (fun x : ℝ => staticSpectralChoiVector d (T * x) energy)
      (continuous_staticSpectralChoiVector_scaled hd energy T) _ i).aestronglyMeasurable
  have hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r (fun c => (target c).ofLp)
          state R) (state x) i‖ ^ 2)
      ((gaussianReal 0 1).restrict Rᶜ) := by
    intro i
    exact integrable_sq_replicaSubspaceCoordinate_staticSpectralChoiVector
      hd energy T _ i _
  have hcoarea :=
    (quenchedReplica_returnExcisedMinimalRankCoareaIncidence_bound_of_replicaNorm_le_one
      (gaussianReal 0 1) hr (fun c => (target c).ofLp) state htargetReplica
      (thetaW ^ 2) (sq_pos_of_pos hthetaW) R measurableSet_Icc hmeas hcoord).2
  have hthresholdPow : 0 < (thetaW ^ 2) ^ r :=
    pow_pos (sq_pos_of_pos hthetaW) r
  have hL : 0 ≤ gaussianFloorTwo * (mesh / (2 * T)) :=
    mul_nonneg gaussianFloorTwo_pos.le
      (div_nonneg hmesh.le (by positivity : 0 ≤ 2 * T))
  have hM : 0 ≤ ((gaussianReal 0 1).restrict Rᶜ).real E := measureReal_nonneg
  have hscaled :
      gaussianFloorTwo * (mesh / (2 * T)) * (thetaW ^ 2) ^ r ≤
        ((gaussianReal 0 1).restrict Rᶜ).real E * (thetaW ^ 2) ^ r :=
    mul_le_mul_of_nonneg_right hmass hthresholdPow.le
  have hsq :
      (gaussianFloorTwo * (mesh / (2 * T)) * (thetaW ^ 2) ^ r) ^ 2 ≤
        (((gaussianReal 0 1).restrict Rᶜ).real E *
          (thetaW ^ 2) ^ r) ^ 2 := by
    exact (sq_le_sq₀
      (mul_nonneg hL hthresholdPow.le)
      (mul_nonneg hM hthresholdPow.le)).2 hscaled
  have hcontra := hsq.trans hcoarea
  apply (not_lt_of_ge hcontra)
  simpa [state, E, R, mesh, speed, mul_assoc] using haction

/-- Scalar recurrence is charged once; every remaining target is charged
through its unnormalized return-orthogonal residual. Thus one scalar ceiling
and one incidence-normalized residual action exclude the complete target
union continuously. -/
theorem no_forward_staticChoiTargetCapture_of_scalarReturn_and_residualIncidenceAction_lt
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C]
    (energy : Fin d → ℝ)
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    {r : ℕ} (hr : 0 < r)
    {T returnRadius eta thetaN thetaW : ℝ}
    (hTpos : 0 < T) (hreturnPos : 0 < returnRadius)
    (hthetaW : 0 < thetaW) (hgap : thetaW < thetaN)
    (hmeshReturn : (thetaN - thetaW) / staticChoiSpeed energy ≤ returnRadius)
    (hreturnT : returnRadius ≤ T)
    (hscalar : ∀ t ∈ Icc
        (returnRadius + (thetaN - thetaW) / staticChoiSpeed energy) T,
      ‖inner ℂ (staticSpectralChoiVector d t energy)
        (staticSpectralChoiVector d 0 energy)‖ < eta)
    (haction :
      (returnExcisedReplicaIncidenceNumber r
          (fun c => (staticChoiTracelessResidual energy (target c)).ofLp)
          (fun x => (staticSpectralChoiVector d (T * x) energy).ofLp)
          (Icc (-(returnRadius / T)) (returnRadius / T)) : ℝ) *
        returnExcisedReplicaIncidenceAction (gaussianReal 0 1) r
          (fun c => (staticChoiTracelessResidual energy (target c)).ofLp)
          (fun x => (staticSpectralChoiVector d (T * x) energy).ofLp)
          (Icc (-(returnRadius / T)) (returnRadius / T)) <
      (gaussianFloorTwo *
        (((thetaN - thetaW) / staticChoiSpeed energy) / (2 * T)) *
          (thetaW ^ 2) ^ r) ^ 2) :
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
    exact no_forward_staticChoiOverlapCapture_of_returnExcisedGaussianIncidenceAction_lt
      hd energy (fun c => staticChoiTracelessResidual energy (target c))
      (fun c => norm_staticChoiTracelessResidual_le_one hd energy (htarget c))
      hr hTpos hreturnPos hthetaW hgap hmeshReturn hreturnT haction
  rintro ⟨t, ht, c, hcapture⟩
  rcases staticChoiTarget_capture_scalar_or_traceless_budget
      hd t energy (htarget c) (theta := eta + thetaN) (eta := eta) hcapture with
    hreturn | hresidualCapture
  · exact (not_lt_of_ge hreturn) (hscalar t ht)
  · apply hresidual
    refine ⟨t, ht, c, ?_⟩
    simpa only [add_sub_cancel_left] using hresidualCapture

end RHTower
