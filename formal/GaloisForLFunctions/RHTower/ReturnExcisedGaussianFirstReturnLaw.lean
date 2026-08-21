import GaloisForLFunctions.RHTower.StaticChoiGaussianFirstReturnLaw
import GaloisForLFunctions.HTGeometry.ReturnExcisedMinimalIncidenceRankLaw

/-!
# Return-excised Gaussian incidence first-return law

A later narrow capture forces a positive Gaussian-time cell of wider capture.  The return-excised
coarea law then forces the occupied-image incidence action above an explicit threshold.  Its
contrapositive converts the exact quenched action estimate sought for ordinary local Hamiltonians
into exclusion of the complete target union throughout a continuous time interval.
-/

open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- **Return-excised incidence action controls first entry.**  The cut removes only the common
initial time cell.  Every later source sheet remains in the Gaussian measure, while the circuit
family enters through its occupied replica incidence span rather than its label count. -/
theorem no_second_capture_of_returnExcised_gaussianIncidenceAction_lt
    {C α : Type*} [Fintype C] [Fintype α]
    (D : (α → ℂ) → (α → ℂ) → ℝ)
    (psi : ℝ → α → ℂ) (target : C → α → ℂ)
    {r : ℕ} (hr : 0 < r)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    {speed epsn epsw T threshold : ℝ}
    (hspeed : 0 < speed) (hTpos : 0 < T)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hT : epsw / speed ≤ T) (hthreshold : 0 < threshold)
    (htriangle : ∀ t u c,
      D (psi t) (target c) ≤ D (psi t) (psi u) + D (psi u) (target c))
    (hLip : ∀ t u, D (psi t) (psi u) ≤ speed * |t - u|)
    (hfidelity : ∀ t c, D (psi t) (target c) ≤ epsw →
      threshold ≤ finitePureStateFidelity (psi t) (target c))
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target (fun y => psi (T * y))
          (Icc (-(epsw / speed / T)) (epsw / speed / T)))
        (psi (T * x)) i)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target (fun y => psi (T * y))
          (Icc (-(epsw / speed / T)) (epsw / speed / T)))
        (psi (T * x)) i‖ ^ 2)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ))
    (haction :
      (returnExcisedReplicaIncidenceNumber r target (fun x => psi (T * x))
          (Icc (-(epsw / speed / T)) (epsw / speed / T)) : ℝ) *
        returnExcisedReplicaIncidenceAction (gaussianReal 0 1) r target
          (fun x => psi (T * x))
          (Icc (-(epsw / speed / T)) (epsw / speed / T)) <
      (gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)) *
        threshold ^ r) ^ 2) :
    ¬ ∃ t ∈ Icc
        (epsw / speed + (epsw - epsn) / speed) T,
      ∃ c, D (psi t) (target c) ≤ epsn := by
  let a := epsw / speed
  let mesh := (epsw - epsn) / speed
  let R : Set ℝ := Icc (-(a / T)) (a / T)
  let state : ℝ → α → ℂ := fun x => psi (T * x)
  let E : Set ℝ := {x | ∃ c, threshold ≤ finitePureStateFidelity (state x) (target c)}
  have hepsw : 0 < epsw := lt_of_le_of_lt hepsn hgap
  have ha : 0 < a := div_pos hepsw hspeed
  have hmesh : 0 < mesh := div_pos (sub_pos.mpr hgap) hspeed
  rintro ⟨t, ht, c, hcap⟩
  let rho := mesh / (4 * T)
  let center := (t - mesh / 4) / T
  let I : Set ℝ := Icc ((t - mesh / 2) / T) (t / T)
  have hrho : 0 < rho := div_pos hmesh (by positivity)
  have hmeshLeA : mesh ≤ a := by
    dsimp [mesh, a]
    exact div_le_div_of_nonneg_right (sub_le_self epsw hepsn) hspeed.le
  have hcenter_nonneg : 0 ≤ center := by
    dsimp [center]
    apply div_nonneg
    · have hta : a + mesh ≤ t := by simpa [a, mesh] using ht.1
      linarith
    · exact hTpos.le
  have hcenter_le : center ≤ 1 := by
    dsimp [center]
    rw [div_le_one hTpos]
    exact (sub_le_self t (by positivity)).trans ht.2
  have hcenter : |center| ≤ 1 := by
    rw [abs_of_nonneg hcenter_nonneg]
    exact hcenter_le
  have hrhoOne : rho ≤ 1 := by
    have haT : a ≤ T := by simpa [a] using hT
    have hmeshT : mesh ≤ T := hmeshLeA.trans haT
    dsimp [rho]
    rw [div_le_one (by positivity : 0 < 4 * T)]
    linarith
  have hI : I = Icc (center - rho) (center + rho) := by
    dsimp [I, center, rho]
    congr 1 <;> field_simp <;> ring
  have hIR : I ⊆ Rᶜ := by
    intro x hx hxR
    have hta : a + mesh ≤ t := by simpa [a, mesh] using ht.1
    have hxlower : (t - mesh / 2) / T ≤ x := by simpa [I] using hx.1
    have hxRupper : x ≤ a / T := by simpa [R] using hxR.2
    rw [div_le_iff₀ hTpos] at hxlower
    rw [le_div_iff₀ hTpos] at hxRupper
    nlinarith
  have hIE : I ⊆ E := by
    intro x hx
    refine ⟨c, hfidelity (T * x) c ?_⟩
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
    have hmove := hLip (T * x) t
    calc
      D (psi (T * x)) (target c) ≤
          D (psi (T * x)) (psi t) + D (psi t) (target c) :=
        htriangle (T * x) t c
      _ ≤ speed * |T * x - t| + epsn := add_le_add hmove hcap
      _ ≤ speed * (mesh / 2) + epsn :=
        add_le_add (mul_le_mul_of_nonneg_left hxt hspeed.le) le_rfl
      _ ≤ epsw := by dsimp [mesh]; field_simp; nlinarith
  have hmuE := gaussianReal_Icc_shifted_lower
    (a := center) (rho := rho) hcenter hrho.le hrhoOne
  rw [← hI] at hmuE
  have hlowerI : gaussianFloorTwo * (mesh / (2 * T)) ≤
      (gaussianReal 0 1).real I := by
    have hnonneg : 0 ≤ 2 * gaussianFloorTwo * rho :=
      mul_nonneg (mul_nonneg (by norm_num) gaussianFloorTwo_pos.le) hrho.le
    have hreal : 2 * gaussianFloorTwo * rho ≤ (gaussianReal 0 1).real I := by
      rw [← ENNReal.toReal_ofReal hnonneg]
      exact ENNReal.toReal_mono (measure_ne_top _ _) hmuE
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
  have hcoarea := (quenchedReplica_returnExcisedMinimalRankCoareaIncidence_bound
    (gaussianReal 0 1) hr target state htarget threshold hthreshold R
      measurableSet_Icc (by simpa [state, R, a] using hmeas)
      (by simpa [state, R, a] using hcoord)).2
  have hthresholdPow : 0 < threshold ^ r := pow_pos hthreshold r
  have hL : 0 ≤ gaussianFloorTwo * (mesh / (2 * T)) :=
    mul_nonneg gaussianFloorTwo_pos.le
      (div_nonneg hmesh.le (by positivity : 0 ≤ 2 * T))
  have hM : 0 ≤ ((gaussianReal 0 1).restrict Rᶜ).real E := measureReal_nonneg
  have hscaled :
      gaussianFloorTwo * (mesh / (2 * T)) * threshold ^ r ≤
        ((gaussianReal 0 1).restrict Rᶜ).real E * threshold ^ r :=
    mul_le_mul_of_nonneg_right hmass hthresholdPow.le
  have hsq :
      (gaussianFloorTwo * (mesh / (2 * T)) * threshold ^ r) ^ 2 ≤
        (((gaussianReal 0 1).restrict Rᶜ).real E * threshold ^ r) ^ 2 := by
    exact (sq_le_sq₀
      (mul_nonneg hL hthresholdPow.le)
      (mul_nonneg hM hthresholdPow.le)).2 hscaled
  have hcontra := hsq.trans hcoarea
  apply (not_lt_of_ge hcontra)
  simpa [state, E, R, a, mesh] using haction

end RHTower
