import GaloisForLFunctions.RHTower.StaticChoiReturnExcisedGaussianFirstReturnLaw
import GaloisForLFunctions.RHTower.UnitaryReplicaOptimalDesignTransportLaw
import GaloisForLFunctions.HTGeometry.PolynomialCircuitReplicaHilbertLaw

/-!
# Return-excised first entry for complete continuous circuit classes

Return-excised replica coarea does not require a finite endpoint dictionary.
The complete target union is projected into its occupied replica span before
integration, so target type may be finite, countable, or continuous without a
selector, compactness premise, discretization, or union bound.

The arbitrary-target first-entry law is joined here to the polynomial Hilbert
law for continuous two-qubit circuits.  After any common unitary coordinate
transport—including conjugation into a Hamiltonian eigenbasis—the
return-excised incidence carrier of every exact-`s` circuit Choi endpoint has
rank at most

`(n*n)^s * (r*s+1)^(16*s)`.

Thus continuous gate cardinality is absent from the growing-replica first
entry problem.  Remaining quantitative input is the return-excised incidence
action itself.
-/

open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Arbitrary-target strengthening: no finiteness, compactness, countability,
or measurable selector is needed. -/
theorem quenchedReplica_returnExcisedMinimalIncidence_bound_arbitraryTarget
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i) (μ.restrict returnSetᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i‖ ^ 2) (μ.restrict returnSetᶜ)) :
    (((μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
        threshold ^ r) ^ 2) ≤
      (returnExcisedReplicaIncidenceNumber r target state returnSet : ℝ) *
        returnExcisedReplicaMinimalIncidenceAction
          μ r target state returnSet := by
  let U := returnExcisedReplicaIncidenceSpan r target state returnSet
  let a : X → Fin (Module.finrank ℂ U) → ℂ :=
    fun x i => replicaSubspaceCoordinate r U (state x) i
  let E : Set X := {x | ∃ c,
    threshold ≤ finitePureStateFidelity (state x) (target c)}
  have hcapture : E ∩ returnSetᶜ ⊆
      {x | threshold ^ r ≤ finiteCoordinateEnergy a x} := by
    intro x hx
    have htargetNorm : ∀ c,
        ‖finitePureTensorPowerEuclidean r (target c)‖ ≤ 1 := by
      intro c
      rw [norm_finitePureTensorPowerEuclidean_eq_one r
        (target c) (htarget c)]
    have hproj := completePureStateTargetCapture_subset_replicaProjectionMass
      hr target state htargetNorm threshold hthreshold.le hx.1
    change threshold ^ r ≤ replicaTargetProjectionMass r target (state x) at hproj
    have heq := replicaTargetProjectionMass_eq_incidenceProjectionMass_offReturn
      r target state returnSet hx.2
    rw [heq, replicaSubspaceProjectionMass_eq_finiteCoordinateEnergy] at hproj
    simpa [finiteCoordinateEnergy, a, U] using hproj
  simpa [E, a, U, returnExcisedReplicaIncidenceNumber,
    returnExcisedReplicaMinimalIncidenceAction, Fintype.card_fin] using
    returnExcisedFiniteCoordinateIncidence_bound
      μ E returnSet hreturn a (threshold ^ r) (pow_pos hthreshold r)
        hcapture hmeas hcoord

theorem quenchedReplica_returnExcisedMinimalRankCoareaIncidence_bound_arbitraryTarget
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i) (μ.restrict returnSetᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i‖ ^ 2) (μ.restrict returnSetᶜ)) :
    (((μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
        threshold ^ r) ^ 2 ≤
      (returnExcisedReplicaIncidenceNumber r target state returnSet : ℝ) *
        returnExcisedReplicaIncidenceAction
          μ r target state returnSet) := by
  rw [← returnExcisedReplicaMinimalIncidenceAction_eq_targetAction
      μ r target state returnSet hreturn]
  exact quenchedReplica_returnExcisedMinimalIncidence_bound_arbitraryTarget
    μ hr target state htarget threshold hthreshold returnSet hreturn
      hmeas hcoord

theorem returnExcisedReplicaIncidenceNumber_le_targetSpan_finrank_arbitraryTarget
    {X C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) :
    returnExcisedReplicaIncidenceNumber r target state returnSet ≤
      Module.finrank ℂ (replicaTargetSpan r target) := by
  unfold returnExcisedReplicaIncidenceNumber
  exact Submodule.finrank_mono
    (returnExcisedReplicaIncidenceSpan_le_targetSpan
      r target state returnSet)

end GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **Return-excised incidence action controls first entry.**  The cut removes only the common
initial time cell.  Every later source sheet remains in the Gaussian measure, while the circuit
family enters through its occupied replica incidence span rather than its label count. -/
theorem no_second_capture_of_returnExcised_gaussianIncidenceAction_lt_arbitraryTarget
    {C α : Type*} [Fintype α]
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
  have hcoarea := (quenchedReplica_returnExcisedMinimalRankCoareaIncidence_bound_arbitraryTarget
    (gaussianReal 0 1) hr target state htarget threshold hthreshold R
      measurableSet_Icc (by simpa [state, R, a] using hmeas)
      (by simpa [state, R, a] using hcoord))
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

namespace GaloisForLFunctions.HTGeometry

/-- Return removal can only decrease occupied rank, so the complete continuous
two-qubit Choi image retains the same cardinality-free polynomial bound in the
incidence carrier used by first-entry coarea. -/
theorem returnExcisedReplicaIncidenceNumber_twoQubitCircuitChoi_le
    {X C : Type*} {n s : ℕ}
    (pos : C → TwoQubitCircuit.twoQubitCircuitArchitectureIndex n s)
    (G : C → Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ c k, TwoQubitCircuit.IsTwoQubitGate
      (pos c k).1 (pos c k).2 (G c k))
    (r : ℕ)
    (state : X → ((Fin n → Bool) × (Fin n → Bool)) → ℂ)
    (returnSet : Set X) :
    returnExcisedReplicaIncidenceNumber r (fun c p =>
        (List.ofFn (G c)).prod p.1 p.2 /
          Real.sqrt (Fintype.card (Fin n → Bool)))
        state returnSet ≤
      (n * n) ^ s * (r * s + 1) ^ (s * 16) := by
  let target : C → ((Fin n → Bool) × (Fin n → Bool)) → ℂ :=
    fun c p => (List.ofFn (G c)).prod p.1 p.2 /
      Real.sqrt (Fintype.card (Fin n → Bool))
  have hcarrier : returnExcisedReplicaIncidenceNumber r target state returnSet ≤
      Module.finrank ℂ (replicaTargetSpan r target) :=
    returnExcisedReplicaIncidenceNumber_le_targetSpan_finrank_arbitraryTarget
      r target state returnSet
  have himage : Module.finrank ℂ (replicaTargetSpan r target) ≤
      (n * n) ^ s * (r * s + 1) ^ (s * 16) := by
    simpa only [target] using
      (TwoQubitCircuit.finrank_replicaTargetSpan_twoQubitCircuitChoi_complete_le
        pos G hG r)
  exact hcarrier.trans himage

/-- The same complete-continuum incidence bound after an arbitrary common
unitary coordinate transport, including transport to a Hamiltonian eigenbasis. -/
theorem returnExcisedReplicaIncidenceNumber_unitaryTransport_twoQubitCircuitChoi_le
    {X C : Type*} {n s : ℕ}
    (pos : C → TwoQubitCircuit.twoQubitCircuitArchitectureIndex n s)
    (G : C → Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ c k, TwoQubitCircuit.IsTwoQubitGate
      (pos c k).1 (pos c k).2 (G c k))
    (r : ℕ)
    (U : Matrix.unitaryGroup
      ((Fin n → Bool) × (Fin n → Bool)) ℂ)
    (state : X → ((Fin n → Bool) × (Fin n → Bool)) → ℂ)
    (returnSet : Set X) :
    returnExcisedReplicaIncidenceNumber r
        (RHTower.unitaryTransportTarget U (fun c p =>
          (List.ofFn (G c)).prod p.1 p.2 /
            Real.sqrt (Fintype.card (Fin n → Bool))))
        state returnSet ≤
      (n * n) ^ s * (r * s + 1) ^ (s * 16) := by
  let target : C → ((Fin n → Bool) × (Fin n → Bool)) → ℂ :=
    fun c p => (List.ofFn (G c)).prod p.1 p.2 /
      Real.sqrt (Fintype.card (Fin n → Bool))
  have hcarrier : returnExcisedReplicaIncidenceNumber r
      (RHTower.unitaryTransportTarget U target) state returnSet ≤
      Module.finrank ℂ
        (replicaTargetSpan r (RHTower.unitaryTransportTarget U target)) :=
    returnExcisedReplicaIncidenceNumber_le_targetSpan_finrank_arbitraryTarget
      r (RHTower.unitaryTransportTarget U target) state returnSet
  have htransport : Module.finrank ℂ
        (replicaTargetSpan r (RHTower.unitaryTransportTarget U target)) =
      Module.finrank ℂ (replicaTargetSpan r target) :=
    RHTower.finrank_replicaTargetSpan_unitaryTransportTarget r U target
  have himage : Module.finrank ℂ (replicaTargetSpan r target) ≤
      (n * n) ^ s * (r * s + 1) ^ (s * 16) := by
    simpa only [target] using
      (TwoQubitCircuit.finrank_replicaTargetSpan_twoQubitCircuitChoi_complete_le
        pos G hG r)
  exact hcarrier.trans (htransport.le.trans himage)

end GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **Static Choi first-return law from the exact return-excised incidence action.**  For every
target family of arbitrary cardinality, a bound on the occupied-image action below the displayed threshold excludes
all later narrow captures through `T`.  Continuity, measurability, and integrability are automatic;
the action estimate is the only remaining scientific input. -/
theorem no_forward_pureChoiCircuitReturn_of_returnExcisedGaussianIncidenceAction_lt_arbitraryTarget
    {d : ℕ} (hd : 0 < d)
    {C : Type*}
    (energy : Fin d → ℝ)
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    {r : ℕ} (hr : 0 < r)
    {T epsn epsw : ℝ}
    (hTpos : 0 < T) (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hepswOne : epsw < 1)
    (hT : epsw / staticChoiSpeed energy ≤ T)
    (haction :
      (returnExcisedReplicaIncidenceNumber r (fun c => (target c).ofLp)
          (fun x => (staticSpectralChoiVector d (T * x) energy).ofLp)
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T)) : ℝ) *
        returnExcisedReplicaIncidenceAction (gaussianReal 0 1) r
          (fun c => (target c).ofLp)
          (fun x => (staticSpectralChoiVector d (T * x) energy).ofLp)
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T)) <
      (gaussianFloorTwo *
        ((epsw - epsn) / staticChoiSpeed energy / (2 * T)) *
          (1 - epsw ^ 2) ^ r) ^ 2) :
    ¬ ∃ t ∈ Icc
        (epsw / staticChoiSpeed energy +
          (epsw - epsn) / staticChoiSpeed energy) T,
      ∃ c, pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (target c) ≤ epsn := by
  have hepsw : 0 ≤ epsw := hepsn.trans (le_of_lt hgap)
  have htargetInner : ∀ c,
      finiteComplexInner (target c).ofLp (target c).ofLp = 1 := by
    intro c
    rw [finiteComplexInner_eq_inner]
    simp only [WithLp.toLp_ofLp]
    rw [inner_self_eq_norm_sq_to_K, htarget c]
    norm_num
  have hthreshold : 0 < 1 - epsw ^ 2 := by
    nlinarith [sq_nonneg epsw]
  have htriangle : ∀ t u c,
      pureStateTraceDistance
          (WithLp.toLp 2 (staticSpectralChoiVector d t energy).ofLp :
            EuclideanSpace ℂ (Fin d × Fin d))
          (WithLp.toLp 2 (target c).ofLp) ≤
        pureStateTraceDistance
            (WithLp.toLp 2 (staticSpectralChoiVector d t energy).ofLp :
              EuclideanSpace ℂ (Fin d × Fin d))
            (WithLp.toLp 2 (staticSpectralChoiVector d u energy).ofLp) +
          pureStateTraceDistance
            (WithLp.toLp 2 (staticSpectralChoiVector d u energy).ofLp :
              EuclideanSpace ℂ (Fin d × Fin d))
            (WithLp.toLp 2 (target c).ofLp) := by
    intro t u c
    simpa only [WithLp.toLp_ofLp] using
      pureStateTraceDistance_triangle
        (staticSpectralChoiVector d t energy)
        (staticSpectralChoiVector d u energy)
        (target c)
        (staticSpectralChoiVector_norm hd t energy)
        (staticSpectralChoiVector_norm hd u energy)
        (htarget c)
  have hLip : ∀ t u,
      pureStateTraceDistance
          (WithLp.toLp 2 (staticSpectralChoiVector d t energy).ofLp :
            EuclideanSpace ℂ (Fin d × Fin d))
          (WithLp.toLp 2 (staticSpectralChoiVector d u energy).ofLp) ≤
        staticChoiSpeed energy * |t - u| := by
    intro t u
    simpa only [WithLp.toLp_ofLp] using
      pureStateTraceDistance_staticSpectralChoiVector_time_le hd energy t u
  have hfidelity : ∀ t c,
      pureStateTraceDistance
          (WithLp.toLp 2 (staticSpectralChoiVector d t energy).ofLp :
            EuclideanSpace ℂ (Fin d × Fin d))
          (WithLp.toLp 2 (target c).ofLp) ≤ epsw →
        1 - epsw ^ 2 ≤ finitePureStateFidelity
          (staticSpectralChoiVector d t energy).ofLp (target c).ofLp := by
    intro t c hdist
    rw [finitePureStateFidelity_eq_norm_inner_sq]
    simp only [WithLp.toLp_ofLp]
    rw [norm_inner_symm]
    have hsq := sq_pureStateTraceDistance
      (staticSpectralChoiVector d t energy) (target c)
      (by rw [staticSpectralChoiVector_norm hd])
      (by rw [htarget c])
    have hdistSq : pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (target c) ^ 2 ≤ epsw ^ 2 :=
      (sq_le_sq₀ (pureStateTraceDistance_nonneg _ _) hepsw).2 hdist
    nlinarith
  have hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r (fun c => (target c).ofLp)
          (fun y => (staticSpectralChoiVector d (T * y) energy).ofLp)
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T)))
        (staticSpectralChoiVector d (T * x) energy).ofLp i)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / staticChoiSpeed energy / T))
          (epsw / staticChoiSpeed energy / T))ᶜ) := by
    intro i
    exact (continuous_replicaSubspaceCoordinate_comp
      (fun x : ℝ => staticSpectralChoiVector d (T * x) energy)
      (continuous_staticSpectralChoiVector_scaled hd energy T) _ i).aestronglyMeasurable
  have hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r (fun c => (target c).ofLp)
          (fun y => (staticSpectralChoiVector d (T * y) energy).ofLp)
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T)))
        (staticSpectralChoiVector d (T * x) energy).ofLp i‖ ^ 2)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / staticChoiSpeed energy / T))
          (epsw / staticChoiSpeed energy / T))ᶜ) := by
    intro i
    exact integrable_sq_replicaSubspaceCoordinate_staticSpectralChoiVector
      hd energy T _ i _
  simpa only [WithLp.toLp_ofLp] using
    (no_second_capture_of_returnExcised_gaussianIncidenceAction_lt_arbitraryTarget
      (fun u v => pureStateTraceDistance
        (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin d × Fin d))
        (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d × Fin d)))
      (fun t => (staticSpectralChoiVector d t energy).ofLp)
      (fun c => (target c).ofLp) hr htargetInner
      (staticChoiSpeed_pos energy) hTpos hepsn hgap hT hthreshold
      htriangle hLip hfidelity hmeas hcoord haction)

end RHTower
