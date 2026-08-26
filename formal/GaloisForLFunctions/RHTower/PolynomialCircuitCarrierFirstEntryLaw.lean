import GaloisForLFunctions.RHTower.ContinuousCircuitReturnExcisedFirstEntryLaw

/-!
# Polynomial carrier reduction for continuous-circuit first entry

An arbitrary containing replica subspace is enough for return-excised coarea:
every replicated target lies in the carrier, so complete target capture forces
large carrier-projection mass.  Target label cardinality remains irrelevant.

For exact-`s` continuous two-qubit Choi circuits, the range of the polynomial
coefficient map is an explicit carrier.  It contains every replicated circuit
endpoint and has rank at most

`(n*n)^s * (r*s+1)^(16*s)`.

The carrier and its rank bound survive arbitrary common unitary coordinate
transport, including conjugation into a Hamiltonian eigenbasis.  Consequently
the first-entry problem reduces to anti-concentration of one explicit finite
polynomial-feature carrier rather than an unknown occupied circuit image.
-/

open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HTGeometry

noncomputable def returnExcisedReplicaCarrierIncidenceAction
    {X α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (state : X → α → ℂ) (returnSet : Set X) : ℝ :=
  returnExcisedFiniteCoordinateIncidenceAction μ
    (fun x i => replicaSubspaceCoordinate r S (state x) i) returnSet

theorem returnExcisedReplicaCarrierIncidenceAction_eq_pairKernel
    {X α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [SFinite μ] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (state : X → α → ℂ) (returnSet : Set X) :
    returnExcisedReplicaCarrierIncidenceAction μ r S state returnSet =
      ∫ p in (returnSetᶜ ×ˢ returnSetᶜ),
        replicaSubspacePairIncidenceKernel r S state p ∂(μ.prod μ) := by
  rfl

theorem finitePureStateFidelity_pow_le_replicaSubspaceProjectionMass_of_mem
    {α : Type*} [Fintype α]
    (r : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (ψ target : α → ℂ)
    (hmem : finitePureTensorPowerEuclidean r target ∈ S)
    (htarget : ‖finitePureTensorPowerEuclidean r target‖ ≤ 1) :
    finitePureStateFidelity ψ target ^ r ≤
      replicaSubspaceProjectionMass r S ψ := by
  let u := finitePureTensorPowerEuclidean r ψ
  let v := finitePureTensorPowerEuclidean r target
  let vS : S := ⟨v, hmem⟩
  have hproj : inner ℂ (S.orthogonalProjectionOnto u) vS = inner ℂ u v :=
    S.inner_orthogonalProjectionOnto_eq_of_mem_right vS u
  have hcs := norm_inner_le_norm (𝕜 := ℂ)
    (S.orthogonalProjectionOnto u) vS
  have hinner : ‖inner ℂ u v‖ ≤ ‖S.orthogonalProjectionOnto u‖ := by
    rw [← hproj]
    calc
      ‖inner ℂ (S.orthogonalProjectionOnto u) vS‖ ≤
          ‖S.orthogonalProjectionOnto u‖ * ‖vS‖ := hcs
      _ ≤ ‖S.orthogonalProjectionOnto u‖ * 1 := by
        gcongr
        simpa [vS, v] using htarget
      _ = ‖S.orthogonalProjectionOnto u‖ := mul_one _
  have hfid : finitePureStateFidelity ψ target ^ r =
      ‖inner ℂ u v‖ ^ 2 := by
    rw [← finitePureStateFidelity_tensorPower r ψ target]
    rw [finitePureStateFidelity, show inner ℂ u v =
      finiteComplexInner (finitePureTensorPower r ψ)
        (finitePureTensorPower r target) by
          exact inner_toLp_eq_finiteComplexInner _ _]
  rw [hfid]
  exact pow_le_pow_left₀ (norm_nonneg _) hinner 2

/-- Arbitrary-carrier return-excised coarea law. Target type may have any
cardinality; only membership of each replicated target in the chosen carrier
is used. -/
theorem quenchedReplica_returnExcisedCarrierCoareaIncidence_bound
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    (r : ℕ)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (hmem : ∀ c, finitePureTensorPowerEuclidean r (target c) ∈ S)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r S (state x) i)
        (μ.restrict returnSetᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r S (state x) i‖ ^ 2)
        (μ.restrict returnSetᶜ)) :
    (((μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
        threshold ^ r) ^ 2) ≤
      (Module.finrank ℂ S : ℝ) *
        returnExcisedReplicaCarrierIncidenceAction
          μ r S state returnSet := by
  let a : X → Fin (Module.finrank ℂ S) → ℂ :=
    fun x i => replicaSubspaceCoordinate r S (state x) i
  let E : Set X := {x | ∃ c,
    threshold ≤ finitePureStateFidelity (state x) (target c)}
  have hcapture : E ∩ returnSetᶜ ⊆
      {x | threshold ^ r ≤ finiteCoordinateEnergy a x} := by
    intro x hx
    obtain ⟨c, hc⟩ := hx.1
    have htargetNorm :
        ‖finitePureTensorPowerEuclidean r (target c)‖ ≤ 1 := by
      rw [norm_finitePureTensorPowerEuclidean_eq_one r
        (target c) (htarget c)]
    have hproj :=
      finitePureStateFidelity_pow_le_replicaSubspaceProjectionMass_of_mem
        r S (state x) (target c) (hmem c) htargetNorm
    have hpow : threshold ^ r ≤
        finitePureStateFidelity (state x) (target c) ^ r :=
      pow_le_pow_left₀ hthreshold.le hc r
    have hmass := hpow.trans hproj
    rw [replicaSubspaceProjectionMass_eq_finiteCoordinateEnergy] at hmass
    simpa [finiteCoordinateEnergy, a] using hmass
  simpa [E, a, returnExcisedReplicaCarrierIncidenceAction,
    Fintype.card_fin] using
    returnExcisedFiniteCoordinateIncidence_bound
      μ E returnSet hreturn a (threshold ^ r) (pow_pos hthreshold r)
        hcapture hmeas hcoord

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry.TwoQubitCircuit

/-- Explicit polynomial-feature carrier for every exact-`s` two-qubit Choi
endpoint at replica order `r`. -/
noncomputable def twoQubitCircuitChoiPolynomialReplicaCarrier
    (n s r : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ
      (Fin r → ((Fin n → Bool) × (Fin n → Bool)))) :=
  let coord : twoQubitCircuitArchitectureIndex n s →
      ((Fin n → Bool) × (Fin n → Bool)) →
        MvPolynomial (Fin (s * 16)) ℂ :=
    fun a => complexTwoQubitCircuitChoiCoords s a
  (polynomialFamilyReplicaCoefficientMap coord r s).range

theorem finrank_twoQubitCircuitChoiPolynomialReplicaCarrier_le
    (n s r : ℕ) :
    Module.finrank ℂ
        (twoQubitCircuitChoiPolynomialReplicaCarrier n s r) ≤
      (n * n) ^ s * (r * s + 1) ^ (s * 16) := by
  let coord : twoQubitCircuitArchitectureIndex n s →
      ((Fin n → Bool) × (Fin n → Bool)) →
        MvPolynomial (Fin (s * 16)) ℂ :=
    fun a => complexTwoQubitCircuitChoiCoords s a
  let L := polynomialFamilyReplicaCoefficientMap coord r s
  change Module.finrank ℂ L.range ≤ _
  calc
    Module.finrank ℂ L.range ≤ Module.finrank ℂ
        (twoQubitCircuitArchitectureIndex n s ×
          multilinearReplicaFeatureIndex (s * 16) (r * s) → ℂ) :=
      LinearMap.finrank_range_le L
    _ = (n * n) ^ s * (r * s + 1) ^ (s * 16) := by simp

theorem finitePureTensorPowerEuclidean_twoQubitCircuitChoi_mem_carrier
    {C : Type*} {n s : ℕ}
    (pos : C → twoQubitCircuitArchitectureIndex n s)
    (G : C → Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ c k, IsTwoQubitGate
      (pos c k).1 (pos c k).2 (G c k))
    (r : ℕ) (c : C) :
    finitePureTensorPowerEuclidean r (fun p =>
        (List.ofFn (G c)).prod p.1 p.2 /
          Real.sqrt (Fintype.card (Fin n → Bool))) ∈
      twoQubitCircuitChoiPolynomialReplicaCarrier n s r := by
  classical
  let coord : twoQubitCircuitArchitectureIndex n s →
      ((Fin n → Bool) × (Fin n → Bool)) →
        MvPolynomial (Fin (s * 16)) ℂ :=
    fun a => complexTwoQubitCircuitChoiCoords s a
  have hcoord : ∀ a p, coord a p ∈
      MvPolynomial.degreesLE ℂ (Fin (s * 16))
        (multilinearDegreeBound (s * 16) s) := by
    intro a p
    exact complexTwoQubitCircuitChoiCoords_mem_degreeGateCount a p
  have hexists : ∀ c, ∃ u : Fin (s * 16) → ℂ, ∀ p,
      MvPolynomial.aeval u (coord (pos c) p) =
        (List.ofFn (G c)).prod p.1 p.2 /
          Real.sqrt (Fintype.card (Fin n → Bool)) := by
    intro c
    exact exists_param_aeval_complexTwoQubitCircuitChoiCoords
      (pos c) (G c) (hG c)
  choose param hparam using hexists
  have hbase :=
    finitePureTensorPowerEuclidean_aeval_mem_polynomialFamilyReplicaCoefficientMap_range
      coord hcoord pos param r c
  have htarget : (fun p =>
      (List.ofFn (G c)).prod p.1 p.2 /
        Real.sqrt (Fintype.card (Fin n → Bool))) =
      (fun p => MvPolynomial.aeval (param c) (coord (pos c) p)) := by
    funext p
    exact (hparam c p).symm
  rw [htarget]
  simpa only [twoQubitCircuitChoiPolynomialReplicaCarrier, coord] using hbase

end GaloisForLFunctions.HTGeometry.TwoQubitCircuit

namespace GaloisForLFunctions.HTGeometry

/-- Replica carrier transported by one common unitary coordinate change. -/
noncomputable def unitaryTransportReplicaCarrier
    {α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (U : Matrix.unitaryGroup α ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α))) :
    Submodule ℂ (EuclideanSpace ℂ (Fin r → α)) :=
  S.map (finiteTensorEuclideanMap r
    (Matrix.toLpLin 2 2 (U : Matrix α α ℂ)))

theorem finitePureTensorPowerEuclidean_unitaryTransport_mem_carrier
    {C α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (U : Matrix.unitaryGroup α ℂ)
    (target : C → α → ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (hmem : ∀ c, finitePureTensorPowerEuclidean r (target c) ∈ S)
    (c : C) :
    finitePureTensorPowerEuclidean r
        (RHTower.unitaryTransportTarget U target c) ∈
      unitaryTransportReplicaCarrier r U S := by
  have hmapped : finiteTensorEuclideanMap r
      (Matrix.toLpLin 2 2 (U : Matrix α α ℂ))
        (finitePureTensorPowerEuclidean r (target c)) ∈
      unitaryTransportReplicaCarrier r U S := by
    exact ⟨finitePureTensorPowerEuclidean r (target c), hmem c, rfl⟩
  rw [finiteTensorEuclideanMap_pureTensor] at hmapped
  simpa only [RHTower.unitaryTransportTarget, Matrix.toLpLin_apply,
    WithLp.toLp_ofLp] using hmapped

theorem finrank_unitaryTransportReplicaCarrier_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (U : Matrix.unitaryGroup α ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α))) :
    Module.finrank ℂ (unitaryTransportReplicaCarrier r U S) ≤
      Module.finrank ℂ S := by
  exact Submodule.finrank_map_le _ _

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry.TwoQubitCircuit

noncomputable def unitaryTransportTwoQubitCircuitChoiPolynomialReplicaCarrier
    (n s r : ℕ)
    (U : Matrix.unitaryGroup
      ((Fin n → Bool) × (Fin n → Bool)) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ
      (Fin r → ((Fin n → Bool) × (Fin n → Bool)))) :=
  unitaryTransportReplicaCarrier r U
    (twoQubitCircuitChoiPolynomialReplicaCarrier n s r)

theorem finrank_unitaryTransportTwoQubitCircuitChoiPolynomialReplicaCarrier_le
    (n s r : ℕ)
    (U : Matrix.unitaryGroup
      ((Fin n → Bool) × (Fin n → Bool)) ℂ) :
    Module.finrank ℂ
        (unitaryTransportTwoQubitCircuitChoiPolynomialReplicaCarrier
          n s r U) ≤
      (n * n) ^ s * (r * s + 1) ^ (s * 16) := by
  exact (finrank_unitaryTransportReplicaCarrier_le r U
      (twoQubitCircuitChoiPolynomialReplicaCarrier n s r)).trans
    (finrank_twoQubitCircuitChoiPolynomialReplicaCarrier_le n s r)

theorem finitePureTensorPowerEuclidean_unitaryTransport_twoQubitCircuitChoi_mem_carrier
    {C : Type*} {n s : ℕ}
    (pos : C → twoQubitCircuitArchitectureIndex n s)
    (G : C → Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ c k, IsTwoQubitGate
      (pos c k).1 (pos c k).2 (G c k))
    (r : ℕ)
    (U : Matrix.unitaryGroup
      ((Fin n → Bool) × (Fin n → Bool)) ℂ)
    (c : C) :
    finitePureTensorPowerEuclidean r
        (RHTower.unitaryTransportTarget U (fun c p =>
          (List.ofFn (G c)).prod p.1 p.2 /
            Real.sqrt (Fintype.card (Fin n → Bool))) c) ∈
      unitaryTransportTwoQubitCircuitChoiPolynomialReplicaCarrier
        n s r U := by
  exact finitePureTensorPowerEuclidean_unitaryTransport_mem_carrier
    r U (fun c p =>
      (List.ofFn (G c)).prod p.1 p.2 /
        Real.sqrt (Fintype.card (Fin n → Bool)))
    (twoQubitCircuitChoiPolynomialReplicaCarrier n s r)
    (finitePureTensorPowerEuclidean_twoQubitCircuitChoi_mem_carrier
      pos G hG r) c

end GaloisForLFunctions.HTGeometry.TwoQubitCircuit

namespace RHTower

/-- **Return-excised incidence action controls first entry.**  The cut removes only the common
initial time cell.  Every later source sheet remains in the Gaussian measure, while the circuit
family enters through its occupied replica incidence span rather than its label count. -/
theorem no_second_capture_of_returnExcised_gaussianCarrierAction_lt
    {C α : Type*} [Fintype α]
    (D : (α → ℂ) → (α → ℂ) → ℝ)
    (psi : ℝ → α → ℂ) (target : C → α → ℂ)
    (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (hmem : ∀ c, finitePureTensorPowerEuclidean r (target c) ∈ S)
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
        S
        (psi (T * x)) i)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        S
        (psi (T * x)) i‖ ^ 2)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ))
    (haction :
      (Module.finrank ℂ S : ℝ) *
        returnExcisedReplicaCarrierIncidenceAction (gaussianReal 0 1) r S
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
  have hcoarea :=
    quenchedReplica_returnExcisedCarrierCoareaIncidence_bound
      (gaussianReal 0 1) r target state S hmem htarget threshold hthreshold R
      measurableSet_Icc (by simpa [state, R, a] using hmeas)
      (by simpa [state, R, a] using hcoord)
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

namespace RHTower

/-- **Static Choi first-return law from the exact return-excised incidence action.**  For every
target family of arbitrary cardinality, a bound on the occupied-image action below the displayed threshold excludes
all later narrow captures through `T`.  Continuity, measurability, and integrability are automatic;
the action estimate is the only remaining scientific input. -/
theorem no_forward_pureChoiCircuitReturn_of_returnExcisedGaussianCarrierAction_lt
    {d : ℕ} (hd : 0 < d)
    {C : Type*}
    (energy : Fin d → ℝ)
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    (r : ℕ)
    (S : Submodule ℂ
      (EuclideanSpace ℂ (Fin r → (Fin d × Fin d))))
    (hmem : ∀ c, finitePureTensorPowerEuclidean r (target c).ofLp ∈ S)
    {T epsn epsw : ℝ}
    (hTpos : 0 < T) (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hepswOne : epsw < 1)
    (hT : epsw / staticChoiSpeed energy ≤ T)
    (haction :
      (Module.finrank ℂ S : ℝ) *
        returnExcisedReplicaCarrierIncidenceAction (gaussianReal 0 1) r S
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
        S
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
        S
        (staticSpectralChoiVector d (T * x) energy).ofLp i‖ ^ 2)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / staticChoiSpeed energy / T))
          (epsw / staticChoiSpeed energy / T))ᶜ) := by
    intro i
    exact integrable_sq_replicaSubspaceCoordinate_staticSpectralChoiVector
      hd energy T _ i _
  simpa only [WithLp.toLp_ofLp] using
    (no_second_capture_of_returnExcised_gaussianCarrierAction_lt
      (fun u v => pureStateTraceDistance
        (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin d × Fin d))
        (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d × Fin d)))
      (fun t => (staticSpectralChoiVector d t energy).ofLp)
      (fun c => (target c).ofLp) r S hmem htargetInner
      (staticChoiSpeed_pos energy) hTpos hepsn hgap hT hthreshold
      htriangle hLip hfidelity hmeas hcoord haction)


end RHTower
