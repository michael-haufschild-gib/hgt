import GaloisForLFunctions.RHTower.StaticChoiOptimalDesignFirstReturnLaw
import GaloisForLFunctions.RHTower.DirectAdaptiveStaticChoiWeightedCrowdingLaw

/-!
# Optimal-design weighted spectral crowding and first return

The maximum replica-action crowding degree discards both target weights and circuit geometry.  This
module retains the determinant-design weights selected by the occupied circuit endpoint image and
uses them inside the spectral near-action mass.  The resulting first-return budget couples the
spectrum, eigenbasis, and circuit image in one quenched invariant.
-/

open Set MeasureTheory ProbabilityTheory Matrix
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

noncomputable section

namespace RHTower

/-- A canonical determinant-optimal endpoint design, selected from the unconditional existence
theorem. -/
noncomputable def replicaTargetOptimalDesignWeight
    {C α : Type*} [Fintype C] [Nonempty C] [DecidableEq C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1) : C → ℝ :=
  Classical.choose (exists_replicaTarget_optimalDesign_pointwise r target htarget)

theorem replicaTargetOptimalDesignWeight_mem_stdSimplex
    {C α : Type*} [Fintype C] [Nonempty C] [DecidableEq C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1) :
    replicaTargetOptimalDesignWeight r target htarget ∈ stdSimplex ℝ C :=
  (Classical.choose_spec
    (exists_replicaTarget_optimalDesign_pointwise r target htarget)).1

theorem replicaTargetOptimalDesignWeight_pointwise
    {C α : Type*} [Fintype C] [Nonempty C] [DecidableEq C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (ψ : α → ℂ) (c : C) :
    finitePureStateFidelity ψ (target c) ^ r ≤
      (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
        ∑ j, replicaTargetOptimalDesignWeight r target htarget j *
          finitePureStateFidelity ψ (target j) ^ r :=
  (Classical.choose_spec
    (exists_replicaTarget_optimalDesign_pointwise r target htarget)).2 ψ c

theorem finiteComplexInner_ofLp_self_eq_one_of_norm_eq_one
    {α : Type*} [Fintype α] (target : EuclideanSpace ℂ α)
    (htarget : ‖target‖ = 1) :
    finiteComplexInner target.ofLp target.ofLp = 1 := by
  rw [finiteComplexInner_eq_inner]
  simp only [WithLp.toLp_ofLp]
  rw [inner_self_eq_norm_sq_to_K, htarget]
  norm_num

/-- Canonical determinant-optimal weights for a normalized static Choi target dictionary. -/
noncomputable def staticChoiTargetOptimalDesignWeight
    {d : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1) : C → ℝ :=
  replicaTargetOptimalDesignWeight r (fun c => (target c).ofLp)
    (fun c => finiteComplexInner_ofLp_self_eq_one_of_norm_eq_one
      (target c) (htarget c))

theorem staticChoiTargetOptimalDesignWeight_mem_stdSimplex
    {d : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1) :
    staticChoiTargetOptimalDesignWeight r target htarget ∈ stdSimplex ℝ C :=
  replicaTargetOptimalDesignWeight_mem_stdSimplex r
    (fun c => (target c).ofLp) _

theorem staticChoiTargetOptimalDesignWeight_pointwise
    {d : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    (φ : (Fin d × Fin d) → ℂ) (c : C) :
    finitePureStateFidelity φ (target c).ofLp ^ r ≤
      (Module.finrank ℂ
        (replicaTargetSpan r (fun j => (target j).ofLp)) : ℝ) *
        ∑ j, staticChoiTargetOptimalDesignWeight r target htarget j *
          finitePureStateFidelity φ (target j).ofLp ^ r :=
  replicaTargetOptimalDesignWeight_pointwise r
    (fun j => (target j).ofLp) _ φ c

/-- Restricted complete-target capture bound for any supplied probability design satisfying the
replica pointwise leverage inequality. -/
theorem measure_completeTargetCapture_restrict_le_designMoments
    {X C α : Type*} [MeasurableSpace X]
    [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (target : C → α → ℂ) (state : X → α → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (hdesign : ∀ (ψ : α → ℂ) (c : C),
      finitePureStateFidelity ψ (target c) ^ r ≤
        (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          ∑ j, w j * finitePureStateFidelity ψ (target j) ^ r)
    (hint : ∀ c, Integrable
      (fun x => finitePureStateFidelity (state x) (target c) ^ r)
      (μ.restrict returnSetᶜ)) :
    threshold ^ r *
        (μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
        ∑ c, w c * ∫ x,
          finitePureStateFidelity (state x) (target c) ^ r
            ∂(μ.restrict returnSetᶜ) := by
  classical
  let ν : Measure X := μ.restrict returnSetᶜ
  let E : Set X :=
    {x | ∃ c, threshold ≤ finitePureStateFidelity (state x) (target c)}
  let q : X → ℝ := fun x =>
    (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
      ∑ c, w c * finitePureStateFidelity (state x) (target c) ^ r
  have hEQ : E ⊆ {x | threshold ^ r ≤ q x} := by
    intro x hx
    obtain ⟨c, hc⟩ := hx
    calc
      threshold ^ r ≤ finitePureStateFidelity (state x) (target c) ^ r :=
        pow_le_pow_left₀ hthreshold.le hc r
      _ ≤ q x := hdesign (state x) c
  have hintq : Integrable q ν := by
    dsimp [q, ν]
    apply Integrable.const_mul
    exact integrable_finsetSum Finset.univ fun c _ =>
      (hint c).const_mul (w c)
  have hqnonneg : 0 ≤ᵐ[ν] q :=
    Filter.Eventually.of_forall fun x => by
      dsimp [q]
      exact mul_nonneg (Nat.cast_nonneg _) <|
        Finset.sum_nonneg fun c _ =>
          mul_nonneg (hw.1 c) (pow_nonneg (sq_nonneg _) r)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hqnonneg hintq (threshold ^ r)
  have hscaled : threshold ^ r * ν.real E ≤ ∫ x, q x ∂ν := by
    calc
      threshold ^ r * ν.real E ≤
          threshold ^ r * ν.real {x | threshold ^ r ≤ q x} := by
        exact mul_le_mul_of_nonneg_left
          (measureReal_mono hEQ (by finiteness))
          (pow_nonneg hthreshold.le r)
      _ ≤ ∫ x, q x ∂ν := hmarkov
  have hqIntegral :
      (∫ x, q x ∂ν) =
        (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          ∑ c, w c * ∫ x,
            finitePureStateFidelity (state x) (target c) ^ r ∂ν := by
    dsimp [q]
    rw [integral_const_mul]
    rw [integral_finsetSum Finset.univ
      (fun c _ => (hint c).const_mul (w c))]
    apply congrArg
    apply Finset.sum_congr rfl
    intro c _
    rw [integral_const_mul]
  simpa [E, ν, hqIntegral] using hscaled

/-- A supplied replica design and its weighted restricted moment exclude all later captures. -/
theorem no_second_capture_of_returnExcised_gaussianDesignMoment_lt
    {C α : Type*} [Fintype C] [Fintype α]
    (D : (α → ℂ) → (α → ℂ) → ℝ)
    (psi : ℝ → α → ℂ) (target : C → α → ℂ)
    {r : ℕ} {speed epsn epsw T threshold fixedMoment : ℝ}
    (hspeed : 0 < speed) (hTpos : 0 < T)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hT : epsw / speed ≤ T) (hthreshold : 0 < threshold)
    (htriangle : ∀ t u c,
      D (psi t) (target c) ≤ D (psi t) (psi u) + D (psi u) (target c))
    (hLip : ∀ t u, D (psi t) (psi u) ≤ speed * |t - u|)
    (hfidelity : ∀ t c, D (psi t) (target c) ≤ epsw →
      threshold ≤ finitePureStateFidelity (psi t) (target c))
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (hdesign : ∀ (φ : α → ℂ) (c : C),
      finitePureStateFidelity φ (target c) ^ r ≤
        (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          ∑ j, w j * finitePureStateFidelity φ (target j) ^ r)
    (hint : ∀ c, Integrable
      (fun x => finitePureStateFidelity (psi (T * x)) (target c) ^ r)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ))
    (hweightedMoment :
      (∑ c, w c * ∫ x,
        finitePureStateFidelity (psi (T * x)) (target c) ^ r
          ∂((gaussianReal 0 1).restrict
            (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ)) ≤ fixedMoment)
    (hbudget :
      (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) * fixedMoment <
        gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T)) *
          threshold ^ r) :
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
  have hupper := measure_completeTargetCapture_restrict_le_designMoments
    (gaussianReal 0 1) target state threshold hthreshold R w hw hdesign
    (by simpa [state, R, a] using hint)
  have hupper' : threshold ^ r *
        ((gaussianReal 0 1).restrict Rᶜ).real E ≤
      (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) * fixedMoment :=
    hupper.trans (mul_le_mul_of_nonneg_left
      (by simpa [state, R, a] using hweightedMoment) (by positivity))
  have hscaled : threshold ^ r *
        (gaussianFloorTwo * (mesh / (2 * T))) ≤
      threshold ^ r * ((gaussianReal 0 1).restrict Rᶜ).real E :=
    mul_le_mul_of_nonneg_left hmass (pow_nonneg hthreshold.le r)
  have hcontra := hscaled.trans hupper'
  apply (not_lt_of_ge ?_) hbudget
  simpa [mul_assoc, mul_left_comm, mul_comm, mesh] using hcontra

/-- Exact one-target Gaussian Choi moment bound retaining target-weighted near-action mass. -/
theorem integral_gaussian_staticChoi_fidelity_pow_le_weightedCrowding
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ‖target‖ = 1)
    (r : ℕ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    (∫ x, finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r
      ∂gaussianReal 0 1) ≤
      (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
        directStaticChoiTargetNearActionMass target energy r δ +
        Real.exp (-((T * δ) ^ 2) / 2) := by
  let weight := directStaticChoiTargetWeight d target
  let negEnergy : Fin d → ℝ := fun i => -energy i
  let twist := directStaticChoiTargetTwist target
  have hmean :
      ((∫ x, finitePureStateFidelity
          (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r
        ∂gaussianReal 0 1 : ℝ) : ℂ) =
        twistedGaussianSpectralFidelityMean weight negEnergy twist r T := by
    unfold twistedGaussianSpectralFidelityMean
    have hInt : Integrable
        (fun x => finitePureStateFidelity
          (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r)
        (gaussianReal 0 1) := by
      simpa using
        (integrable_staticChoi_fidelity_pow hd energy T target htarget r Set.univ)
    change Complex.ofRealCLM (∫ x, finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r
      ∂gaussianReal 0 1) = _
    rw [← Complex.ofRealCLM.integral_comp_comm hInt]
    apply integral_congr_ae
    filter_upwards with x
    rw [← staticChoi_fidelity_eq_directTwistedFidelity
      (d := d) (T * x) energy target]
    norm_cast
  have hreal :
      (∫ x, finitePureStateFidelity
          (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r
        ∂gaussianReal 0 1) =
        (twistedGaussianSpectralFidelityMean weight negEnergy twist r T).re := by
    rw [← hmean]
    simp
  rw [hreal]
  calc
    _ ≤ ‖twistedGaussianSpectralFidelityMean weight negEnergy twist r T‖ :=
      Complex.re_le_norm _
    _ ≤ fidelityReplicaCollisionMass weight negEnergy r +
        fidelityReplicaNearActionMass weight negEnergy r δ +
        Real.exp (-((T * δ) ^ 2) / 2) :=
      norm_twistedGaussianSpectralFidelityMean_le_collision_add_crowding
        (directStaticChoiTargetWeight_nonneg target)
        (sum_directStaticChoiTargetWeight_le_one hd htarget)
        (norm_directStaticChoiTargetTwist target) r hT hδ
    _ ≤ (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
        fidelityReplicaNearActionMass weight negEnergy r δ +
        Real.exp (-((T * δ) ^ 2) / 2) := by
      gcongr
      exact directStaticChoiTarget_collision_le_factorial_inv_pow
        hd hmax htarget r
    _ = _ := rfl

/-- **Optimal-design weighted-crowding static first-return law.**  This is the strongest finite
target criterion in the hierarchy: the complete union costs occupied replica dimension, while the
spectral term is the same design-weighted near-action mass rather than a worst-spectrum degree. -/
theorem no_forward_pureChoiCircuitReturn_of_optimalDesignWeightedCrowding
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C]
    {energy : Fin d → ℝ} (hmax : MaximallyProjectiveEnergy energy)
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    {r : ℕ} {T δ epsn epsw : ℝ}
    (hTpos : 0 < T) (hδ : 0 < δ)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hepswOne : epsw < 1)
    (hT : epsw / staticChoiSpeed energy ≤ T)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (hdesign : ∀ (φ : (Fin d × Fin d) → ℂ) (c : C),
      finitePureStateFidelity φ (target c).ofLp ^ r ≤
        (Module.finrank ℂ
          (replicaTargetSpan r (fun j => (target j).ofLp)) : ℝ) *
          ∑ j, w j * finitePureStateFidelity φ (target j).ofLp ^ r)
    (hbudget :
      (Module.finrank ℂ
          (replicaTargetSpan r (fun c => (target c).ofLp)) : ℝ) *
        ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
          ∑ c, w c * directStaticChoiTargetNearActionMass
            (target c) energy r δ +
          Real.exp (-((T * δ) ^ 2) / 2)) <
        gaussianFloorTwo *
          ((epsw - epsn) / staticChoiSpeed energy / (2 * T)) *
          (1 - epsw ^ 2) ^ r) :
    ¬ ∃ t ∈ Icc
        (epsw / staticChoiSpeed energy +
          (epsw - epsn) / staticChoiSpeed energy) T,
      ∃ c, pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (target c) ≤ epsn := by
  have hepsw : 0 ≤ epsw := hepsn.trans (le_of_lt hgap)
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
  have hint : ∀ c, Integrable
      (fun x => finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp (target c).ofLp ^ r)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / staticChoiSpeed energy / T))
          (epsw / staticChoiSpeed energy / T))ᶜ) := by
    intro c
    exact integrable_staticChoi_fidelity_pow hd energy T (target c) (htarget c) r _
  have hsingle : ∀ c,
      (∫ x, finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp (target c).ofLp ^ r
        ∂((gaussianReal 0 1).restrict
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T))ᶜ)) ≤
        (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
          directStaticChoiTargetNearActionMass (target c) energy r δ +
          Real.exp (-((T * δ) ^ 2) / 2) := by
    intro c
    refine (integral_mono_measure Measure.restrict_le_self ?_ ?_).trans
      (integral_gaussian_staticChoi_fidelity_pow_le_weightedCrowding
        hd hmax (target c) (htarget c) r hTpos hδ)
    · filter_upwards with x
      exact pow_nonneg (sq_nonneg _) r
    · simpa using
        (integrable_staticChoi_fidelity_pow hd energy T (target c) (htarget c) r Set.univ)
  have hweighted :
      (∑ c, w c * ∫ x, finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp (target c).ofLp ^ r
          ∂((gaussianReal 0 1).restrict
            (Icc (-(epsw / staticChoiSpeed energy / T))
              (epsw / staticChoiSpeed energy / T))ᶜ)) ≤
        (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
          ∑ c, w c * directStaticChoiTargetNearActionMass
            (target c) energy r δ +
          Real.exp (-((T * δ) ^ 2) / 2) := by
    calc
      _ ≤ ∑ c, w c *
          ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
            directStaticChoiTargetNearActionMass (target c) energy r δ +
            Real.exp (-((T * δ) ^ 2) / 2)) :=
        Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hsingle c) (hw.1 c)
      _ = _ := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul, hw.2]
        ring
  simpa only [WithLp.toLp_ofLp] using
    (no_second_capture_of_returnExcised_gaussianDesignMoment_lt
      (fun u v => pureStateTraceDistance
        (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin d × Fin d))
        (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d × Fin d)))
      (fun t => (staticSpectralChoiVector d t energy).ofLp)
      (fun c => (target c).ofLp)
      (staticChoiSpeed_pos energy) hTpos hepsn hgap hT hthreshold
      htriangle hLip hfidelity w hw hdesign hint hweighted hbudget)

/-- **Canonical optimal-design weighted-crowding law.**  Determinant-design existence is fully
discharged.  The sole quantitative input is the displayed same-draw weighted spectral budget. -/
theorem no_forward_pureChoiCircuitReturn_of_canonicalOptimalDesignWeightedCrowding
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    {energy : Fin d → ℝ} (hmax : MaximallyProjectiveEnergy energy)
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    {r : ℕ} {T δ epsn epsw : ℝ}
    (hTpos : 0 < T) (hδ : 0 < δ)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hepswOne : epsw < 1)
    (hT : epsw / staticChoiSpeed energy ≤ T)
    (hbudget :
      (Module.finrank ℂ
          (replicaTargetSpan r (fun c => (target c).ofLp)) : ℝ) *
        ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
          ∑ c, staticChoiTargetOptimalDesignWeight r target htarget c *
            directStaticChoiTargetNearActionMass (target c) energy r δ +
          Real.exp (-((T * δ) ^ 2) / 2)) <
        gaussianFloorTwo *
          ((epsw - epsn) / staticChoiSpeed energy / (2 * T)) *
          (1 - epsw ^ 2) ^ r) :
    ¬ ∃ t ∈ Icc
        (epsw / staticChoiSpeed energy +
          (epsw - epsn) / staticChoiSpeed energy) T,
      ∃ c, pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (target c) ≤ epsn := by
  exact no_forward_pureChoiCircuitReturn_of_optimalDesignWeightedCrowding
    hd hmax target htarget hTpos hδ hepsn hgap hepswOne hT
    (staticChoiTargetOptimalDesignWeight r target htarget)
    (staticChoiTargetOptimalDesignWeight_mem_stdSimplex r target htarget)
    (staticChoiTargetOptimalDesignWeight_pointwise r target htarget)
    hbudget

end RHTower
