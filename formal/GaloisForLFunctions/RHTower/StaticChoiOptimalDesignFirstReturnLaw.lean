import GaloisForLFunctions.RHTower.StaticChoiReturnExcisedGaussianFirstReturnLaw
import GaloisForLFunctions.RHTower.DirectAdaptiveStaticChoiCrowdingLaw
import GaloisForLFunctions.HTGeometry.ReturnExcisedOptimalDesignCoareaLaw

/-!
# Static Choi first return from an intrinsic-rank spectral moment

A determinant-optimal probability design on the occupied replica endpoints converts capture by an
entire finite target dictionary into one weighted single-target moment.  The cost is the intrinsic
dimension of the occupied replica span, not the number of target labels.  Return removal is performed
on the source measure, so every surviving source sheet remains counted.

For a static Choi orbit, each single-target Gaussian replica moment is bounded by one explicit
spectral crowding expression.  Consequently, first return to the complete target dictionary follows
from an intrinsic-rank times spectral-moment budget.  No minimum spectral gap or incidence action is
used.
-/

open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Static Choi fidelity is exactly the direct phase-twisted spectral fidelity. -/
theorem staticChoi_fidelity_eq_directTwistedFidelity
    {d : ℕ} (t : ℝ) (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    ((finitePureStateFidelity
      (staticSpectralChoiVector d t energy).ofLp target.ofLp : ℝ) : ℂ) =
      twistedFiniteSpectralFidelity
        (directStaticChoiTargetWeight d target) (fun i => -energy i)
        (directStaticChoiTargetTwist target) t := by
  rw [finitePureStateFidelity_eq_norm_inner_sq]
  simp only [WithLp.toLp_ofLp]
  rw [norm_inner_symm, inner_staticSpectralChoiVector_target_eq_directTwistedAmplitude]
  unfold twistedFiniteSpectralFidelity
  rw [Complex.normSq_eq_norm_sq]

/-- Every static Choi fidelity power is integrable against every restricted Gaussian measure. -/
theorem integrable_staticChoi_fidelity_pow
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (T : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ‖target‖ = 1) (r : ℕ) (R : Set ℝ) :
    Integrable
      (fun x => finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r)
      ((gaussianReal 0 1).restrict R) := by
  have hcState := continuous_staticSpectralChoiVector_scaled hd energy T
  have hcInner : Continuous (fun x =>
      inner ℂ target (staticSpectralChoiVector d (T * x) energy)) :=
    Continuous.inner continuous_const hcState
  have hc : Continuous (fun x => finitePureStateFidelity
      (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r) := by
    simp_rw [finitePureStateFidelity_eq_norm_inner_sq]
    simp only [WithLp.toLp_ofLp]
    exact (hcInner.norm.pow 2).pow r
  apply Integrable.of_bound hc.aestronglyMeasurable 1
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) r)]
  have hinner : ‖inner ℂ target
      (staticSpectralChoiVector d (T * x) energy)‖ ≤ 1 := by
    calc
      _ ≤ ‖target‖ * ‖staticSpectralChoiVector d (T * x) energy‖ :=
        norm_inner_le_norm _ _
      _ = 1 := by rw [htarget, staticSpectralChoiVector_norm hd, one_mul]
  have hsquare : ‖inner ℂ target
      (staticSpectralChoiVector d (T * x) energy)‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (inner ℂ target
      (staticSpectralChoiVector d (T * x) energy))]
  simp only [finitePureStateFidelity_eq_norm_inner_sq, WithLp.toLp_ofLp]
  exact pow_le_one₀ (by positivity) hsquare

/-- A uniform one-target moment bound for one static Choi orbit.  Resonant collision mass is bounded
by the permutation floor, while all nonresonant replica actions are paid through their crowding
degree at scale `δ`. -/
theorem integral_gaussian_staticChoi_fidelity_pow_le_crowding
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ‖target‖ = 1)
    (r : ℕ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    (∫ x, finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r
      ∂gaussianReal 0 1) ≤
      (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
        (replicaActionCrowdingDegree energy r δ : ℝ) *
          ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r) +
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
        (replicaActionCrowdingDegree negEnergy r δ : ℝ) *
          fidelityReplicaPermutationFloor weight r +
        Real.exp (-((T * δ) ^ 2) / 2) :=
      norm_twistedGaussianSpectralFidelityMean_le_collision_add_degree_floor
        (directStaticChoiTargetWeight_nonneg target)
        (sum_directStaticChoiTargetWeight_le_one hd htarget)
        (norm_directStaticChoiTargetTwist target) r hT hδ
    _ ≤ (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
        (replicaActionCrowdingDegree negEnergy r δ : ℝ) *
          ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r) +
        Real.exp (-((T * δ) ^ 2) / 2) := by
      have hcollision := directStaticChoiTarget_collision_le_factorial_inv_pow
        hd hmax htarget r
      have hfloor := directStaticChoiTarget_floor_le_factorial_inv_pow
        hd htarget r
      have hk : 0 ≤ (replicaActionCrowdingDegree negEnergy r δ : ℝ) := by positivity
      gcongr
    _ = _ := by rw [replicaActionCrowdingDegree_neg]

/-- Return-excised optimal-design moment budget excludes every later capture.  Unlike a union bound,
the complete finite target family costs only its occupied replica-span dimension. -/
theorem no_second_capture_of_returnExcised_gaussianOptimalDesignMoment_lt
    {C α : Type*} [Fintype C] [Nonempty C] [DecidableEq C] [Fintype α]
    (D : (α → ℂ) → (α → ℂ) → ℝ)
    (psi : ℝ → α → ℂ) (target : C → α → ℂ)
    {r : ℕ}
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    {speed epsn epsw T threshold fixedMoment : ℝ}
    (hspeed : 0 < speed) (hTpos : 0 < T)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hT : epsw / speed ≤ T) (hthreshold : 0 < threshold)
    (htriangle : ∀ t u c,
      D (psi t) (target c) ≤ D (psi t) (psi u) + D (psi u) (target c))
    (hLip : ∀ t u, D (psi t) (psi u) ≤ speed * |t - u|)
    (hfidelity : ∀ t c, D (psi t) (target c) ≤ epsw →
      threshold ≤ finitePureStateFidelity (psi t) (target c))
    (hint : ∀ c, Integrable
      (fun x => finitePureStateFidelity (psi (T * x)) (target c) ^ r)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ))
    (hmoment : ∀ c,
      (∫ x, finitePureStateFidelity (psi (T * x)) (target c) ^ r
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
  obtain ⟨w, hw, hoptimal, -⟩ :=
    measure_completeTargetCapture_le_optimalDesignMoments
      (gaussianReal 0 1) target state htarget threshold hthreshold R
      measurableSet_Icc (by simpa [state, R, a] using hint)
  have hweighted :
      (∑ c, w c * ∫ x,
        finitePureStateFidelity (state x) (target c) ^ r
          ∂((gaussianReal 0 1).restrict Rᶜ)) ≤ fixedMoment := by
    calc
      _ ≤ ∑ c, w c * fixedMoment :=
        Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left
            (by simpa [state, R, a] using hmoment c) (hw.1 c)
      _ = fixedMoment := by rw [← Finset.sum_mul, hw.2, one_mul]
  have hupper : threshold ^ r *
        ((gaussianReal 0 1).restrict Rᶜ).real E ≤
      (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) * fixedMoment :=
    hoptimal.trans (mul_le_mul_of_nonneg_left hweighted (by positivity))
  have hscaled : threshold ^ r *
        (gaussianFloorTwo * (mesh / (2 * T))) ≤
      threshold ^ r * ((gaussianReal 0 1).restrict Rᶜ).real E :=
    mul_le_mul_of_nonneg_left hmass (pow_nonneg hthreshold.le r)
  have hcontra := hscaled.trans hupper
  apply (not_lt_of_ge ?_) hbudget
  simpa [mul_assoc, mul_left_comm, mul_comm, mesh] using hcontra

/-- **Intrinsic-rank static Choi first-return law.**  The displayed budget is sufficient to exclude
return to the entire finite target dictionary after the common initial return cell. -/
theorem no_forward_pureChoiCircuitReturn_of_gaussianReplicaCrowding
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    {energy : Fin d → ℝ} (hmax : MaximallyProjectiveEnergy energy)
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    {r : ℕ}
    {T δ epsn epsw : ℝ}
    (hTpos : 0 < T) (hδ : 0 < δ)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hepswOne : epsw < 1)
    (hT : epsw / staticChoiSpeed energy ≤ T)
    (hbudget :
      (Module.finrank ℂ
          (replicaTargetSpan r (fun c => (target c).ofLp)) : ℝ) *
        ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
          (replicaActionCrowdingDegree energy r δ : ℝ) *
            ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r) +
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
  have hint : ∀ c, Integrable
      (fun x => finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp (target c).ofLp ^ r)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / staticChoiSpeed energy / T))
          (epsw / staticChoiSpeed energy / T))ᶜ) := by
    intro c
    exact integrable_staticChoi_fidelity_pow hd energy T (target c) (htarget c) r _
  have hmoment : ∀ c,
      (∫ x, finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp (target c).ofLp ^ r
        ∂((gaussianReal 0 1).restrict
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T))ᶜ)) ≤
        (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
          (replicaActionCrowdingDegree energy r δ : ℝ) *
            ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r) +
          Real.exp (-((T * δ) ^ 2) / 2) := by
    intro c
    refine (integral_mono_measure Measure.restrict_le_self ?_ ?_).trans
      (integral_gaussian_staticChoi_fidelity_pow_le_crowding
        hd hmax (target c) (htarget c) r hTpos hδ)
    · filter_upwards with x
      exact pow_nonneg (sq_nonneg _) r
    · simpa using
        (integrable_staticChoi_fidelity_pow hd energy T (target c) (htarget c) r Set.univ)
  simpa only [WithLp.toLp_ofLp] using
    (no_second_capture_of_returnExcised_gaussianOptimalDesignMoment_lt
      (fun u v => pureStateTraceDistance
        (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin d × Fin d))
        (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d × Fin d)))
      (fun t => (staticSpectralChoiVector d t energy).ofLp)
      (fun c => (target c).ofLp) htargetInner
      (staticChoiSpeed_pos energy) hTpos hepsn hgap hT hthreshold
      htriangle hLip hfidelity hint hmoment hbudget)

end RHTower
