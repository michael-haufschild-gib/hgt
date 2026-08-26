import GaloisForLFunctions.HTGeometry.FullProjectiveReplicaMomentWindowLaw
import GaloisForLFunctions.RHTower.StaticChoiOptimalDesignWeightedCrowdingFirstReturnLaw
import GaloisForLFunctions.RHTower.FullProjectiveChoiFirstReturnLaw

open scoped BigOperators Interval
open Set MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

variable {n : ℕ}

theorem neg_projectiveFrequencyEnergy_clockScaledFullProjective
    (g : ℝ) (y : Fin n → ℝ) :
    (fun i => -projectiveFrequencyEnergy
        (clockScaledFullProjectiveFrequency g y) i) =
      fun i => g * anchoredFullProjectiveFrequency y i := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [projectiveFrequencyEnergy, anchoredFullProjectiveFrequency]
  · simp [projectiveFrequencyEnergy, clockScaledFullProjectiveFrequency,
      anchoredFullProjectiveFrequency]

/-- Uniform full-projective physical-window moment against every normalized
Choi target. Target choice and growing replica order share one constant. -/
theorem exists_uniform_windowMean_staticChoiTarget_fullProjective_le
    {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {eps : ℝ} (heps : 0 < eps) {g : ℝ} (hg : 0 < g) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (target : EuclideanSpace ℂ (Fin (n + 2) × Fin (n + 2))),
        ‖target‖ = 1 → ∀ (r : ℕ) (u T : ℝ), 0 < T →
          (1 / T) * ∫ t in u..(u + T),
              finitePureStateFidelity
                (staticSpectralChoiVector (n + 2) t
                  (projectiveFrequencyEnergy
                    (clockScaledFullProjectiveFrequency g y))).ofLp
                target.ofLp ^ r ≤
            (r.factorial : ℝ) * ((n + 2 : ℕ) : ℝ)⁻¹ ^ r +
              (2 * C / (g * T)) *
                (4 : ℝ) ^ ((r : ℝ) * (1 + eps)) := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_uniform_windowMean_twistedFidelity_clockScaledFullProjective_le
      hy heps hg
  refine ⟨C, hC, ?_⟩
  intro target htarget r u T hT
  let energy : Fin (n + 2) → ℝ :=
    projectiveFrequencyEnergy (clockScaledFullProjectiveFrequency g y)
  let weight := directStaticChoiTargetWeight (n + 2) target
  let twist := directStaticChoiTargetTwist target
  have hm := hmoment weight twist r
    (directStaticChoiTargetWeight_nonneg target)
    (sum_directStaticChoiTargetWeight_le_one (by omega) htarget)
    (norm_directStaticChoiTargetTwist target) u T hT
  have henergy : (fun i => -energy i) =
      fun i => g * anchoredFullProjectiveFrequency y i := by
    exact neg_projectiveFrequencyEnergy_clockScaledFullProjective g y
  have hpoint : ∀ t : ℝ,
      (((finitePureStateFidelity
          (staticSpectralChoiVector (n + 2) t energy).ofLp target.ofLp ^ r : ℝ) : ℂ)) =
        twistedFiniteSpectralFidelity weight
          (fun i => g * anchoredFullProjectiveFrequency y i) twist t ^ r := by
    intro t
    push_cast
    rw [← henergy]
    exact congrArg (fun z : ℂ => z ^ r)
      (staticChoi_fidelity_eq_directTwistedFidelity t energy target)
  have hcont : Continuous fun t : ℝ =>
      finitePureStateFidelity
        (staticSpectralChoiVector (n + 2) t energy).ofLp target.ofLp ^ r := by
    have hstate : Continuous fun t : ℝ =>
        staticSpectralChoiVector (n + 2) t energy := by
      simpa only [one_mul] using
        (continuous_staticSpectralChoiVector_scaled (by omega) energy 1)
    simp_rw [finitePureStateFidelity_eq_norm_inner_sq]
    simp only [WithLp.toLp_ofLp]
    exact ((Continuous.inner continuous_const hstate).norm.pow 2).pow r
  have hint : IntervalIntegrable (fun t : ℝ =>
      finitePureStateFidelity
        (staticSpectralChoiVector (n + 2) t energy).ofLp target.ofLp ^ r)
      volume u (u + T) := hcont.intervalIntegrable u (u + T)
  have hcast := Complex.ofRealCLM.intervalIntegral_comp_comm hint
  have hmean :
      (((1 / T) * ∫ t in u..(u + T),
          finitePureStateFidelity
            (staticSpectralChoiVector (n + 2) t energy).ofLp target.ofLp ^ r : ℝ) : ℂ) =
        (1 / (T : ℂ)) * ∫ t in u..(u + T),
          twistedFiniteSpectralFidelity weight
            (fun i => g * anchoredFullProjectiveFrequency y i) twist t ^ r := by
    have hcast' :
        (((∫ t in u..(u + T),
          finitePureStateFidelity
            (staticSpectralChoiVector (n + 2) t energy).ofLp target.ofLp ^ r : ℝ) : ℂ)) =
          ∫ t in u..(u + T),
            (((finitePureStateFidelity
              (staticSpectralChoiVector (n + 2) t energy).ofLp target.ofLp ^ r : ℝ) : ℂ)) := by
      simpa using hcast.symm
    calc
      _ = (1 / (T : ℂ)) * (((∫ t in u..(u + T),
          finitePureStateFidelity
            (staticSpectralChoiVector (n + 2) t energy).ofLp target.ofLp ^ r : ℝ) : ℂ)) := by
        push_cast
        rfl
      _ = (1 / (T : ℂ)) * ∫ t in u..(u + T),
          (((finitePureStateFidelity
            (staticSpectralChoiVector (n + 2) t energy).ofLp target.ofLp ^ r : ℝ) : ℂ)) := by
        rw [hcast']
      _ = _ := by
        congr 1
        exact intervalIntegral.integral_congr fun t _ => hpoint t
  have hnonneg : 0 ≤ (1 / T) * ∫ t in u..(u + T),
      finitePureStateFidelity
        (staticSpectralChoiVector (n + 2) t energy).ofLp target.ofLp ^ r := by
    apply mul_nonneg
    · positivity
    · exact intervalIntegral.integral_nonneg (by linarith) fun t _ => by
        rw [finitePureStateFidelity_eq_norm_inner_sq]
        apply pow_nonneg
        exact sq_nonneg _
  have hreal :
      (1 / T) * ∫ t in u..(u + T),
          finitePureStateFidelity
            (staticSpectralChoiVector (n + 2) t energy).ofLp target.ofLp ^ r =
        ‖(1 / (T : ℂ)) * ∫ t in u..(u + T),
          twistedFiniteSpectralFidelity weight
            (fun i => g * anchoredFullProjectiveFrequency y i) twist t ^ r‖ := by
    rw [← hmean, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [show projectiveFrequencyEnergy
      (clockScaledFullProjectiveFrequency g y) = energy by rfl, hreal]
  calc
    _ ≤ (r.factorial : ℝ) * (∑ i, weight i ^ 2) ^ r +
        (2 * C / (g * T)) *
          (4 : ℝ) ^ ((r : ℝ) * (1 + eps)) := hm
    _ ≤ (r.factorial : ℝ) * ((n + 2 : ℕ) : ℝ)⁻¹ ^ r +
        (2 * C / (g * T)) *
          (4 : ℝ) ^ ((r : ℝ) * (1 + eps)) := by
      gcongr
      exact sum_sq_directStaticChoiTargetWeight_le_inv (by omega) htarget

set_option maxHeartbeats 800000 in
/-- Complete finite target union with target cardinality replaced by occupied
replica-span rank. All target moments use one quenched Diophantine constant. -/
theorem exists_uniform_fullProjectiveChoi_optimalDesignOccupation_le
    {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {eps : ℝ} (heps : 0 < eps) {g : ℝ} (hg : 0 < g) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
        (target : C → EuclideanSpace ℂ (Fin (n + 2) × Fin (n + 2)))
        (htarget : ∀ c, ‖target c‖ = 1)
        (r : ℕ) {threshold u T : ℝ}, 0 < threshold → 0 < T →
        ((volume.restrict (Ioc u (u + T))).real
          {t | ∃ c, threshold ≤ finitePureStateFidelity
            (staticSpectralChoiVector (n + 2) t
              (projectiveFrequencyEnergy
                (clockScaledFullProjectiveFrequency g y))).ofLp
            (target c).ofLp}) ≤
          (Module.finrank ℂ
            (replicaTargetSpan r (fun c => (target c).ofLp)) : ℝ) * T *
            ((r.factorial : ℝ) * ((n + 2 : ℕ) : ℝ)⁻¹ ^ r +
              (2 * C0 / (g * T)) *
                (4 : ℝ) ^ ((r : ℝ) * (1 + eps))) /
              threshold ^ r := by
  obtain ⟨C0, hC0, hsingle⟩ :=
    exists_uniform_windowMean_staticChoiTarget_fullProjective_le hy heps hg
  refine ⟨C0, hC0, ?_⟩
  intro C _ _ _ target htarget r threshold u T hthreshold hT
  let energy : Fin (n + 2) → ℝ :=
    projectiveFrequencyEnergy (clockScaledFullProjectiveFrequency g y)
  let μ : Measure ℝ := volume.restrict (Ioc u (u + T))
  let state : ℝ → (Fin (n + 2) × Fin (n + 2)) → ℂ :=
    fun t => (staticSpectralChoiVector (n + 2) t energy).ofLp
  have htargetInner : ∀ c,
      finiteComplexInner (target c).ofLp (target c).ofLp = 1 := by
    intro c
    rw [← inner_toLp_eq_finiteComplexInner]
    simp only [WithLp.toLp_ofLp]
    rw [inner_self_eq_norm_sq_to_K, htarget]
    norm_num
  have hcont : ∀ c, Continuous fun t : ℝ =>
      finitePureStateFidelity (state t) (target c).ofLp ^ r := by
    intro c
    have hstate : Continuous fun t : ℝ =>
        staticSpectralChoiVector (n + 2) t energy := by
      simpa only [one_mul] using
        (continuous_staticSpectralChoiVector_scaled (by omega) energy 1)
    simp_rw [finitePureStateFidelity_eq_norm_inner_sq]
    simp only [state, WithLp.toLp_ofLp]
    exact ((Continuous.inner continuous_const hstate).norm.pow 2).pow r
  have hint : ∀ c, Integrable
      (fun t => finitePureStateFidelity (state t) (target c).ofLp ^ r) μ := by
    intro c
    exact (hcont c).integrableOn_Ioc
  let w := staticChoiTargetOptimalDesignWeight r target htarget
  have hw : w ∈ stdSimplex ℝ C := by
    exact staticChoiTargetOptimalDesignWeight_mem_stdSimplex r target htarget
  have hdesign : ∀ (ψ : (Fin (n + 2) × Fin (n + 2)) → ℂ) (c : C),
      finitePureStateFidelity ψ (target c).ofLp ^ r ≤
        (Module.finrank ℂ
          (replicaTargetSpan r (fun j => (target j).ofLp)) : ℝ) *
          ∑ j, w j * finitePureStateFidelity ψ (target j).ofLp ^ r := by
    intro ψ c
    exact staticChoiTargetOptimalDesignWeight_pointwise r target htarget ψ c
  have hintEmpty : ∀ c, Integrable
      (fun t => finitePureStateFidelity (state t) (target c).ofLp ^ r)
        (μ.restrict (∅ : Set ℝ)ᶜ) := by
    intro c
    simpa only [compl_empty, Measure.restrict_univ] using hint c
  have hcoarea := measure_completeTargetCapture_restrict_le_designMoments
    (r := r) μ (fun c => (target c).ofLp) state threshold hthreshold
    (∅ : Set ℝ) w hw hdesign hintEmpty
  have hsingleInt : ∀ c,
      (∫ t, finitePureStateFidelity (state t) (target c).ofLp ^ r ∂μ) ≤
        T * ((r.factorial : ℝ) * ((n + 2 : ℕ) : ℝ)⁻¹ ^ r +
          (2 * C0 / (g * T)) *
            (4 : ℝ) ^ ((r : ℝ) * (1 + eps))) := by
    intro c
    have hs := hsingle (target c) (htarget c) r u T hT
    have hmul := mul_le_mul_of_nonneg_left hs hT.le
    change (∫ t in Ioc u (u + T),
      finitePureStateFidelity (state t) (target c).ofLp ^ r) ≤ _
    rw [← intervalIntegral.integral_of_le (by linarith : u ≤ u + T)]
    calc
      (∫ t in u..(u + T),
          finitePureStateFidelity (state t) (target c).ofLp ^ r) =
        T * ((1 / T) * ∫ t in u..(u + T),
          finitePureStateFidelity (state t) (target c).ofLp ^ r) := by
            field_simp
      _ ≤ _ := by
        simpa only [state, energy] using hmul
  have hweighted :
      (∑ c, w c * ∫ t,
        finitePureStateFidelity (state t) (target c).ofLp ^ r ∂μ) ≤
        T * ((r.factorial : ℝ) * ((n + 2 : ℕ) : ℝ)⁻¹ ^ r +
          (2 * C0 / (g * T)) *
            (4 : ℝ) ^ ((r : ℝ) * (1 + eps))) := by
    calc
      _ ≤ ∑ c, w c *
          (T * ((r.factorial : ℝ) * ((n + 2 : ℕ) : ℝ)⁻¹ ^ r +
            (2 * C0 / (g * T)) *
              (4 : ℝ) ^ ((r : ℝ) * (1 + eps)))) :=
        Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hsingleInt c) (hw.1 c)
      _ = _ := by
        rw [← Finset.sum_mul, hw.2, one_mul]
  have hcoarea' :
      threshold ^ r * μ.real {t | ∃ c,
          threshold ≤ finitePureStateFidelity (state t) (target c).ofLp} ≤
        (Module.finrank ℂ
          (replicaTargetSpan r (fun c => (target c).ofLp)) : ℝ) *
          ∑ c, w c * ∫ t,
            finitePureStateFidelity (state t) (target c).ofLp ^ r ∂μ := by
    simpa only [compl_empty, Measure.restrict_univ] using hcoarea
  have hbound := hcoarea'.trans
    (mul_le_mul_of_nonneg_left hweighted (by positivity))
  rw [le_div_iff₀ (pow_pos hthreshold r)]
  convert hbound using 1 <;> ring

set_option maxHeartbeats 800000 in
/-- Continuous first-reentry dichotomy for the complete finite target family.
Either the explicit occupied-rank replica budget already consumes the
geometrically mandatory initial-plus-return width, or no narrow re-entry
occurs anywhere in the entire displayed post-ramp interval. -/
theorem exists_uniform_fullProjectiveChoi_initialExclusion_or_budgetObstruction
    {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {eps : ℝ} (heps : 0 < eps) {g : ℝ} (hg : 0 < g) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
        (target : C → EuclideanSpace ℂ (Fin (n + 2) × Fin (n + 2)))
        (htarget : ∀ c, ‖target c‖ = 1) (identity : C),
        target identity = staticSpectralChoiVector (n + 2) 0
          (projectiveFrequencyEnergy
            (clockScaledFullProjectiveFrequency g y)) →
        ∀ (r : ℕ) {epsn epsw T : ℝ},
          0 ≤ epsn → epsn < epsw → epsw < 1 →
          epsw / staticChoiSpeed
            (projectiveFrequencyEnergy
              (clockScaledFullProjectiveFrequency g y)) ≤ T →
          2 * (epsw / staticChoiSpeed
                (projectiveFrequencyEnergy
                  (clockScaledFullProjectiveFrequency g y))) +
              (epsw - epsn) / staticChoiSpeed
                (projectiveFrequencyEnergy
                  (clockScaledFullProjectiveFrequency g y)) ≤
            (Module.finrank ℂ
              (replicaTargetSpan r (fun c => (target c).ofLp)) : ℝ) *
              (2 * T) *
              ((r.factorial : ℝ) * ((n + 2 : ℕ) : ℝ)⁻¹ ^ r +
                (2 * C0 / (g * (2 * T))) *
                  (4 : ℝ) ^ ((r : ℝ) * (1 + eps))) /
                (1 - epsw ^ 2) ^ r ∨
          ¬ ∃ t ∈ Icc
              (epsw / staticChoiSpeed
                  (projectiveFrequencyEnergy
                    (clockScaledFullProjectiveFrequency g y)) +
                (epsw - epsn) / staticChoiSpeed
                  (projectiveFrequencyEnergy
                    (clockScaledFullProjectiveFrequency g y))) T,
            ∃ c, pureStateTraceDistance
              (staticSpectralChoiVector (n + 2) t
                (projectiveFrequencyEnergy
                  (clockScaledFullProjectiveFrequency g y)))
              (target c) ≤ epsn := by
  obtain ⟨C0, hC0, hoccupation⟩ :=
    exists_uniform_fullProjectiveChoi_optimalDesignOccupation_le hy heps hg
  refine ⟨C0, hC0, ?_⟩
  intro C _ _ _ target htarget identity hidentity r epsn epsw T
    hepsn hgap hepswOne honset
  let energy : Fin (n + 2) → ℝ :=
    projectiveFrequencyEnergy (clockScaledFullProjectiveFrequency g y)
  let threshold : ℝ := 1 - epsw ^ 2
  let width : ℝ := 2 * (epsw / staticChoiSpeed energy) +
    (epsw - epsn) / staticChoiSpeed energy
  let budget : ℝ :=
    (Module.finrank ℂ
      (replicaTargetSpan r (fun c => (target c).ofLp)) : ℝ) *
      (2 * T) *
      ((r.factorial : ℝ) * ((n + 2 : ℕ) : ℝ)⁻¹ ^ r +
        (2 * C0 / (g * (2 * T))) *
          (4 : ℝ) ^ ((r : ℝ) * (1 + eps))) / threshold ^ r
  have hd : 0 < n + 2 := by omega
  have hspeed : 0 < staticChoiSpeed energy := staticChoiSpeed_pos energy
  have hepsw : 0 < epsw := lt_of_le_of_lt hepsn hgap
  have hTpos : 0 < T := lt_of_lt_of_le (div_pos hepsw hspeed) honset
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    nlinarith [sq_nonneg epsw]
  have hoccupation' := hoccupation target htarget r hthreshold
    (u := -T) (T := 2 * T) (by positivity)
  rw [show -T + 2 * T = T by ring] at hoccupation'
  let fidelityCapture : Set ℝ := {t | ∃ c, threshold ≤
    finitePureStateFidelity
      (staticSpectralChoiVector (n + 2) t energy).ofLp (target c).ofLp}
  have hoccupationReal :
      volume.real (fidelityCapture ∩ Ioc (-T) T) ≤ budget := by
    rw [Measure.real, Measure.restrict_apply' measurableSet_Ioc] at hoccupation'
    simpa only [Measure.real, fidelityCapture, energy, budget] using hoccupation'
  by_cases hbudget : width ≤ budget
  · left
    simpa only [width, budget, threshold, energy] using hbudget
  · right
    have hbudgetLt : budget < width := lt_of_not_ge hbudget
    have hfidelity : ∀ t c,
        pureStateTraceDistance
            (staticSpectralChoiVector (n + 2) t energy) (target c) ≤ epsw →
          threshold ≤ finitePureStateFidelity
            (staticSpectralChoiVector (n + 2) t energy).ofLp (target c).ofLp := by
      intro t c hdist
      dsimp [threshold]
      rw [finitePureStateFidelity_eq_norm_inner_sq]
      simp only [WithLp.toLp_ofLp]
      rw [norm_inner_symm]
      have hsq := sq_pureStateTraceDistance
        (staticSpectralChoiVector (n + 2) t energy) (target c)
        (by rw [staticSpectralChoiVector_norm hd])
        (by rw [htarget c])
      have hdistSq : pureStateTraceDistance
          (staticSpectralChoiVector (n + 2) t energy) (target c) ^ 2 ≤ epsw ^ 2 :=
        (sq_le_sq₀ (pureStateTraceDistance_nonneg _ _) hepsw.le).2 hdist
      nlinarith
    let wide : Set ℝ := {t | t ∈ Ioc (-T) T ∧ ∃ c,
      pureStateTraceDistance
        (staticSpectralChoiVector (n + 2) t energy) (target c) ≤ epsw}
    have hwideSub : wide ⊆ fidelityCapture ∩ Ioc (-T) T := by
      intro t ht
      rcases ht with ⟨htI, c, hc⟩
      exact ⟨⟨c, hfidelity t c hc⟩, htI⟩
    have hfinite : volume (fidelityCapture ∩ Ioc (-T) T) ≠ ⊤ :=
      ne_top_of_le_ne_top measure_Ioc_lt_top.ne
        (measure_mono inter_subset_right)
    have hwide : volume.real wide < width :=
      (measureReal_mono hwideSub hfinite).trans_lt
        (hoccupationReal.trans_lt hbudgetLt)
    have htriangle : ∀ t u c,
        pureStateTraceDistance
            (staticSpectralChoiVector (n + 2) t energy) (target c) ≤
          pureStateTraceDistance
              (staticSpectralChoiVector (n + 2) t energy)
              (staticSpectralChoiVector (n + 2) u energy) +
            pureStateTraceDistance
              (staticSpectralChoiVector (n + 2) u energy) (target c) := by
      intro t u c
      exact pureStateTraceDistance_triangle
        (staticSpectralChoiVector (n + 2) t energy)
        (staticSpectralChoiVector (n + 2) u energy) (target c)
        (staticSpectralChoiVector_norm hd t energy)
        (staticSpectralChoiVector_norm hd u energy) (htarget c)
    have hLip : ∀ t u,
        pureStateTraceDistance
            (staticSpectralChoiVector (n + 2) t energy)
            (staticSpectralChoiVector (n + 2) u energy) ≤
          staticChoiSpeed energy * |t - u| :=
      pureStateTraceDistance_staticSpectralChoiVector_time_le hd energy
    have hno := no_second_capture_of_wide_occupation_lt
      pureStateTraceDistance
      (fun t => staticSpectralChoiVector (n + 2) t energy)
      target identity hspeed hepsn hgap honset
      (by simpa only [energy] using hidentity)
      htriangle hLip (by simpa only [wide] using hwide)
    simpa only [energy] using hno

end RHTower
