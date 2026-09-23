import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentRadialCutoff

/-!
# The renormalized radial finite part of the horizon-mode temporal current

Near the fundamental quasinormal frequency, the exterior radial integral of the temporal current
cut off at tortoise time `L`, plus the two counterterms read off from the horizon jet of the
cleared density profile, converges as `L → -∞`.  The limit is the quotient of an analytic
function by the clearing factor: the two-counterterm endpoint Mellin transform of the patched
profile plus the analytic compact part.  The package also records the horizon jet that determines
the counterterm coefficients and the value of the Mellin part at the quasinormal frequency as an
endpoint limit of the actual profile.
-/

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
  D4BMJointWave D4BMPhysicalModeAction GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- The renormalized radial cutoff of the horizon-mode temporal current near the fundamental
quasinormal frequency. -/
theorem radial_cutoff_package (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) :
    ∃ (b : ℝ) (c₀ c₁ Mel : ℂ → ℂ), 0 < b ∧ b ≤ 1 / 2 ∧
      AnalyticAt ℂ c₀ (physicalFundamentalFrequency q side) ∧
      AnalyticAt ℂ c₁ (physicalFundamentalFrequency q side) ∧
      AnalyticAt ℂ Mel (physicalFundamentalFrequency q side) ∧
      AnalyticAt ℂ (compactPart q branch a zang b) (physicalFundamentalFrequency q side) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ u in 𝓝 (physicalFundamentalFrequency q side), ∀ z ∈ Ioc (0:ℝ) b,
        ‖clearedDensityProfile q branch a zang u z - c₀ u - c₁ u * z‖ ≤ C * z ^ (2 : ℕ)) ∧
      (∀ᶠ u in 𝓝[≠] (physicalFundamentalFrequency q side), Tendsto (fun L : ℝ =>
        (∫ t in L..0, ((tortoiseRadius t:ℂ) ^ (2 : ℕ) - 1) *
          continuedPhysicalTimeAction q branch u a false t zang) +
          (c₀ u * (horizonCoordinate L:ℂ) ^ u / u + c₁ u * (horizonCoordinate L:ℂ) ^ (u + 1) / (u + 1)) /
            reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch))
        atBot (𝓝 ((Mel u + compactPart q branch a zang b u) /
          reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch)))) ∧
      Tendsto (fun ε : ℝ => (∫ z in Ioc ε b, (z:ℂ) ^ (physicalFundamentalFrequency q side - 1) *
          clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z) +
          c₀ (physicalFundamentalFrequency q side) * (ε:ℂ) ^ (physicalFundamentalFrequency q side) /
            physicalFundamentalFrequency q side +
          c₁ (physicalFundamentalFrequency q side) *
            (ε:ℂ) ^ (physicalFundamentalFrequency q side + 1) /
            (physicalFundamentalFrequency q side + 1))
        (𝓝[>] 0) (𝓝 (Mel (physicalFundamentalFrequency q side))) := by
  have hw := physicalFundamentalFrequency_strip q side
  have hwr : -2 < (physicalFundamentalFrequency q side).re := (abs_lt.mp hw.2).1
  have hs0 := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨R, b, hR, -, hb, -, hbh, c₀, c₁, C, M, hC, -, h₀, h₁, -, -, hjet⟩ :=
    (clearedDensityProfile_germ q branch side a zang).exists_bounded one_pos one_half_pos
  have hb1 : b < 1 := by linarith
  have hbI : b ∈ Ioo (0:ℝ) 1 := ⟨hb, hb1⟩
  obtain ⟨RB, CB, hRB, -, hbound⟩ :=
    clearedTemporalDensity_outer_uniform_bound q branch side a zang (tortoiseOf b)
  have hev : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side),
      u.im ≠ 0 ∧ -2 < u.re ∧ u - 2 * physicalRate q branch ≠ 0 ∧
      (∀ i : Fin 3, connection u (principalFrequency q i) ≠ 0) ∧
      AnalyticAt ℂ c₀ u ∧ AnalyticAt ℂ c₁ u ∧
      u ∈ closedBall (physicalFundamentalFrequency q side) R ∧
      u ∈ ball (physicalFundamentalFrequency q side) RB ∧
      ((physicalFundamentalFrequency q side).re - 2) / 2 ≤ u.re := by
    have h3 : ∀ i : Fin 3, ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side),
        connection u (principalFrequency q i) ≠ 0 := fun i =>
      (connection_frequency_analyticAt _ (principalFrequency q i) hw.1).continuousAt.eventually_ne
        (physicalFundamental_principal_connection_ne_zero q side i)
    have hβ : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side),
        ((physicalFundamentalFrequency q side).re - 2) / 2 < u.re :=
      continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (by linarith)
    exact Filter.Eventually.and (Complex.continuous_im.continuousAt.eventually_ne hw.1)
      (Filter.Eventually.and (continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hwr)
      (Filter.Eventually.and ((continuous_id.sub continuous_const).continuousAt.eventually_ne hs0)
      (Filter.Eventually.and (Filter.eventually_all.mpr h3)
      (Filter.Eventually.and h₀.eventually_analyticAt
      (Filter.Eventually.and h₁.eventually_analyticAt
      (Filter.Eventually.and (closedBall_mem_nhds _ hR)
      (Filter.Eventually.and (ball_mem_nhds _ hRB) (hβ.mono (fun u h => h.le)))))))))
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.mp hev
  -- the patched profile and its properties on the ball
  have hm : ∀ u ∈ ball (physicalFundamentalFrequency q side) r,
      Measurable (patchedProfile q branch a zang c₀ b u) := by
    intro u hu
    obtain ⟨hui, hur, -, -, -, -, -, -, -⟩ := hall (mem_ball.mp hu)
    exact patchedProfile_measurable q branch a zang c₀ hbI u hui hur
  have hPan : ∀ z ∈ Ioc (0:ℝ) b, ∀ u ∈ ball (physicalFundamentalFrequency q side) r,
      AnalyticAt ℂ (fun v => clearedDensityProfile q branch a zang v z) u := by
    intro z hz u hu
    obtain ⟨hui, hur, hus, hcp, -, -, -, -, -⟩ := hall (mem_ball.mp hu)
    have hzI : z ∈ Ioo (0:ℝ) 1 := ⟨hz.1, hz.2.trans_lt hb1⟩
    have hz0 : (z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
    have hpow : AnalyticAt ℂ (fun v : ℂ => (z:ℂ) ^ v) u := by
      have hd : Differentiable ℂ (fun v : ℂ => (z:ℂ) ^ v) :=
        fun v => differentiableAt_id.const_cpow (Or.inl hz0)
      exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd) u (mem_univ _)
    have hpow0 : (z:ℂ) ^ u ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hA : AnalyticAt ℂ (fun v => clearedTemporalDensity q branch a zang v (tortoiseOf z) /
        (z:ℂ) ^ v * ((Real.sqrt (1 - z) : ℂ))⁻¹ / 2) u :=
      (((clearedTemporalDensity_frequency_analyticAt q branch a zang u hui hur hus hcp
        (tortoiseOf z) (tortoiseOf_neg hzI)).div hpow hpow0).mul analyticAt_const).div
        analyticAt_const (by norm_num)
    refine hA.congr (Filter.Eventually.of_forall (fun v => ?_))
    simp only [clearedDensityProfile, clearedDensityCore_eq_density q branch a zang v hzI]
  have hd : ∀ t ∈ Icc (0:ℝ) b, ∀ u ∈ ball (physicalFundamentalFrequency q side) r,
      DifferentiableAt ℂ (fun v => patchedProfile q branch a zang c₀ b v t) u := by
    intro t ht u hu
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      simp only [patchedProfile_zero]
      exact (hall (mem_ball.mp hu)).2.2.2.2.1.differentiableAt
    · have htI : t ∈ Ioc (0:ℝ) b := ⟨hpos, ht.2⟩
      have he : (fun v => patchedProfile q branch a zang c₀ b v t) =
          fun v => clearedDensityProfile q branch a zang v t :=
        funext (fun v => patchedProfile_of_mem q branch a zang c₀ b v htI)
      rw [he]
      exact (hPan t htI u hu).differentiableAt
  have hC' : ∀ u ∈ ball (physicalFundamentalFrequency q side) r, ∀ t ∈ Ioc (0:ℝ) b,
      ‖patchedProfile q branch a zang c₀ b u t - patchedProfile q branch a zang c₀ b u 0 -
        c₁ u * t‖ ≤ C * t ^ (2 : ℕ) := by
    intro u hu t ht
    rw [patchedProfile_of_mem q branch a zang c₀ b u ht, patchedProfile_zero]
    exact hjet u (hall (mem_ball.mp hu)).2.2.2.2.2.2.1 t ht
  have hne0 : ∀ u ∈ ball (physicalFundamentalFrequency q side) r, u ≠ 0 := by
    intro u hu he
    exact (hall (mem_ball.mp hu)).1 (by simp [he])
  have hne1 : ∀ u ∈ ball (physicalFundamentalFrequency q side) r, u + 1 ≠ 0 := by
    intro u hu he
    apply (hall (mem_ball.mp hu)).1
    have := congrArg Complex.im he
    simpa using this
  have hMel : AnalyticAt ℂ (secondEndpointMellin (patchedProfile q branch a zang c₀ b) c₁ b)
      (physicalFundamentalFrequency q side) :=
    secondEndpointMellin_analyticAt hb hb1.le hr hC (by linarith)
      (fun u hu => (hall (mem_ball.mp hu)).2.2.2.2.2.2.2.2) hm hd
      (fun u hu => (hall (mem_ball.mp hu)).2.2.2.2.2.1.differentiableAt) hC' hne0 hne1
  refine ⟨b, c₀, c₁, secondEndpointMellin (patchedProfile q branch a zang c₀ b) c₁ b, hb, hbh,
    h₀, h₁, hMel, compactPart_analyticAt q branch side a zang b, ⟨C, hC, ?_⟩, ?_, ?_⟩
  · filter_upwards [closedBall_mem_nhds (physicalFundamentalFrequency q side) hR] with u hu
    exact hjet u hu
  · have hev' : ∀ᶠ u in 𝓝[≠] (physicalFundamentalFrequency q side),
        u ∈ ball (physicalFundamentalFrequency q side) r :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hr)
    filter_upwards [hev', connection_eventually_ne_zero _ (physicalRadialFrequency q) hw.1]
      with u hu hcu
    obtain ⟨hui, hur, hus, -, -, -, -, huB, -⟩ := hall (mem_ball.mp hu)
    have hM := secondEndpointMellin_cutoff_tendsto (F := patchedProfile q branch a zang c₀ b)
      (F₁ := c₁) (w := u) (b := b) (C := C) hb hur (hne0 u hu) (hne1 u hu) (hm u hu) (hC' u hu)
    have hcomp := hM.comp D4BMFundamentalNorm.horizonCoordinate_tendsto_positive
    have h2 := (hcomp.add (tendsto_const_nhds (x := compactPart q branch a zang b u))).div_const
      (reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch))
    refine h2.congr' ?_
    filter_upwards [eventually_lt_atBot (tortoiseOf b)] with L hL
    rw [cutoff_integral_split q branch a zang c₀ hbI u hui hur hus hcu (hbound u huB) hL]
    simp only [Function.comp_apply, patchedProfile_zero]
    ring
  · have hM0 := secondEndpointMellin_cutoff_tendsto (F := patchedProfile q branch a zang c₀ b)
      (F₁ := c₁) (w := physicalFundamentalFrequency q side) (b := b) (C := C) hb hwr
      (hne0 _ (mem_ball_self hr)) (hne1 _ (mem_ball_self hr)) (hm _ (mem_ball_self hr))
      (hC' _ (mem_ball_self hr))
    refine hM0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hI : (∫ z in Ioc ε b, (z:ℂ) ^ (physicalFundamentalFrequency q side - 1) *
        patchedProfile q branch a zang c₀ b (physicalFundamentalFrequency q side) z) =
        ∫ z in Ioc ε b, (z:ℂ) ^ (physicalFundamentalFrequency q side - 1) *
          clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro z hz
      dsimp only
      rw [patchedProfile_of_mem q branch a zang c₀ b _ ⟨(mem_Ioi.mp hε).trans hz.1, hz.2⟩]
    rw [hI, patchedProfile_zero]

end
end RHTower.D4BMJointSource
