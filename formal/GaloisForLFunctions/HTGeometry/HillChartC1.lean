import GaloisForLFunctions.HTGeometry.HillChartPartials
import GaloisForLFunctions.HTGeometry.KleinGordonChartC1

/-!
# The chart field of the evolution has continuous partial derivatives

Each coordinate partial of the chart field is the real part of a synthesis: the time partial
synthesises the velocity density, a spatial partial synthesises the derived density. Both syntheses
are dominated near an event by a fixed integrable function — the exponential factor of the energy
estimate is uniform on a unit time ball, and the speed is bounded below — so both are continuous in
the event.

Hence the chart field satisfies the corpus's condition for being differentiable with the expected
differential, and its coordinate partials are the computed ones.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Metric

open scoped RealInnerProductSpace

section ChartC1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m K C cmin : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ}

/-! ## The velocity density -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The velocity density is continuous in the frequency**, at every time. -/
theorem continuous_hillDensityDeriv_all (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀) (t : ℝ) :
    Continuous (hillDensityDeriv m c G₀ t) := by
  have hfibre : Continuous fun s : ℝ => hillFlow (massiveFreq m c s) (1, 0) t :=
    continuous_iff_continuousAt.mpr fun s₀ =>
      continuousAt_hillFlow_massive_all (C := C) hm hc hC (1, 0) t s₀
  have hscalar : Continuous fun s : ℝ => hillSolutionDeriv (massiveFreq m c s) (1, 0) t :=
    continuous_snd.comp hfibre
  exact (Complex.continuous_ofReal.comp (hscalar.comp continuous_norm)).mul hG

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The velocity density is continuous in time.** -/
theorem continuous_hillDensityDeriv_time (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (ξ : E) :
    Continuous fun t : ℝ => hillDensityDeriv m c G₀ t ξ := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c ‖ξ‖ r ^ (2 : ℕ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) := fun r =>
    (massiveFreq_sq_le hm hC le_rfl r).trans (le_max_right _ _)
  have hflow : Continuous (hillFlow (massiveFreq m c ‖ξ‖) (1, 0)) :=
    continuous_hillFlow (continuous_massiveFreq hc m ‖ξ‖) hM1 hMb (1, 0)
  exact (Complex.continuous_ofReal.comp (continuous_snd.comp hflow)).mul continuous_const

/-! ## The two syntheses are continuous in the event -/

/-- Any two nearby times have comparable absolute values. -/
theorem abs_le_abs_add_one_of_dist_lt {t₀ r : ℝ} (h : dist r t₀ < 1) : |r| ≤ |t₀| + 1 := by
  have h1 : |r - t₀| < 1 := by simpa [Real.dist_eq] using h
  have hpair := abs_lt.mp h1
  cases abs_cases r with
  | inl h => cases abs_cases t₀ with
    | inl h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
    | inr h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
  | inr h => cases abs_cases t₀ with
    | inl h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
    | inr h2 => linarith [h.1, h2.1, hpair.1, hpair.2]

/-- **The synthesis of the velocity density is continuous in the event.** -/
theorem continuous_hillSynthesisDeriv_event (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (hweight : Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) (volume : Measure E)) :
    Continuous fun p : ℝ × E =>
      hillSynthesisDeriv m c G₀ (kgChar p.2) (volume : Measure E) p.1 := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc 0| := abs_nonneg _
    have h1 := hK 0
    have h2 := hcpos 0
    nlinarith
  refine continuous_iff_continuousAt.mpr fun p₀ => ?_
  obtain ⟨t₀, x₀⟩ := p₀
  simp only [hillSynthesisDeriv]
  have hFmeas : ∀ᶠ p : ℝ × E in nhds (t₀, x₀),
      AEStronglyMeasurable (fun ξ : E => kgChar p.2 ξ * hillDensityDeriv m c G₀ p.1 ξ)
        (volume : Measure E) := by
    filter_upwards with p
    exact ((continuous_kgChar' p.2).aestronglyMeasurable).mul
      (continuous_hillDensityDeriv_all (C := C) hm hc hC hG p.1).aestronglyMeasurable
  have hbound : ∀ᶠ p : ℝ × E in nhds (t₀, x₀), ∀ᵐ ξ : E ∂(volume : Measure E),
      ‖kgChar p.2 ξ * hillDensityDeriv m c G₀ p.1 ξ‖
        ≤ Real.exp (K * (|t₀| + 1)) * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) := by
    have hball : ball ((t₀, x₀) : ℝ × E) 1 ∈ nhds ((t₀, x₀) : ℝ × E) := ball_mem_nhds _ one_pos
    filter_upwards [hball] with p hp
    have hdist : dist p.1 t₀ < 1 := lt_of_le_of_lt (le_max_left _ _) hp
    have habs : |p.1| ≤ |t₀| + 1 := abs_le_abs_add_one_of_dist_lt hdist
    filter_upwards with ξ
    have hbase := norm_hillDensityDeriv_le_abs (G₀ := G₀) hm hc hcd hcpos hK hC p.1 ξ
    have hfreq := massiveFreq_zero_le (c := c) hm hcpos ξ
    have hmf : (0 : ℝ) ≤ massiveFreq m c ‖ξ‖ 0 := le_of_lt (massiveFreq_pos hm c ‖ξ‖ 0)
    have hsum : (0 : ℝ) ≤ m + c 0 * ‖ξ‖ := le_trans hmf hfreq
    have hexp : Real.exp (K * |p.1|) ≤ Real.exp (K * (|t₀| + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hK0)
    calc ‖kgChar p.2 ξ * hillDensityDeriv m c G₀ p.1 ξ‖
        = ‖hillDensityDeriv m c G₀ p.1 ξ‖ := by rw [norm_mul, norm_kgChar, one_mul]
      _ ≤ (massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |p.1|)) * ‖G₀ ξ‖ := hbase
      _ ≤ ((m + c 0 * ‖ξ‖) * Real.exp (K * (|t₀| + 1))) * ‖G₀ ξ‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hfreq hexp (le_of_lt (Real.exp_pos _)) hsum) (norm_nonneg _)
      _ = Real.exp (K * (|t₀| + 1)) * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) := by ring
  have hcont : ∀ᵐ ξ : E ∂(volume : Measure E),
      ContinuousAt (fun p : ℝ × E => kgChar p.2 ξ * hillDensityDeriv m c G₀ p.1 ξ) (t₀, x₀) := by
    filter_upwards with ξ
    have h1 : Continuous fun p : ℝ × E => kgChar p.2 ξ :=
      (continuous_kgChar_point ξ).comp continuous_snd
    have h2 : Continuous fun p : ℝ × E => hillDensityDeriv m c G₀ p.1 ξ :=
      (continuous_hillDensityDeriv_time (C := C) hm hc hC ξ).comp continuous_fst
    exact (h1.mul h2).continuousAt
  exact continuousAt_of_dominated hFmeas hbound
    (hweight.const_mul (Real.exp (K * (|t₀| + 1)))) hcont

/-- **The synthesis of a derived density is continuous in the event.** -/
theorem continuous_hillDirSynthesis_event (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r)
    (hG : Continuous G₀)
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖G₀ ξ‖) (volume : Measure E)) (v : E) :
    Continuous fun p : ℝ × E =>
      kgSynthesis (kgDirDensity v (hillDensity m c G₀ p.1)) p.2 := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc 0| := abs_nonneg _
    have hk1 := hK 0
    have h2 := hcpos 0
    nlinarith
  refine continuous_iff_continuousAt.mpr fun p₀ => ?_
  obtain ⟨t₀, x₀⟩ := p₀
  simp only [kgSynthesis]
  set R : ℝ := max 1 (c 0 / cmin) * Real.exp (K * (|t₀| + 1)) with hR
  have hRnonneg : (0 : ℝ) ≤ R := by
    have hone : (0 : ℝ) ≤ max 1 (c 0 / cmin) := le_trans zero_le_one (le_max_left _ _)
    exact mul_nonneg hone (le_of_lt (Real.exp_pos _))
  have hFmeas : ∀ᶠ p : ℝ × E in nhds (t₀, x₀),
      AEStronglyMeasurable
        (fun ξ : E => kgChar p.2 ξ * kgDirDensity v (hillDensity m c G₀ p.1) ξ)
        (volume : Measure E) := by
    filter_upwards with p
    exact ((continuous_kgChar' p.2).aestronglyMeasurable).mul
      (aestronglyMeasurable_kgDirDensity
        (aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG p.1 _) v)
  have hbound : ∀ᶠ p : ℝ × E in nhds (t₀, x₀), ∀ᵐ ξ : E ∂(volume : Measure E),
      ‖kgChar p.2 ξ * kgDirDensity v (hillDensity m c G₀ p.1) ξ‖
        ≤ 2 * Real.pi * ‖v‖ * R * (kgFreq ξ * ‖G₀ ξ‖) := by
    have hball : ball ((t₀, x₀) : ℝ × E) 1 ∈ nhds ((t₀, x₀) : ℝ × E) := ball_mem_nhds _ one_pos
    filter_upwards [hball] with p hp
    have hdist : dist p.1 t₀ < 1 := lt_of_le_of_lt (le_max_left _ _) hp
    have habs : |p.1| ≤ |t₀| + 1 := abs_le_abs_add_one_of_dist_lt hdist
    filter_upwards with ξ
    have hden := norm_hillDensity_le_abs (G₀ := G₀) hm hc hcd hcpos hK hC p.1 ξ
    have hratio : max 1 (c 0 / c p.1) ≤ max 1 (c 0 / cmin) :=
      max_le_max le_rfl (div_le_div_of_nonneg_left (le_of_lt (hcpos 0)) hcmin (hclow p.1))
    have hexp : Real.exp (K * |p.1|) ≤ Real.exp (K * (|t₀| + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hK0)
    have hstep : max 1 (c 0 / c p.1) * Real.exp (K * |p.1|) ≤ R :=
      mul_le_mul hratio hexp (le_of_lt (Real.exp_pos _)) (le_trans zero_le_one (le_max_left _ _))
    have hdenR : ‖hillDensity m c G₀ p.1 ξ‖ ≤ R * ‖G₀ ξ‖ :=
      hden.trans (mul_le_mul_of_nonneg_right hstep (norm_nonneg _))
    have hpiv : (0 : ℝ) ≤ 2 * Real.pi * ‖v‖ := by positivity
    calc ‖kgChar p.2 ξ * kgDirDensity v (hillDensity m c G₀ p.1) ξ‖
        = ‖kgDirDensity v (hillDensity m c G₀ p.1) ξ‖ := by
          rw [norm_mul, norm_kgChar, one_mul]
      _ ≤ 2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖hillDensity m c G₀ p.1 ξ‖) :=
          norm_kgDirDensity_le v _ ξ
      _ ≤ 2 * Real.pi * ‖v‖ * (kgFreq ξ * (R * ‖G₀ ξ‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hdenR (le_of_lt (kgFreq_pos ξ))) hpiv
      _ = 2 * Real.pi * ‖v‖ * R * (kgFreq ξ * ‖G₀ ξ‖) := by ring
  have hcont : ∀ᵐ ξ : E ∂(volume : Measure E),
      ContinuousAt
        (fun p : ℝ × E => kgChar p.2 ξ * kgDirDensity v (hillDensity m c G₀ p.1) ξ) (t₀, x₀) := by
    filter_upwards with ξ
    have hchar : Continuous fun p : ℝ × E => kgChar p.2 ξ :=
      (continuous_kgChar_point ξ).comp continuous_snd
    have hden : Continuous fun p : ℝ × E => hillDensity m c G₀ p.1 ξ :=
      (continuous_hillDensity_time (C := C) hm hc hC ξ).comp continuous_fst
    have hdir : Continuous fun p : ℝ × E => kgDirDensity v (hillDensity m c G₀ p.1) ξ :=
      continuous_const.mul hden
    exact (hchar.mul hdir).continuousAt
  exact continuousAt_of_dominated hFmeas hbound
    (h1.const_mul (2 * Real.pi * ‖v‖ * R)) hcont

/-! ## The chart partials are continuous -/

section Chart

variable {d : ℕ} {G : EuclideanSpace ℝ (Fin d) → ℂ}

theorem continuous_hillChartTimePartial (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G)
    (hweight : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) => (m + c 0 * ‖ξ‖) * ‖G ξ‖) (volume)) :
    Continuous (hillChartTimePartial m c G) := by
  have hfun : hillChartTimePartial m c G
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
          (hillSynthesisDeriv m c G (kgChar p.2) (volume) p.1).re)
        ∘ (fun y : Fin (d + 1) → ℝ => (y 0, kgSpatial d y)) := by
    funext y
    rfl
  rw [hfun]
  exact (Complex.continuous_re.comp
    (continuous_hillSynthesisDeriv_event (C := C) hm hc hcd hcpos hK hC hG hweight)).comp
    (continuous_chartPoint d)

theorem continuous_hillChartSpacePartial (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h1 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ * ‖G ξ‖) (volume))
    (i : Fin d) :
    Continuous (hillChartSpacePartial m c G i) := by
  have hfun : hillChartSpacePartial m c G i
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
          (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
            (hillDensity m c G p.1)) p.2).re)
        ∘ (fun y : Fin (d + 1) → ℝ => (y 0, kgSpatial d y)) := by
    funext y
    rfl
  rw [hfun]
  exact (Complex.continuous_re.comp
    (continuous_hillDirSynthesis_event (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h1
      ((2 * Real.pi)⁻¹ • kgDir d i))).comp (continuous_chartPoint d)

/-- **Every chart partial is continuous.** -/
theorem continuous_hillChartPartial (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (hweight : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) => (m + c 0 * ‖ξ‖) * ‖G ξ‖) (volume))
    (h1 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ * ‖G ξ‖) (volume))
    (j : Fin (d + 1)) :
    Continuous (hillChartPartial m c G j) := by
  refine Fin.cases ?_ ?_ j
  · rw [hillChartPartial_zero]
    exact continuous_hillChartTimePartial (C := C) hm hc hcd hcpos hK hC hG hweight
  · intro i
    rw [hillChartPartial_succ]
    exact continuous_hillChartSpacePartial (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h1 i

/-! ## The chart field is differentiable -/

/-- **The chart field has continuous partial derivatives everywhere.** -/
theorem isC1OnPi_hillChartField (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖G ξ‖) (volume))
    (hweight : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) => (m + c 0 * ‖ξ‖) * ‖G ξ‖) (volume))
    (h1 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ * ‖G ξ‖) (volume)) :
    IsC1OnPi (hillChartField m c G) (hillChartPartial m c G) Set.univ where
  isOpen := isOpen_univ
  hasDeriv := fun y _ j =>
    hasDerivAt_hillChartField_update (C := C) hm hc hcd hcpos hK hC hG hint hweight h1 y j
  cont := fun j =>
    continuous_hillChartPartial (C := C) hm hc hcd hcpos hK hC hcmin hclow hG hweight h1 j

/-- **Hence the chart field is differentiable, with the expected differential.** -/
theorem hasFDerivAt_hillChartField (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖G ξ‖) (volume))
    (hweight : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) => (m + c 0 * ‖ξ‖) * ‖G ξ‖) (volume))
    (h1 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ * ‖G ξ‖) (volume))
    (y : Fin (d + 1) → ℝ) :
    HasFDerivAt (hillChartField m c G) (piToCLM fun j => hillChartPartial m c G j y) y :=
  hasFDerivAt_of_isC1OnPi (d + 1) (hillChartField m c G) (hillChartPartial m c G) Set.univ
    (isC1OnPi_hillChartField (C := C) hm hc hcd hcpos hK hC hcmin hclow hG hint hweight h1) y
    (Set.mem_univ y)

/-- **And its coordinate partials are the computed ones.** -/
theorem coordPartial_hillChartField (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖G ξ‖) (volume))
    (hweight : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) => (m + c 0 * ‖ξ‖) * ‖G ξ‖) (volume))
    (h1 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ * ‖G ξ‖) (volume))
    (j : Fin (d + 1)) (y : Fin (d + 1) → ℝ) :
    coordPartial j (hillChartField m c G) y = hillChartPartial m c G j y := by
  rw [coordPartial,
    (hasFDerivAt_hillChartField (C := C) hm hc hcd hcpos hK hC hcmin hclow hG hint hweight h1
      y).fderiv, piToCLM_single]

end Chart

end ChartC1

end GaloisForLFunctions.HTGeometry
