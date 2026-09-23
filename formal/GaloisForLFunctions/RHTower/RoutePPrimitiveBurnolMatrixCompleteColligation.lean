import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaFiniteApertureHiddenBudget

/-!
# Route P matrix-complete Burnol aperture colligation

The scalar P-G188 energy identity is polarized before any Xi divisor expansion.
The three literal aperture channels define a Hilbert direct-sum isometry, so
every finite P-G186 primitive packet satisfies an exact Gram conservation law.
-/

open Complex Matrix Set Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

abbrev routePBurnolHalfLineL2 :=
  Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

theorem memLp_routePBurnolHalfLine
    {f : ℝ → ℂ} (hfcont : Continuous f)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0)) :
    MemLp f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  exact (memLp_two_iff_integrable_sq_norm
    hfcont.aestronglyMeasurable.restrict).2 hf

theorem integrableOn_norm_sq_routePBurnolForwardDampingShift
    {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℂ}
    (hfcont : Continuous f)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0)) :
    IntegrableOn
      (fun u : ℝ => ‖routePBurnolForwardDampingShift c f u‖ ^ (2 : ℕ))
      (Ioi 0) := by
  let g : ℝ → ℝ := fun u => ‖f u‖ ^ (2 : ℕ)
  have hsub : Ioi c ⊆ Ioi (0 : ℝ) := by
    intro u hu
    exact mem_Ioi.mpr (lt_of_le_of_lt hc (mem_Ioi.mp hu))
  have htail : IntegrableOn g (Ioi c) := hf.mono_set hsub
  have hshift : IntegrableOn (fun u : ℝ => g (u + c)) (Ioi 0) := by
    have hmp : MeasurePreserving (fun u : ℝ => u + c) volume volume :=
      measurePreserving_add_right volume c
    rw [show Ioi (0 : ℝ) = (fun u : ℝ => u + c) ⁻¹' Ioi c by
      ext u
      simp]
    exact (hmp.integrableOn_comp_preimage
      (measurableEmbedding_addRight c)).mpr htail
  apply Integrable.mono' hshift
  · have hm : Measurable
        (fun u : ℝ => ‖routePBurnolForwardDampingShift c f u‖ ^ (2 : ℕ)) := by
      unfold routePBurnolForwardDampingShift
      fun_prop
    exact hm.aestronglyMeasurable.restrict
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    simpa [g] using routePBurnolForwardDampingShift_norm_sq_le hc hu f

theorem memLp_routePBurnolForwardDampingShift
    {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℂ}
    (hfcont : Continuous f)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0)) :
    MemLp (routePBurnolForwardDampingShift c f) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm ?_).2
    (integrableOn_norm_sq_routePBurnolForwardDampingShift hc hfcont hf)
  have hm : Measurable (routePBurnolForwardDampingShift c f) := by
    unfold routePBurnolForwardDampingShift
    fun_prop
  exact hm.aestronglyMeasurable.restrict

theorem memLp_routePBurnolApertureBoundaryDefect
    (c : ℝ) {f : ℝ → ℂ} (hfcont : Continuous f)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0)) :
    MemLp (routePBurnolApertureBoundaryDefect c f) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  change MemLp ((Ioc (0 : ℝ) c).indicator f) 2
    (volume.restrict (Ioi (0 : ℝ)))
  exact (memLp_routePBurnolHalfLine hfcont hf).indicator measurableSet_Ioc

theorem memLp_routePBurnolApertureTailDefect
    {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℂ}
    (hfcont : Continuous f)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0)) :
    MemLp (routePBurnolApertureTailDefect c f) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_routePBurnolHalfLine hfcont hf).mono
  · have hm : Measurable (routePBurnolApertureTailDefect c f) := by
      unfold routePBurnolApertureTailDefect
      apply Measurable.indicator
      · exact (Complex.continuous_ofReal.measurable.comp
        ((by
          unfold routePBurnolApertureTailDefectWeight
          fun_prop : Measurable
            (fun u : ℝ => Real.sqrt
              (routePBurnolApertureTailDefectWeight c u))))).mul hfcont.measurable
      · exact measurableSet_Ioi
    exact hm.aestronglyMeasurable.restrict
  · filter_upwards with u
    by_cases huc : u ∈ Ioi c
    · have hcu : c < u := mem_Ioi.mp huc
      rw [routePBurnolApertureTailDefect, Set.indicator_of_mem huc,
        norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (Real.sqrt_le_one.mpr
          (routePBurnolApertureTailDefectWeight_le_one hc hcu))
    · simp [routePBurnolApertureTailDefect, huc]

def routePBurnolHalfLineL2Of
    (f : ℝ → ℂ) (hfcont : Continuous f)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0)) :
    routePBurnolHalfLineL2 :=
  (memLp_routePBurnolHalfLine hfcont hf).toLp f

def routePBurnolApertureColligationChannels
    (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℂ) (hfcont : Continuous f)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0)) :
    Fin 3 → routePBurnolHalfLineL2 :=
  ![(memLp_routePBurnolForwardDampingShift hc hfcont hf).toLp
      (routePBurnolForwardDampingShift c f),
    (memLp_routePBurnolApertureBoundaryDefect c hfcont hf).toLp
      (routePBurnolApertureBoundaryDefect c f),
    (memLp_routePBurnolApertureTailDefect hc hfcont hf).toLp
      (routePBurnolApertureTailDefect c f)]

def routePBurnolApertureColligationVector
    (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℂ) (hfcont : Continuous f)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0)) :
    PiLp 2 (fun _ : Fin 3 => routePBurnolHalfLineL2) :=
  WithLp.toLp 2 (routePBurnolApertureColligationChannels c hc f hfcont hf)

theorem norm_sq_routePBurnolHalfLineL2Of
    (f : ℝ → ℂ) (hfcont : Continuous f)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0)) :
    ‖routePBurnolHalfLineL2Of f hfcont hf‖ ^ (2 : ℕ) =
      routePBurnolApertureEnergy f := by
  rw [routePBurnolHalfLineL2Of,
    norm_sq_toLp_eq_integral_norm_sq,
    routePBurnolApertureEnergy]

theorem norm_sq_routePBurnolApertureColligationVector
    (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℂ) (hfcont : Continuous f)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0)) :
    ‖routePBurnolApertureColligationVector c hc f hfcont hf‖ ^ (2 : ℕ) =
      routePBurnolApertureEnergy f := by
  have htransport :
      ‖(memLp_routePBurnolForwardDampingShift hc hfcont hf).toLp
          (routePBurnolForwardDampingShift c f)‖ ^ (2 : ℕ) =
        routePBurnolApertureEnergy
          (routePBurnolForwardDampingShift c f) := by
    simpa [routePBurnolApertureEnergy] using
      norm_sq_toLp_eq_integral_norm_sq
        (memLp_routePBurnolForwardDampingShift hc hfcont hf)
  have hboundary :
      ‖(memLp_routePBurnolApertureBoundaryDefect c hfcont hf).toLp
          (routePBurnolApertureBoundaryDefect c f)‖ ^ (2 : ℕ) =
        routePBurnolApertureEnergy
          (routePBurnolApertureBoundaryDefect c f) := by
    simpa [routePBurnolApertureEnergy] using
      norm_sq_toLp_eq_integral_norm_sq
        (memLp_routePBurnolApertureBoundaryDefect c hfcont hf)
  have htail :
      ‖(memLp_routePBurnolApertureTailDefect hc hfcont hf).toLp
          (routePBurnolApertureTailDefect c f)‖ ^ (2 : ℕ) =
        routePBurnolApertureEnergy
          (routePBurnolApertureTailDefect c f) := by
    simpa [routePBurnolApertureEnergy] using
      norm_sq_toLp_eq_integral_norm_sq
        (memLp_routePBurnolApertureTailDefect hc hfcont hf)
  rw [routePBurnolApertureColligationVector,
    PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  change
    ‖(memLp_routePBurnolForwardDampingShift hc hfcont hf).toLp
        (routePBurnolForwardDampingShift c f)‖ ^ (2 : ℕ) +
      ‖(memLp_routePBurnolApertureBoundaryDefect c hfcont hf).toLp
        (routePBurnolApertureBoundaryDefect c f)‖ ^ (2 : ℕ) +
      ‖(memLp_routePBurnolApertureTailDefect hc hfcont hf).toLp
        (routePBurnolApertureTailDefect c f)‖ ^ (2 : ℕ) = _
  rw [htransport, hboundary, htail]
  exact routePBurnolApertureDamping_energy_colligation hc hfcont hf

def routePBurnolHalfLinePairing (f g : ℝ → ℂ) : ℂ :=
  ∫ u : ℝ in Ioi 0, star (f u) * g u

theorem integrableOn_star_mul_of_integrableOn_norm_sq
    {f g : ℝ → ℂ} (hfcont : Continuous f) (hgcont : Continuous g)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0))
    (hg : IntegrableOn (fun u : ℝ => ‖g u‖ ^ (2 : ℕ)) (Ioi 0)) :
    IntegrableOn (fun u : ℝ => star (f u) * g u) (Ioi 0) := by
  apply Integrable.mono' (hf.add hg)
  · exact ((hfcont.star.mul hgcont).aestronglyMeasurable).restrict
  · filter_upwards with u
    change ‖star (f u) * g u‖ ≤ ‖f u‖ ^ (2 : ℕ) + ‖g u‖ ^ (2 : ℕ)
    rw [norm_mul, norm_star]
    nlinarith [sq_nonneg (‖f u‖ - ‖g u‖), norm_nonneg (f u), norm_nonneg (g u)]

theorem routePBurnolHalfLinePairing_forwardDampingShift_eq_tail
    {c : ℝ} (hc : 0 ≤ c) (f g : ℝ → ℂ) :
    routePBurnolHalfLinePairing
        (routePBurnolForwardDampingShift c f)
        (routePBurnolForwardDampingShift c g) =
      ∫ u : ℝ in Ioi c,
        (((u - c) / u) ^ (2 : ℕ) : ℂ) * (star (f u) * g u) := by
  rw [routePBurnolHalfLinePairing]
  calc
    (∫ u : ℝ in Ioi 0,
        star (routePBurnolForwardDampingShift c f u) *
          routePBurnolForwardDampingShift c g u) =
        ∫ u : ℝ in Ioi 0,
          (((u / (u + c)) ^ (2 : ℕ) : ℝ) : ℂ) *
            (star (f (u + c)) * g (u + c)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      have hden : u + c ≠ 0 := by
        have hu0 := mem_Ioi.mp hu
        linarith
      change star ((((u / (u + c) : ℝ) : ℂ) * f (u + c))) *
          (((u / (u + c) : ℝ) : ℂ) * g (u + c)) = _
      rw [star_mul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    _ = ∫ u : ℝ in Ioi 0,
        (((((u + c) - c) / (u + c)) ^ (2 : ℕ) : ℝ) : ℂ) *
          (star (f (u + c)) * g (u + c)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _hu
      ring_nf
    _ = ∫ u : ℝ in Ioi c,
        (((u - c) / u) ^ (2 : ℕ) : ℂ) * (star (f u) * g u) := by
      convert routePIntegral_Ioi_comp_add_eq
        (fun u : ℝ => (((u - c) / u) ^ (2 : ℕ) : ℂ) *
          (star (f u) * g u)) c using 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _hu
      push_cast
      rfl

theorem routePBurnolHalfLinePairing_boundaryDefect
    (c : ℝ) (f g : ℝ → ℂ) :
    routePBurnolHalfLinePairing
        (routePBurnolApertureBoundaryDefect c f)
        (routePBurnolApertureBoundaryDefect c g) =
      ∫ u : ℝ in Ioc 0 c, star (f u) * g u := by
  rw [routePBurnolHalfLinePairing]
  calc
    (∫ u : ℝ in Ioi 0,
        star (routePBurnolApertureBoundaryDefect c f u) *
          routePBurnolApertureBoundaryDefect c g u) =
        ∫ u : ℝ in Ioi 0,
          (Ioc (0 : ℝ) c).indicator
            (fun u => star (f u) * g u) u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _hu
      by_cases huc : u ∈ Ioc (0 : ℝ) c <;>
        simp [routePBurnolApertureBoundaryDefect, huc]
    _ = ∫ u : ℝ in Ioi (0 : ℝ) ∩ Ioc 0 c,
        star (f u) * g u := by
      exact setIntegral_indicator measurableSet_Ioc
    _ = ∫ u : ℝ in Ioc 0 c, star (f u) * g u := by
      rw [inter_eq_right.mpr Ioc_subset_Ioi_self]

theorem routePBurnolHalfLinePairing_tailDefect
    {c : ℝ} (hc : 0 ≤ c) (f g : ℝ → ℂ) :
    routePBurnolHalfLinePairing
        (routePBurnolApertureTailDefect c f)
        (routePBurnolApertureTailDefect c g) =
      ∫ u : ℝ in Ioi c,
        (routePBurnolApertureTailDefectWeight c u : ℂ) *
          (star (f u) * g u) := by
  have hsubset : Ioi c ⊆ Ioi (0 : ℝ) := by
    intro u hu
    exact mem_Ioi.mpr (lt_of_le_of_lt hc (mem_Ioi.mp hu))
  rw [routePBurnolHalfLinePairing]
  calc
    (∫ u : ℝ in Ioi 0,
        star (routePBurnolApertureTailDefect c f u) *
          routePBurnolApertureTailDefect c g u) =
        ∫ u : ℝ in Ioi 0,
          (Ioi c).indicator
            (fun u => (routePBurnolApertureTailDefectWeight c u : ℂ) *
              (star (f u) * g u)) u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _hu
      by_cases huc : u ∈ Ioi c
      · have hcu := mem_Ioi.mp huc
        rw [Set.indicator_of_mem huc]
        simp only [routePBurnolApertureTailDefect,
          Set.indicator_of_mem huc]
        rw [star_mul]
        simp only [Complex.star_def, Complex.conj_ofReal]
        have hsqrt :
            ((Real.sqrt (routePBurnolApertureTailDefectWeight c u) : ℝ) : ℂ) *
                ((Real.sqrt (routePBurnolApertureTailDefectWeight c u) : ℝ) : ℂ) =
              (routePBurnolApertureTailDefectWeight c u : ℂ) := by
          norm_cast
          exact Real.mul_self_sqrt
            (routePBurnolApertureTailDefectWeight_nonneg hc hcu)
        rw [← hsqrt]
        ring
      · rw [Set.indicator_of_notMem huc]
        simp [routePBurnolApertureTailDefect, huc]
    _ = ∫ u : ℝ in Ioi (0 : ℝ) ∩ Ioi c,
        (routePBurnolApertureTailDefectWeight c u : ℂ) *
          (star (f u) * g u) := by
      exact setIntegral_indicator measurableSet_Ioi
    _ = ∫ u : ℝ in Ioi c,
        (routePBurnolApertureTailDefectWeight c u : ℂ) *
          (star (f u) * g u) := by
      rw [inter_eq_right.mpr hsubset]

/-- Matrix-coefficient form of P-G188: the three literal channels preserve
the full complex sesquilinear pairing, not merely diagonal energy. -/
theorem routePBurnolApertureDamping_pairing_colligation
    {c : ℝ} (hc : 0 ≤ c) {f g : ℝ → ℂ}
    (hfcont : Continuous f) (hgcont : Continuous g)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0))
    (hg : IntegrableOn (fun u : ℝ => ‖g u‖ ^ (2 : ℕ)) (Ioi 0)) :
    routePBurnolHalfLinePairing
        (routePBurnolForwardDampingShift c f)
        (routePBurnolForwardDampingShift c g) +
      routePBurnolHalfLinePairing
        (routePBurnolApertureBoundaryDefect c f)
        (routePBurnolApertureBoundaryDefect c g) +
      routePBurnolHalfLinePairing
        (routePBurnolApertureTailDefect c f)
        (routePBurnolApertureTailDefect c g) =
      routePBurnolHalfLinePairing f g := by
  let h : ℝ → ℂ := fun u => star (f u) * g u
  have hpair : IntegrableOn h (Ioi 0) :=
    integrableOn_star_mul_of_integrableOn_norm_sq hfcont hgcont hf hg
  have hsubset : Ioi c ⊆ Ioi (0 : ℝ) := by
    intro u hu
    exact mem_Ioi.mpr (lt_of_le_of_lt hc (mem_Ioi.mp hu))
  have hhead : IntegrableOn h (Ioc 0 c) := hpair.mono_set Ioc_subset_Ioi_self
  have htail : IntegrableOn h (Ioi c) := hpair.mono_set hsubset
  have htransport : IntegrableOn
      (fun u : ℝ => (((u - c) / u) ^ (2 : ℕ) : ℂ) * h u) (Ioi c) := by
    apply Integrable.mono' htail.norm
    · have hm : Measurable
          (fun u : ℝ => (((u - c) / u) ^ (2 : ℕ) : ℂ) * h u) := by
        dsimp [h]
        fun_prop
      exact hm.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul]
      rw [norm_pow, Complex.norm_div, ← ofReal_sub,
        norm_real, norm_real, Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr (mem_Ioi.mp hu)),
        Real.norm_eq_abs,
        abs_of_pos (lt_of_le_of_lt hc (mem_Ioi.mp hu))]
      have hw := routePBurnolApertureTailRatio_sq_le_one hc (mem_Ioi.mp hu)
      exact mul_le_of_le_one_left (norm_nonneg _) hw
  have hdefect : IntegrableOn
      (fun u : ℝ => (routePBurnolApertureTailDefectWeight c u : ℂ) * h u)
      (Ioi c) := by
    apply Integrable.mono' htail.norm
    · have hm : Measurable
          (fun u : ℝ => (routePBurnolApertureTailDefectWeight c u : ℂ) * h u) := by
        dsimp [routePBurnolApertureTailDefectWeight, h]
        fun_prop
      exact hm.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hw0 := routePBurnolApertureTailDefectWeight_nonneg hc (mem_Ioi.mp hu)
      have hw1 := routePBurnolApertureTailDefectWeight_le_one hc (mem_Ioi.mp hu)
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      exact mul_le_of_le_one_left (norm_nonneg _) hw1
  have htailComplete :
      (∫ u : ℝ in Ioi c, (((u - c) / u) ^ (2 : ℕ) : ℂ) * h u) +
          ∫ u : ℝ in Ioi c,
            (routePBurnolApertureTailDefectWeight c u : ℂ) * h u =
        ∫ u : ℝ in Ioi c, h u := by
    rw [← integral_add htransport hdefect]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [routePBurnolApertureTailDefectWeight]
    push_cast
    ring
  have hsplit :
      (∫ u : ℝ in Ioc 0 c, h u) + ∫ u : ℝ in Ioi c, h u =
        ∫ u : ℝ in Ioi 0, h u := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hhead htail,
      Ioc_union_Ioi_eq_Ioi hc]
  rw [routePBurnolHalfLinePairing_forwardDampingShift_eq_tail hc,
    routePBurnolHalfLinePairing_boundaryDefect,
    routePBurnolHalfLinePairing_tailDefect hc,
    routePBurnolHalfLinePairing]
  change (∫ u : ℝ in Ioi c, (((u - c) / u) ^ (2 : ℕ) : ℂ) * h u) +
      (∫ u : ℝ in Ioc 0 c, h u) +
      (∫ u : ℝ in Ioi c,
        (routePBurnolApertureTailDefectWeight c u : ℂ) * h u) =
    ∫ u : ℝ in Ioi 0, h u
  calc
    _ = (∫ u : ℝ in Ioc 0 c, h u) +
        ((∫ u : ℝ in Ioi c, (((u - c) / u) ^ (2 : ℕ) : ℂ) * h u) +
          ∫ u : ℝ in Ioi c,
            (routePBurnolApertureTailDefectWeight c u : ℂ) * h u) := by ring
    _ = (∫ u : ℝ in Ioc 0 c, h u) + ∫ u : ℝ in Ioi c, h u := by
      rw [htailComplete]
    _ = ∫ u : ℝ in Ioi 0, h u := hsplit

theorem inner_toLp_routePBurnolHalfLine_eq_pairing
    {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    (hg : MemLp g 2 (volume.restrict (Ioi (0 : ℝ)))) :
    inner ℂ (hf.toLp f) (hg.toLp g) =
      routePBurnolHalfLinePairing f g := by
  rw [MeasureTheory.L2.inner_def, routePBurnolHalfLinePairing]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with u hfu hgu
  rw [hfu, hgu, RCLike.inner_apply]
  rw [starRingEnd_apply]
  exact mul_comm _ _

theorem inner_routePBurnolApertureColligationVector_eq_source
    (c : ℝ) (hc : 0 ≤ c) (f g : ℝ → ℂ)
    (hfcont : Continuous f) (hgcont : Continuous g)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ (2 : ℕ)) (Ioi 0))
    (hg : IntegrableOn (fun u : ℝ => ‖g u‖ ^ (2 : ℕ)) (Ioi 0)) :
    inner ℂ
        (routePBurnolApertureColligationVector c hc f hfcont hf)
        (routePBurnolApertureColligationVector c hc g hgcont hg) =
      inner ℂ
        (routePBurnolHalfLineL2Of f hfcont hf)
        (routePBurnolHalfLineL2Of g hgcont hg) := by
  rw [routePBurnolApertureColligationVector,
    routePBurnolApertureColligationVector, PiLp.inner_apply,
    Fin.sum_univ_three]
  change
    inner ℂ
        ((memLp_routePBurnolForwardDampingShift hc hfcont hf).toLp
          (routePBurnolForwardDampingShift c f))
        ((memLp_routePBurnolForwardDampingShift hc hgcont hg).toLp
          (routePBurnolForwardDampingShift c g)) +
      inner ℂ
        ((memLp_routePBurnolApertureBoundaryDefect c hfcont hf).toLp
          (routePBurnolApertureBoundaryDefect c f))
        ((memLp_routePBurnolApertureBoundaryDefect c hgcont hg).toLp
          (routePBurnolApertureBoundaryDefect c g)) +
      inner ℂ
        ((memLp_routePBurnolApertureTailDefect hc hfcont hf).toLp
          (routePBurnolApertureTailDefect c f))
        ((memLp_routePBurnolApertureTailDefect hc hgcont hg).toLp
          (routePBurnolApertureTailDefect c g)) = _
  rw [inner_toLp_routePBurnolHalfLine_eq_pairing,
    inner_toLp_routePBurnolHalfLine_eq_pairing,
    inner_toLp_routePBurnolHalfLine_eq_pairing,
    routePBurnolHalfLineL2Of,
    routePBurnolHalfLineL2Of,
    inner_toLp_routePBurnolHalfLine_eq_pairing]
  exact routePBurnolApertureDamping_pairing_colligation
    hc hfcont hgcont hf hg

def routePPrimitiveBurnolWindowFeatureLp
    (pe : Nat.Primes × ℕ) (kappa : ℝ) : routePBurnolHalfLineL2 :=
  routePBurnolHalfLineL2Of
    (routePPrimitiveBurnolWindowFeature pe kappa)
    (continuous_routePPrimitiveBurnolWindowFeature pe kappa)
    (integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature pe kappa)

def routePPrimitiveBurnolApertureColligationVector
    (c : ℝ) (hc : 0 ≤ c) (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    PiLp 2 (fun _ : Fin 3 => routePBurnolHalfLineL2) :=
  routePBurnolApertureColligationVector c hc
    (routePPrimitiveBurnolWindowFeature pe kappa)
    (continuous_routePPrimitiveBurnolWindowFeature pe kappa)
    (integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature pe kappa)

/-- P-G186's finite primitive matrix is literally the half-line L2 Gram. -/
theorem routePPrimitiveBurnolWindowGramMatrix_eq_gram_L2
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    routePPrimitiveBurnolWindowGramMatrix pe kappa =
      Matrix.gram ℂ
        (fun i => routePPrimitiveBurnolWindowFeatureLp (pe i) (kappa i)) := by
  ext i j
  rw [routePPrimitiveBurnolWindowGramMatrix, Matrix.gram_apply]
  change routePBurnolHalfLinePairing
      (routePPrimitiveBurnolWindowFeature (pe i) (kappa i))
      (routePPrimitiveBurnolWindowFeature (pe j) (kappa j)) =
    inner ℂ
      (routePPrimitiveBurnolWindowFeatureLp (pe i) (kappa i))
      (routePPrimitiveBurnolWindowFeatureLp (pe j) (kappa j))
  rw [routePPrimitiveBurnolWindowFeatureLp,
    routePPrimitiveBurnolWindowFeatureLp]
  exact (inner_toLp_routePBurnolHalfLine_eq_pairing _ _).symm

/-- **P-G194 matrix-complete colligation.** Every finite primitive packet,
including all off-diagonal ordinate interactions, is preserved exactly by the
three-channel Burnol aperture dilation. -/
theorem routePPrimitiveBurnolWindowGramMatrix_eq_colligation_gram
    {N : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    routePPrimitiveBurnolWindowGramMatrix pe kappa =
      Matrix.gram ℂ (fun i =>
        routePPrimitiveBurnolApertureColligationVector
          c hc (pe i) (kappa i)) := by
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_gram_L2]
  ext i j
  rw [Matrix.gram_apply, Matrix.gram_apply]
  exact (inner_routePBurnolApertureColligationVector_eq_source c hc
    (routePPrimitiveBurnolWindowFeature (pe i) (kappa i))
    (routePPrimitiveBurnolWindowFeature (pe j) (kappa j))
    (continuous_routePPrimitiveBurnolWindowFeature (pe i) (kappa i))
    (continuous_routePPrimitiveBurnolWindowFeature (pe j) (kappa j))
    (integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature (pe i) (kappa i))
    (integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature (pe j) (kappa j))).symm

def routePPrimitiveBurnolApertureChannelGramMatrix
    {N : ℕ} (c : ℝ) (hc : 0 ≤ c) (channel : Fin 3)
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.gram ℂ (fun i =>
    routePPrimitiveBurnolApertureColligationVector
      c hc (pe i) (kappa i) channel)

theorem routePPrimitiveBurnolApertureChannelGramMatrix_posSemidef
    {N : ℕ} (c : ℝ) (hc : 0 ≤ c) (channel : Fin 3)
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (routePPrimitiveBurnolApertureChannelGramMatrix
      c hc channel pe kappa).PosSemidef := by
  exact Matrix.posSemidef_gram ℂ _

/-- Entrywise conservation splits the source Gram into transported,
hard-boundary, and tail-cocycle positive Gram matrices. -/
theorem routePPrimitiveBurnolWindowGramMatrix_eq_sum_channelGrams
    {N : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    routePPrimitiveBurnolWindowGramMatrix pe kappa =
      routePPrimitiveBurnolApertureChannelGramMatrix c hc 0 pe kappa +
      routePPrimitiveBurnolApertureChannelGramMatrix c hc 1 pe kappa +
      routePPrimitiveBurnolApertureChannelGramMatrix c hc 2 pe kappa := by
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_colligation_gram c hc]
  ext i j
  rw [Matrix.gram_apply, PiLp.inner_apply, Fin.sum_univ_three]
  rfl

/-- The transported complete Gram is Loewner-dominated by the original
P-G186 source Gram, with the two explicit defect Grams as positive remainder. -/
theorem routePPrimitiveBurnolApertureTransportedGram_loewnerLE_source
    {N : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    frankensteinMatrixLoewnerLE
      (routePPrimitiveBurnolApertureChannelGramMatrix c hc 0 pe kappa)
      (routePPrimitiveBurnolWindowGramMatrix pe kappa) := by
  unfold frankensteinMatrixLoewnerLE
  have hsum := routePPrimitiveBurnolWindowGramMatrix_eq_sum_channelGrams
    c hc pe kappa
  rw [hsum]
  convert
    (routePPrimitiveBurnolApertureChannelGramMatrix_posSemidef
        c hc 1 pe kappa).add
      (routePPrimitiveBurnolApertureChannelGramMatrix_posSemidef
        c hc 2 pe kappa) using 1
  ext i j
  simp
  ring

end

end RHTower
