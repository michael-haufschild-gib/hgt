import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedThetaProductReadsThePhasedSquare
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.PartialCuspSubtractionsScatter
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesHasADoublePole

/-!
# The translated correlation has a double pole

The opposite translations by `ω` and `−ω` leave one growing cusp term.
Its scattering has one quarter of the full theta-square residue. Mellin
unfolding therefore continues the phased square with leading coefficient
`27π³r³` at `4/3`.
-/

noncomputable section

open MeasureTheory Filter Function Asymptotics
open scoped BigOperators Classical MatrixGroups ComplexConjugate ENNReal Topology

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- Infinity is the only cusp shared by the two opposite translates. -/
def translationCusps : Finset RationalFourCusp := {.inl ()}

theorem translatedSubtraction_eq_partial :
    translatedSubtraction = partialSubtraction translationCusps thetaCoeff (Set.Ici 2) := by
  funext w
  simp [translatedSubtraction, partialSubtraction, translationCusps, rationalRep,
    rationalFourCuspRep]

theorem inl_mem_translationCusps : (.inl () : RationalFourCusp) ∈ translationCusps := by
  simp [translationCusps]

theorem otherCusps_translationCusps : otherCusps translationCusps = 0 := by
  simp [otherCusps, translationCusps]

/-! ### High in the cusp, and the constant term -/

/-- **`G_U = O(v^{−7/3})` high on the standard strip.** -/
theorem norm_translatedRenormalized_high : ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), 2 ≤ v →
    ‖translatedRenormalized (upperPoint z v hv)‖ ≤ C * v ^ (-(7 : ℝ) / 3) := by
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height 1 one_pos
  set c := ‖thetaCoeff‖
  refine ⟨2 * c * C₁ + C₁ ^ 2, by positivity, fun z v hv h2 => ?_⟩
  have hv1 : 1 ≤ v := by linarith
  set X := (v : ℂ) ^ (2 / 3 : ℂ)
  set δ₁ := sourceTheta (upperPoint (z + ringComplex omega) v hv) - thetaCoeff * X with hδ₁def
  set δ₂ := sourceTheta (upperPoint (z + ringComplex (-omega)) v hv) - thetaCoeff * X with hδ₂def
  have hδ₁ : ‖δ₁‖ ≤ C₁ / v ^ 3 := hdec v hv hv1 _
  have hδ₂ : ‖δ₂‖ ≤ C₁ / v ^ 3 := hdec v hv hv1 _
  have hf : growthProfile (Set.Ici 2) v = X ^ 2 := by
    rw [growthProfile, Set.indicator_of_mem (Set.mem_Ici.mpr h2), cpow_two_thirds_sq v hv]
  rw [translatedRenormalized, translatedThetaProduct, integralTranslation_action, integralTranslation_action,
    translatedSubtraction_eq_partial, partialSubtraction_upper _ inl_mem_translationCusps _ _ le_rfl z v hv (by linarith),
    hf]
  have he : sourceTheta (upperPoint (z + ringComplex omega) v hv) *
      sourceTheta (upperPoint (z + ringComplex (-omega)) v hv) - thetaCoeff ^ 2 * X ^ 2 =
      thetaCoeff * X * (δ₁ + δ₂) + δ₁ * δ₂ := by
    rw [hδ₁def, hδ₂def]
    ring
  rw [he]
  have hpow : ‖X‖ = v ^ ((2 : ℝ) / 3) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
    norm_num
  have hA : v ^ ((2 : ℝ) / 3) * (C₁ / v ^ 3) = C₁ * v ^ (-(7 : ℝ) / 3) := by
    rw [show -(7 : ℝ) / 3 = (2 : ℝ) / 3 - 3 by norm_num, Real.rpow_sub hv]
    norm_cast
    ring
  have hB : C₁ / v ^ 3 * (C₁ / v ^ 3) ≤ C₁ ^ 2 * v ^ (-(7 : ℝ) / 3) := by
    have h6 : (v ^ 3) ^ 2 = v ^ (6 : ℝ) := by
      rw [← pow_mul]
      norm_cast
    rw [← sq, div_pow, h6, div_eq_mul_inv, ← Real.rpow_neg hv.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)) (sq_nonneg _)
  have hc0 : 0 ≤ c := norm_nonneg _
  have h1 : ‖thetaCoeff * X * (δ₁ + δ₂)‖ ≤ c * v ^ ((2 : ℝ) / 3) * (‖δ₁‖ + ‖δ₂‖) := by
    rw [norm_mul (thetaCoeff * X) (δ₁ + δ₂), norm_mul thetaCoeff X, hpow]
    exact mul_le_mul_of_nonneg_left (norm_add_le δ₁ δ₂) (by positivity)
  calc ‖thetaCoeff * X * (δ₁ + δ₂) + δ₁ * δ₂‖
      ≤ ‖thetaCoeff * X * (δ₁ + δ₂)‖ + ‖δ₁ * δ₂‖ := norm_add_le _ _
    _ ≤ c * v ^ ((2 : ℝ) / 3) * (‖δ₁‖ + ‖δ₂‖) + ‖δ₁‖ * ‖δ₂‖ := by
        rw [norm_mul δ₁ δ₂]
        linarith [h1]
    _ ≤ c * v ^ ((2 : ℝ) / 3) * (C₁ / v ^ 3 + C₁ / v ^ 3) + C₁ / v ^ 3 * (C₁ / v ^ 3) := by
        gcongr
    _ = 2 * c * (v ^ ((2 : ℝ) / 3) * (C₁ / v ^ 3)) + C₁ / v ^ 3 * (C₁ / v ^ 3) := by ring
    _ ≤ 2 * c * (C₁ * v ^ (-(7 : ℝ) / 3)) + C₁ ^ 2 * v ^ (-(7 : ℝ) / 3) := by
        rw [hA]
        gcongr
    _ = (2 * c * C₁ + C₁ ^ 2) * v ^ (-(7 : ℝ) / 3) := by ring

theorem translatedSubtraction_integrableOn_periodDomain (v : ℝ) (hv : 0 < v) :
    IntegrableOn (fun z => translatedSubtraction (cuspCoordinateLift (v, z))) periodDomain := by
  have hm : AEStronglyMeasurable (fun z => translatedSubtraction (cuspCoordinateLift (v, z)))
      (volume.restrict periodDomain) :=
    (translatedSubtraction_measurable.comp
      (cuspCoordinateLift_measurable.comp measurable_prodMk_left)).aestronglyMeasurable
  have hfin : volume periodDomain < ⊤ := by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_lt_top
  by_cases hv2 : v ≤ 1 / 2
  · refine IntegrableOn.of_bound hfin hm (‖thetaCoeff‖ ^ 2 * (4 * (1 / v) ^ ((4 : ℝ) / 3)))
      (Eventually.of_forall fun z => ?_)
    rw [cuspCoordinateLift_positive v z hv]
    rw [translatedSubtraction_eq_partial]
    exact norm_partialSubtraction_small _ _ _ z v hv hv2
  · refine IntegrableOn.of_bound hfin hm (‖thetaCoeff ^ 2 * growthProfile (Set.Ici 2) v‖)
      (Eventually.of_forall fun z => ?_)
    rw [cuspCoordinateLift_positive v z hv, translatedSubtraction_eq_partial,
      partialSubtraction_upper _ inl_mem_translationCusps _ _ le_rfl z v hv (not_le.mp hv2)]

/-- **The constant term of `G_U`.** `a₀(G_U)(v) = |P| (c² v^{4/3} + R_U(v)) − a₀(H_R)(v)`. -/
theorem cuspConstantTerm_translatedRenormalized (v : ℝ) (hv : 0 < v) :
    cuspConstantTerm translatedRenormalized v =
      periodArea * (thetaCoeff ^ 2 * ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ) + besselRemainder translatedCoeff v) -
        cuspConstantTerm translatedSubtraction v := by
  have hI1 : IntegrableOn (fun z => translatedThetaProduct (cuspCoordinateLift (v, z))) periodDomain := by
    have he : (fun z => translatedThetaProduct (cuspCoordinateLift (v, z))) =
        fun z => translatedThetaProduct (upperPoint z v hv) :=
      funext fun z => congrArg translatedThetaProduct (cuspCoordinateLift_positive v z hv)
    rw [he]
    have ha := summable_translatedAmplitude omega v hv
    have hb := summable_translatedAmplitude (-omega) v hv
    simp only [translatedThetaProduct, translatedTheta_fourier]
    exact integrableOn_periodDomain_of_continuous _
      ((cuspCharacterSeries_continuous _ ha).mul (cuspCharacterSeries_continuous _ hb))
  rw [← cuspConstantTerm_translatedThetaProduct v hv, cuspConstantTerm, cuspConstantTerm, cuspConstantTerm]
  simp only [translatedRenormalized]
  rw [integral_sub hI1 (translatedSubtraction_integrableOn_periodDomain v hv)]

/-! ### The strip bound -/

theorem translated_strip_lintegral_lt_top {σ : ℝ} (hσ2 : 2 < σ) (hσ : σ < 13 / 3) :
    ∫⁻ w in cuspStripSet, ‖translatedRenormalized w‖ₑ * ENNReal.ofReal (hyperbolicHeight w ^ σ)
      ∂hyperbolicVolume < ⊤ := by
  obtain ⟨B, hB⟩ := translatedRenormalized_bounded
  obtain ⟨C, hC, hhigh⟩ := norm_translatedRenormalized_high
  set B' := max B 0
  have hB' : ∀ w, ‖translatedRenormalized w‖ ≤ B' := fun w => (hB w).trans (le_max_left _ _)
  have hm : Measurable (fun w => ‖translatedRenormalized w‖ₑ * ENNReal.ofReal (hyperbolicHeight w ^ σ)) :=
    translatedRenormalized_measurable.enorm.mul
      (ENNReal.measurable_ofReal.comp (hyperbolicHeight_continuous.measurable.pow_const σ))
  rw [cuspStrip_lintegral _ hm]
  set g : ℝ → ℝ := fun v => (Set.Ioc 0 2).indicator (fun v => B' * periodAreaReal * v ^ (σ - 3)) v +
    (Set.Ioi 2).indicator (fun v => C * periodAreaReal * v ^ (σ - 3 - 7 / 3)) v with hgdef
  have hg1 : IntegrableOn (fun v : ℝ => B' * periodAreaReal * v ^ (σ - 3)) (Set.Ioc 0 2) := by
    have := intervalIntegral.intervalIntegrable_rpow' (r := σ - 3) (by linarith) (a := 0) (b := 2)
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp this).const_mul _
  have hg2 : IntegrableOn (fun v : ℝ => C * periodAreaReal * v ^ (σ - 3 - 7 / 3)) (Set.Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _
  have hg : IntegrableOn g (Set.Ioi 0) :=
    (((integrable_indicator_iff measurableSet_Ioc).mpr hg1).add
      ((integrable_indicator_iff measurableSet_Ioi).mpr hg2)).integrableOn
  have hg0 : ∀ v, 0 ≤ g v := by
    intro v
    simp only [hgdef]
    refine add_nonneg (Set.indicator_nonneg (fun v hv => ?_) _) (Set.indicator_nonneg (fun v hv => ?_) _)
    · have : (0 : ℝ) < v := hv.1
      positivity
    · have : (0 : ℝ) < v := lt_trans (by norm_num) hv
      positivity
  have hP : volume periodDomain = ENNReal.ofReal periodAreaReal := periodDomain_volume
  calc ∫⁻ v in Set.Ioi (0 : ℝ), ∫⁻ z in periodDomain,
        ‖translatedRenormalized (cuspCoordinateLift (v, z))‖ₑ *
          ENNReal.ofReal (hyperbolicHeight (cuspCoordinateLift (v, z)) ^ σ) * ENNReal.ofReal ((v ^ 3)⁻¹)
      ≤ ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (g v) := by
        refine setLIntegral_mono' measurableSet_Ioi fun v (hv : 0 < v) => ?_
        have hlift : ∀ z, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z =>
          cuspCoordinateLift_positive v z hv
        simp only [hlift, hyperbolicHeight_upperPoint]
        have hpow : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x * ENNReal.ofReal (v ^ σ) * ENNReal.ofReal ((v ^ 3)⁻¹) =
            ENNReal.ofReal (x * v ^ (σ - 3)) := by
          intro x hx
          rw [← ENNReal.ofReal_mul hx, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Real.rpow_sub hv, mul_assoc, div_eq_mul_inv]
          norm_cast
        by_cases hv2 : v ≤ 2
        · have hgv : g v = B' * periodAreaReal * v ^ (σ - 3) := by
            simp only [hgdef, Set.indicator_of_mem (show v ∈ Set.Ioc 0 2 from ⟨hv, hv2⟩),
              Set.indicator_of_notMem (show v ∉ Set.Ioi 2 from fun h => absurd hv2 (not_le.mpr h)), add_zero]
          calc ∫⁻ z in periodDomain, ‖translatedRenormalized (upperPoint z v hv)‖ₑ * ENNReal.ofReal (v ^ σ) *
                ENNReal.ofReal ((v ^ 3)⁻¹)
              ≤ ∫⁻ _z in periodDomain, ENNReal.ofReal (B' * v ^ (σ - 3)) := by
                refine lintegral_mono fun z => ?_
                rw [← hpow B' (le_max_right _ _)]
                gcongr
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hB' _)
            _ = ENNReal.ofReal (g v) := by
                rw [setLIntegral_const, hP, ← ENNReal.ofReal_mul (by positivity), hgv]
                ring_nf
        · have hv2' : 2 < v := not_le.mp hv2
          have hgv : g v = C * periodAreaReal * v ^ (σ - 3 - 7 / 3) := by
            simp only [hgdef, Set.indicator_of_notMem (show v ∉ Set.Ioc 0 2 from fun h => hv2 h.2),
              Set.indicator_of_mem (show v ∈ Set.Ioi 2 from hv2'), zero_add]
          calc ∫⁻ z in periodDomain, ‖translatedRenormalized (upperPoint z v hv)‖ₑ * ENNReal.ofReal (v ^ σ) *
                ENNReal.ofReal ((v ^ 3)⁻¹)
              ≤ ∫⁻ _z in periodDomain, ENNReal.ofReal (C * v ^ (-(7 : ℝ) / 3) * v ^ (σ - 3)) := by
                refine lintegral_mono fun z => ?_
                rw [← hpow (C * v ^ (-(7 : ℝ) / 3)) (by positivity)]
                gcongr
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hhigh z v hv hv2'.le)
            _ = ENNReal.ofReal (g v) := by
                rw [setLIntegral_const, hP, ← ENNReal.ofReal_mul (by positivity), hgv]
                congr 1
                rw [show σ - 3 - 7 / 3 = -(7 : ℝ) / 3 + (σ - 3) by ring, Real.rpow_add hv]
                ring
    _ = ENNReal.ofReal (∫ v in Set.Ioi (0 : ℝ), g v) :=
        (ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg0)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem translated_integrableOn_unfolded (ψ : ℝ → ℂ) (hψm : Measurable ψ) {σ : ℝ} (hσ2 : 2 < σ)
    (hσ : σ < 13 / 3) (hψ : ∀ v : ℝ, 0 < v → ‖ψ v‖ ≤ v ^ σ) :
    IntegrableOn (unfolded translatedRenormalized ψ) cuspStripSet hyperbolicVolume := by
  refine ⟨(translatedRenormalized_measurable.mul
    (hψm.comp hyperbolicHeight_continuous.measurable)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_) (translated_strip_lintegral_lt_top hσ2 hσ)
  rw [unfolded, enorm_mul]
  gcongr
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hψ _ (hyperbolicHeight_pos w))

theorem translated_integrableOn_mul_incomplete (ψ : ℝ → ℂ) (hψm : Measurable ψ) {σ : ℝ}
    (hσ2 : 2 < σ) (hσ : σ < 13 / 3) (hψ : ∀ v : ℝ, 0 < v → ‖ψ v‖ ≤ v ^ σ) :
    IntegrableOn (fun w => translatedRenormalized w * incompleteEisenstein ψ w) levelSet hyperbolicVolume := by
  have hun := translated_integrableOn_unfolded ψ hψm hσ2 hσ hψ
  refine ⟨(translatedRenormalized_measurable.mul
    (incompleteEisenstein_measurable ψ hψm)).aestronglyMeasurable, ?_⟩
  have heq := lintegral_norm_mul_incompleteEisenstein CuspDomain.strip translatedRenormalized
    translatedRenormalized_automorphy ψ
    (translatedRenormalized_measurable.mul (hψm.comp hyperbolicHeight_continuous.measurable)).enorm.aemeasurable
  change ∫⁻ w in levelSet, ‖translatedRenormalized w * incompleteEisenstein ψ w‖ₑ ∂hyperbolicVolume < ⊤
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_) (heq.trans_lt hun.2)
  rw [enorm_mul, ENNReal.tsum_mul_left, incompleteEisenstein]
  gcongr
  refine enorm_tsum_le_tsum_enorm.trans (le_of_eq (tsum_congr fun x => ?_))
  rw [enorm_mul, ← ofReal_norm ((cosetCharacter x)⁻¹), norm_inv, norm_cosetCharacter, inv_one,
    ENNReal.ofReal_one, one_mul]

/-! ### The cleared one-cusp scattering -/

/-- The cleared scattering of the sole cusp at infinity. -/
def clearedTransScatter (s : ℂ) : ℂ :=
  (Real.pi : ℂ) / (s - 1) * cuspArea * clearedScattering s

theorem sub_mul_partialScatterTotal_zero (s : ℂ) (hs : 2 < s.re) :
    (s - 4 / 3) * partialScatterTotal 0 s = clearedTransScatter s := by
  have hφ := sub_mul_scatteringCoefficient (s := s) (by linarith)
  rw [partialScatterTotal, clearedTransScatter, ← hφ]
  push_cast
  ring

theorem clearedTransScatter_differentiableAt (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ clearedTransScatter s := by
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hcl : DifferentiableAt ℂ clearedScattering s :=
    clearedScattering_differentiableOn.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) / (s - 1)) s :=
    (differentiableAt_const _).div (differentiableAt_id.sub_const 1) hs1
  exact (h1.mul_const _).mul hcl

theorem clearedTransScatter_four_thirds :
    clearedTransScatter (4 / 3) = 3 * (Real.pi : ℂ) * cuspArea * constantArithmeticResidue := by
  rw [clearedTransScatter, clearedScattering_four_thirds]
  have h3 : (4 : ℂ) / 3 - 1 = 1 / 3 := by norm_num
  rw [h3]
  field_simp
  ring

/-! ### The Mellin identity -/

/-- **The renormalized translated product against the Eisenstein series.** For `4 < Re s < 13/3`:
`∫_{D_Γ} G_U E(s) = |P| M(s) C_U(s) + |P| c² 2^{s−2/3}/(s − 2/3) − c² Φ₀(s) 2^{4/3−s}/(s − 4/3)`. -/
theorem integral_translatedRenormalized_mul_eisenstein (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) :
    ∫ w in levelSet, translatedRenormalized w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      periodArea * (besselSqMellin s * besselDirichlet translatedCoeff s) +
        periodArea * thetaCoeff ^ 2 * ((2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3)) -
          thetaCoeff ^ 2 * partialScatterTotal 0 s * ((2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3)) := by
  have hσ2 : 2 < s.re := by linarith
  have hψ : ∀ v : ℝ, 0 < v → ‖(v : ℂ) ^ s‖ ≤ v ^ s.re := fun v hv =>
    le_of_eq (Complex.norm_cpow_eq_rpow_re_of_pos hv s)
  have hint := translated_integrableOn_unfolded (fun t => (t : ℂ) ^ s)
    (Complex.measurable_ofReal.pow_const s) hσ2 hs hψ
  rw [integral_mul_hyperbolicEisenstein_eq_constantTerm translatedRenormalized translatedRenormalized_automorphy
    s hint]
  set A : ℝ → ℂ := fun v => (v : ℂ) ^ s * cuspConstantTerm translatedRenormalized v / (v : ℂ) ^ 3 with hAdef
  change ∫ v in Set.Ioi (0 : ℝ), A v = _
  have hA : IntegrableOn A (Set.Ioi 0) := by
    have h := (cuspStrip_coordinates _ hint).1
    rw [IntegrableOn, show (volume : Measure (ℝ × ℂ)) = (volume : Measure ℝ).prod volume from rfl,
      ← Measure.prod_restrict] at h
    have h2 : IntegrableOn (fun v : ℝ => ∫ z in periodDomain,
        unfolded translatedRenormalized (fun t => (t : ℂ) ^ s) (cuspCoordinateLift (v, z)) / (v : ℂ) ^ 3)
        (Set.Ioi 0) := h.integral_prod_left
    refine h2.congr_fun (fun v (hv : 0 < v) => ?_) measurableSet_Ioi
    have hh : ∀ z, unfolded translatedRenormalized (fun t => (t : ℂ) ^ s) (cuspCoordinateLift (v, z)) =
        translatedRenormalized (cuspCoordinateLift (v, z)) * (v : ℂ) ^ s := fun z => by
      rw [unfolded, cuspCoordinateLift_positive v z hv, hyperbolicHeight_upperPoint]
    simp only [hh, hAdef, cuspConstantTerm]
    rw [integral_div, integral_mul_const]
    ring
  have hB := integrableOn_low_power s (by linarith)
  have hC := integrableOn_partialScatterPart translationCusps inl_mem_translationCusps thetaCoeff (Set.Ici 2) le_rfl
    measurableSet_Ici s (by linarith)
  have hP : periodArea ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ), A v =
      periodArea * ((v : ℂ) ^ s * besselRemainder translatedCoeff v / (v : ℂ) ^ 3) +
        periodArea * thetaCoeff ^ 2 * ((v : ℂ) ^ s *
          (Set.Iio 2).indicator (fun v => ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ)) v / (v : ℂ) ^ 3) -
        (v : ℂ) ^ s * partialScatterPart translationCusps thetaCoeff (Set.Ici 2) v / (v : ℂ) ^ 3 := by
    intro v (hv : 0 < v)
    have hg : growthProfile (Set.Ici 2) v = ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ) -
        (Set.Iio 2).indicator (fun v => ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ)) v := by
      by_cases h : v < 2
      · rw [growthProfile, Set.indicator_of_notMem (show v ∉ Set.Ici (2 : ℝ) from fun h' => by
          linarith [Set.mem_Ici.mp h']), Set.indicator_of_mem (show v ∈ Set.Iio (2 : ℝ) from h), sub_self]
      · rw [growthProfile, Set.indicator_of_mem (show v ∈ Set.Ici (2 : ℝ) from not_lt.mp h),
          Set.indicator_of_notMem (show v ∉ Set.Iio (2 : ℝ) from h), sub_zero]
    simp only [hAdef, partialScatterPart]
    rw [cuspConstantTerm_translatedRenormalized v hv, hg, translatedSubtraction_eq_partial]
    ring
  set Rf : ℝ → ℂ := fun v => (v : ℂ) ^ s * besselRemainder translatedCoeff v / (v : ℂ) ^ 3 with hRfdef
  set Bf : ℝ → ℂ := fun v => (v : ℂ) ^ s *
    (Set.Iio 2).indicator (fun v => ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ)) v / (v : ℂ) ^ 3 with hBfdef
  set Cf : ℝ → ℂ := fun v => (v : ℂ) ^ s * partialScatterPart translationCusps thetaCoeff (Set.Ici 2) v /
    (v : ℂ) ^ 3 with hCfdef
  have hcomb : IntegrableOn (fun v => periodArea⁻¹ * (A v - periodArea * thetaCoeff ^ 2 * Bf v + Cf v))
      (Set.Ioi 0) :=
    ((hA.sub (hB.const_mul (periodArea * thetaCoeff ^ 2))).add hC).const_mul periodArea⁻¹
  have hR : IntegrableOn Rf (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun hcomb (fun v hv => ?_) measurableSet_Ioi
    rw [hpt v hv]
    field_simp
    ring
  have hR' : IntegrableOn (fun v => periodArea * Rf v) (Set.Ioi 0) := hR.const_mul _
  have hB' : IntegrableOn (fun v => periodArea * thetaCoeff ^ 2 * Bf v) (Set.Ioi 0) := hB.const_mul _
  have hRB : IntegrableOn (fun v => periodArea * Rf v + periodArea * thetaCoeff ^ 2 * Bf v) (Set.Ioi 0) :=
    hR'.add hB'
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub hRB hC, integral_add hR' hB',
    integral_const_mul, integral_const_mul, hRfdef, hBfdef, hCfdef,
    integral_besselRemainder translatedCoeff s (by linarith) (summable_translatedCoeff hs4),
    integral_low_power s (by linarith),
    integral_partialScatterPart translationCusps inl_mem_translationCusps thetaCoeff s (by linarith),
    integral_growthProfile_full_eq s (by linarith), otherCusps_translationCusps]

/-! ### The seed and correction pairings -/

/-- The seed pairing of `G_U`. -/
def transSeedPair (s : ℂ) : ℂ :=
  ∫ v in Set.Ioi (0 : ℝ), cuspSeedProfile 2 3 s v * cuspConstantTerm translatedRenormalized v / (v : ℂ) ^ 3

/-- `χ(v) a₀(G_U)(v) v^{−2}`. -/
def transSeedKernel (v : ℝ) : ℂ :=
  (cuspTransition 2 3 v : ℂ) * cuspConstantTerm translatedRenormalized v / (v : ℂ) ^ 2

theorem norm_cuspConstantTerm_translated_high :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 2 ≤ v → ‖cuspConstantTerm translatedRenormalized v‖ ≤ C * v ^ (-(7 : ℝ) / 3) := by
  obtain ⟨C, hC, hhigh⟩ := norm_translatedRenormalized_high
  refine ⟨C * periodAreaReal, by positivity, fun v hv => ?_⟩
  have hv0 : 0 < v := by linarith
  have := norm_cuspConstantTerm_le translatedRenormalized v hv0 _ fun z => hhigh z v hv0 hv
  linarith [this]

theorem transSeedKernel_eq_zero (v : ℝ) (hv : v ≤ 2) : transSeedKernel v = 0 := by
  rw [transSeedKernel, cuspTransition_zero 2 3 v (by norm_num) hv, Complex.ofReal_zero, zero_mul, zero_div]

theorem transSeedKernel_measurable : Measurable transSeedKernel := by
  unfold transSeedKernel
  exact ((Complex.continuous_ofReal.measurable.comp (cuspTransition_contDiff 2 3).continuous.measurable).mul
    (cuspConstantTerm_measurable _ translatedRenormalized_measurable).measurable).div
      (Complex.measurable_ofReal.pow_const 2)

theorem norm_transSeedKernel_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 2 ≤ v → ‖transSeedKernel v‖ ≤ C * v ^ (-(13 : ℝ) / 3) := by
  obtain ⟨C, hC, hb⟩ := norm_cuspConstantTerm_translated_high
  refine ⟨C, hC, fun v hv => ?_⟩
  have hv0 : 0 < v := by linarith
  have h0 : 0 ≤ cuspTransition 2 3 v := Real.smoothTransition.nonneg _
  have h1 : cuspTransition 2 3 v ≤ 1 := Real.smoothTransition.le_one _
  rw [transSeedKernel, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hv0.le]
  have hpow : v ^ (-(7 : ℝ) / 3) / v ^ 2 = v ^ (-(13 : ℝ) / 3) := by
    rw [show -(13 : ℝ) / 3 = -(7 : ℝ) / 3 - 2 by norm_num, Real.rpow_sub hv0]
    norm_cast
  calc cuspTransition 2 3 v * ‖cuspConstantTerm translatedRenormalized v‖ / v ^ 2
      ≤ 1 * (C * v ^ (-(7 : ℝ) / 3)) / v ^ 2 := by
        gcongr
        exact hb v hv
    _ = C * v ^ (-(13 : ℝ) / 3) := by rw [one_mul, mul_div_assoc, hpow]

theorem transSeedPair_eq_mellin (s : ℂ) : transSeedPair s = mellin transSeedKernel s := by
  rw [transSeedPair, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [cuspSeedProfile, positiveHeightPower_eq_cpow s v hv, transSeedKernel, smul_eq_mul,
    Complex.cpow_sub _ _ hv0, Complex.cpow_one]
  field_simp

/-- The translated seed pairing is holomorphic on `0 < Re s < 13/3`. -/
theorem transSeedPair_differentiableAt (s : ℂ) (hs0 : 0 < s.re) (hs : s.re < 13 / 3) :
    DifferentiableAt ℂ transSeedPair s := by
  obtain ⟨C, hC, hb⟩ := norm_transSeedKernel_le
  have hfun : transSeedPair = mellin transSeedKernel := funext transSeedPair_eq_mellin
  rw [hfun]
  have hint : IntegrableOn transSeedKernel (Set.Ioi 0) := by
    have hg : IntegrableOn (fun v : ℝ => C * v ^ (-(13 : ℝ) / 3)) (Set.Ioi 2) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
    have h2 : IntegrableOn transSeedKernel (Set.Ioi 2) :=
      hg.mono' transSeedKernel_measurable.aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioi fun v (hv : 2 < v) => hb v hv.le)
    refine h2.of_forall_sdiff_eq_zero measurableSet_Ioi fun v hv => ?_
    exact transSeedKernel_eq_zero v (not_lt.mp hv.2)
  refine mellin_differentiableAt_of_isBigO_rpow (a := 13 / 3) (b := 0) hint.locallyIntegrableOn ?_ hs ?_ hs0
  · refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with v hv
    have hv0 : 0 < v := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _)]
    have := hb v hv
    rwa [show -(13 : ℝ) / 3 = -(13 / 3) by norm_num] at this
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with v hv
    rw [transSeedKernel_eq_zero v hv.2.le, norm_zero, zero_mul]

/-- The correction pairing `⟨G_U, Corr(s)⟩`. -/
def transCorrPair (s : ℂ) : ℂ := levelPairing translatedRenormalized translatedRenormalized_memLp (eisensteinCorrection s)

/-! ### The continuation and the double pole -/

/-- The continuation `Λ_U(s)` of `M(s) C_U(s)`. -/
def completedTranslated (s : ℂ) : ℂ :=
  periodArea⁻¹ * (transSeedPair s + transCorrPair s -
    periodArea * thetaCoeff ^ 2 * ((2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3)) +
      thetaCoeff ^ 2 * clearedTransScatter s * ((2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2))

/-- **The identity.** For `4 < Re s < 13/3`, `Im s > 0`: `Λ_U(s) = M(s) C_U(s)`. -/
theorem completedTranslated_eq (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    completedTranslated s = besselSqMellin s * besselDirichlet translatedCoeff s := by
  have hσ2 : 2 < s.re := by linarith
  have hseed : IntegrableOn (fun w => translatedRenormalized w * smoothCuspSeed 2 3 s w) levelSet
      hyperbolicVolume := by
    simp_rw [smoothCuspSeed_eq]
    exact translated_integrableOn_mul_incomplete _ (cuspSeedProfile_measurable s) hσ2 hs
      (norm_cuspSeedProfile_le s)
  have hint := translated_integrableOn_unfolded _ (cuspSeedProfile_measurable s) hσ2 hs
    (norm_cuspSeedProfile_le s)
  have h1 := integral_mul_eisenstein_eq translatedRenormalized translatedRenormalized_memLp s hs4 hi hseed
  rw [integral_mul_seed_eq translatedRenormalized translatedRenormalized_automorphy s hint,
    integral_translatedRenormalized_mul_eisenstein s hs4 hs] at h1
  have hne : s - 4 / 3 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re] at this
    norm_num at this
    linarith
  have hΦ : partialScatterTotal 0 s = clearedTransScatter s / (s - 4 / 3) :=
    eq_div_of_mul_eq hne (by rw [mul_comm]; exact sub_mul_partialScatterTotal_zero s hσ2)
  have hP : periodArea ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  rw [completedTranslated]
  change periodArea⁻¹ * (transSeedPair s + transCorrPair s - _ + _) = _
  have hS : transSeedPair s = ∫ v in Set.Ioi (0 : ℝ), cuspSeedProfile 2 3 s v *
      (∫ z in periodDomain, translatedRenormalized (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 := rfl
  have hC : transCorrPair s =
      levelPairing translatedRenormalized translatedRenormalized_memLp (eisensteinCorrection s) := rfl
  rw [hS, hC, ← h1, hΦ]
  field_simp
  ring

theorem completedTranslated_differentiableAt_of (s : ℂ) (hseed : DifferentiableAt ℂ transSeedPair s)
    (hcorr : DifferentiableAt ℂ transCorrPair s) (hs1 : 1 < s.re) (h23 : s - 2 / 3 ≠ 0) (h43 : s - 4 / 3 ≠ 0) :
    DifferentiableAt ℂ completedTranslated s := by
  have hcl := clearedTransScatter_differentiableAt s hs1
  have hp1 : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3)) s :=
    ((differentiableAt_id.sub_const _).const_cpow (Or.inl two_ne_zero)).div
      (differentiableAt_id.sub_const _) h23
  have hp2 : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2) s :=
    (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero)).div
      ((differentiableAt_id.sub_const _).pow 2) (pow_ne_zero 2 h43)
  unfold completedTranslated
  exact ((((hseed.add hcorr).sub (hp1.const_mul _)).add ((hcl.const_mul _).mul hp2))).const_mul _

theorem completedTranslated_differentiableAt (s : ℂ) (hs1 : 1 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    DifferentiableAt ℂ completedTranslated s := by
  have hne : ∀ a : ℝ, s - (a : ℂ) ≠ 0 := by
    intro a h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at this
    linarith
  refine completedTranslated_differentiableAt_of s (transSeedPair_differentiableAt s (by linarith) hs)
    (levelPairing_correction_analyticAt translatedRenormalized translatedRenormalized_memLp s
      (by linarith) hi.ne').differentiableAt hs1 (by simpa using hne (2 / 3)) (by simpa using hne (4 / 3))

theorem transCorrPair_center :
    AnalyticAt ℂ (fun s => levelPairing translatedRenormalized translatedRenormalized_memLp (correctionNumerator s))
      (4 / 3) ∧
      ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), (s - 4 / 3) * transCorrPair s =
        levelPairing translatedRenormalized translatedRenormalized_memLp (correctionNumerator s) := by
  obtain ⟨h1, h2, -⟩ := levelPairing_correction_center translatedRenormalized translatedRenormalized_memLp
  exact ⟨h1, h2⟩

theorem completedTranslated_differentiableAt_near :
    ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ completedTranslated s := by
  obtain ⟨hN, hev⟩ := transCorrPair_center
  set N := fun s => levelPairing translatedRenormalized translatedRenormalized_memLp (correctionNumerator s)
  rw [eventually_nhdsWithin_iff] at hev
  have hP := (hN.eventually_analyticAt.and (hev.and near_four_thirds)).eventually_nhds
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hP] with t ht htc
  have htc' : t ≠ 4 / 3 := htc
  have hne : t - 4 / 3 ≠ 0 := sub_ne_zero.mpr htc'
  obtain ⟨hNt, -, hre1, hre2, h23⟩ := ht.self_of_nhds
  have hcorr_eq : transCorrPair =ᶠ[𝓝 t] fun u => N u / (u - 4 / 3) := by
    have hne' : ∀ᶠ u in 𝓝 t, u ≠ 4 / 3 := isOpen_ne.mem_nhds htc'
    filter_upwards [ht, hne'] with u hu hu'
    rw [eq_div_iff (sub_ne_zero.mpr hu'), mul_comm]
    exact hu.2.1 hu'
  have hcorr : DifferentiableAt ℂ transCorrPair t :=
    (hNt.differentiableAt.div (differentiableAt_id.sub_const _) hne).congr_of_eventuallyEq hcorr_eq
  exact completedTranslated_differentiableAt_of t (transSeedPair_differentiableAt t (by linarith) hre2) hcorr hre1
    h23 hne

/-- **The double pole of `Λ_U` at `4/3`.** `(s − 4/3)² Λ_U(s) → 3π c² r`. -/
theorem completedTranslated_double_pole :
    Tendsto (fun s => (s - 4 / 3) ^ 2 * completedTranslated s) (𝓝[≠] (4 / 3 : ℂ))
      (𝓝 (3 * (Real.pi : ℂ) * thetaCoeff ^ 2 * constantArithmeticResidue)) := by
  obtain ⟨hN, hev⟩ := transCorrPair_center
  set N := fun s => levelPairing translatedRenormalized translatedRenormalized_memLp (correctionNumerator s)
  set F : ℂ → ℂ := fun s => periodArea⁻¹ * ((s - 4 / 3) ^ 2 * transSeedPair s + (s - 4 / 3) * N s -
    (s - 4 / 3) ^ 2 * (periodArea * thetaCoeff ^ 2 * ((2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3))) +
      thetaCoeff ^ 2 * clearedTransScatter s * (2 : ℂ) ^ (4 / 3 - s)) with hFdef
  have hP : periodArea ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  have hseed := transSeedPair_differentiableAt (4 / 3) (by norm_num) (by norm_num)
  have hcl := clearedTransScatter_differentiableAt (4 / 3) (by norm_num)
  have hp1 : ContinuousAt (fun s : ℂ => (2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3)) (4 / 3) :=
    (((continuous_id.sub continuous_const).const_cpow (Or.inl two_ne_zero)).continuousAt).div
      ((continuous_id.sub continuous_const).continuousAt) (by norm_num)
  have hp2 : ContinuousAt (fun s : ℂ => (2 : ℂ) ^ (4 / 3 - s)) (4 / 3) :=
    ((continuous_const.sub continuous_id).const_cpow (Or.inl two_ne_zero)).continuousAt
  have hFc : ContinuousAt F (4 / 3) := by
    have hlin : ContinuousAt (fun s : ℂ => s - 4 / 3) (4 / 3) := (continuous_id.sub continuous_const).continuousAt
    exact continuousAt_const.mul ((((hlin.pow 2).mul hseed.continuousAt).add
      (hlin.mul hN.continuousAt)).sub ((hlin.pow 2).mul (continuousAt_const.mul hp1)) |>.add
      ((continuousAt_const.mul hcl.continuousAt).mul hp2))
  have hF43 : F (4 / 3) = 3 * (Real.pi : ℂ) * thetaCoeff ^ 2 * constantArithmeticResidue := by
    simp only [hFdef, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      add_zero, zero_add, Complex.cpow_zero, mul_one, clearedTransScatter_four_thirds]
    have hcA : cuspArea = periodArea := rfl
    rw [hcA]
    field_simp
  rw [← hF43]
  refine (hFc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hs'
  have hne : s - 4 / 3 ≠ 0 := sub_ne_zero.mpr hs'
  have hs2 : (s - 4 / 3) * transCorrPair s = N s := hs
  have key : (s - 4 / 3) ^ 2 * ((2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2) = (2 : ℂ) ^ (4 / 3 - s) :=
    mul_div_cancel₀ _ (pow_ne_zero 2 hne)
  rw [completedTranslated, hFdef]
  simp only
  linear_combination (-(periodArea⁻¹ * (s - 4 / 3))) * hs2 +
    (-(periodArea⁻¹ * (thetaCoeff ^ 2 * clearedTransScatter s))) * key

/-- **The translated correlation has a double pole at `4/3`.** `M(s) C_U(s)`,
`C_U(s) = Σ_{h≠0} T(h)² e(2ωξ_h) (4π|ξ_h|)^{−s}`, continues to `{1 < Re s < 13/3, Im s > 0}` and to a punctured
neighbourhood of `4/3`, and `(s − 4/3)² M(s) C_U(s) → 27 π³ r³ ≠ 0` there. -/
theorem translatedCorrelation_double_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * besselDirichlet translatedCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (27 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3)) ∧
      (27 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 ≠ 0) := by
  refine ⟨completedTranslated, completedTranslated_eq, completedTranslated_differentiableAt,
    completedTranslated_differentiableAt_near, ?_, ?_⟩
  · have h := completedTranslated_double_pole
    rwa [show 3 * (Real.pi : ℂ) * thetaCoeff ^ 2 * constantArithmeticResidue =
      27 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 by rw [thetaCoeff]; ring] at h
  · have hr := constantArithmeticResidue_ne_zero
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hπ)) (pow_ne_zero 3 hr)

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
