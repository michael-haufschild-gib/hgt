import GaloisForLFunctions.HTGeometry.LikelihoodPolarizationInformation
import GaloisForLFunctions.HTGeometry.PoissonIntensityMarkingIsometry

/-!
# Product formation and nonlinear rapidity fusion

Two independent binary experiments fuse into one.  The balanced law of the product pair has
density `1 + d₁d₂` against the product of the balanced laws, the fused contrast is the
Einstein-type combination `(d₁ + d₂)/(1 + d₁d₂)`, the fused visibility is `a₁a₂/(1 + d₁d₂)`, and
Jeffreys information is additive.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The Radon--Nikodym density of a product against a product. -/
theorem rnDeriv_prod (P₁ ν₁ : Measure X) (P₂ ν₂ : Measure Y) [IsFiniteMeasure P₁]
    [IsFiniteMeasure ν₁] [IsFiniteMeasure P₂] [IsFiniteMeasure ν₂]
    (h₁ : P₁ ≪ ν₁) (h₂ : P₂ ≪ ν₂) :
    (P₁.prod P₂).rnDeriv (ν₁.prod ν₂)
      =ᵐ[ν₁.prod ν₂] fun p => P₁.rnDeriv ν₁ p.1 * P₂.rnDeriv ν₂ p.2 := by
  haveI : SigmaFinite (ν₁.withDensity (P₁.rnDeriv ν₁)) := by
    rw [Measure.withDensity_rnDeriv_eq P₁ ν₁ h₁]; infer_instance
  haveI : SigmaFinite (ν₂.withDensity (P₂.rnDeriv ν₂)) := by
    rw [Measure.withDensity_rnDeriv_eq P₂ ν₂ h₂]; infer_instance
  have hw : (ν₁.prod ν₂).withDensity (fun p => P₁.rnDeriv ν₁ p.1 * P₂.rnDeriv ν₂ p.2)
      = P₁.prod P₂ := by
    rw [← prod_withDensity (Measure.measurable_rnDeriv P₁ ν₁)
      (Measure.measurable_rnDeriv P₂ ν₂), Measure.withDensity_rnDeriv_eq P₁ ν₁ h₁,
      Measure.withDensity_rnDeriv_eq P₂ ν₂ h₂]
  calc (P₁.prod P₂).rnDeriv (ν₁.prod ν₂)
      = ((ν₁.prod ν₂).withDensity
          (fun p => P₁.rnDeriv ν₁ p.1 * P₂.rnDeriv ν₂ p.2)).rnDeriv (ν₁.prod ν₂) := by rw [hw]
    _ =ᵐ[ν₁.prod ν₂] fun p => P₁.rnDeriv ν₁ p.1 * P₂.rnDeriv ν₂ p.2 :=
        Measure.rnDeriv_withDensity _ (by fun_prop)

/-- `(LPC.33)`  Jeffreys information is additive over independent products. -/
theorem formationJeffreys_prod (P₁ Q₁ : Measure X) (P₂ Q₂ : Measure Y) [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure Q₁] [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂] :
    formationJeffreys (P₁.prod P₂) (Q₁.prod Q₂)
      = formationJeffreys P₁ Q₁ + formationJeffreys P₂ Q₂ := by
  rw [formationJeffreys, formationJeffreys, formationJeffreys, klDiv_prod, klDiv_prod]
  abel

/-! ## The fused balanced law -/

variable (P₁ Q₁ : Measure X) (P₂ Q₂ : Measure Y)

theorem absolutelyContinuous_prod_balancedLaw [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂] :
    (P₁.prod P₂) ≪ (balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂) :=
  (absolutelyContinuous_balancedLaw_left P₁ Q₁).prod (absolutelyContinuous_balancedLaw_left P₂ Q₂)

theorem absolutelyContinuous_prod_balancedLaw' [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂] :
    (Q₁.prod Q₂) ≪ (balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂) :=
  (absolutelyContinuous_balancedLaw_right P₁ Q₁).prod
    (absolutelyContinuous_balancedLaw_right P₂ Q₂)

/-- The forward product density in contrast coordinates. -/
theorem toReal_rnDeriv_prod_left [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂] :
    (fun p => ((P₁.prod P₂).rnDeriv ((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)) p).toReal)
      =ᵐ[(balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)]
        fun p => (1 + posteriorContrast P₁ Q₁ p.1) * (1 + posteriorContrast P₂ Q₂ p.2) := by
  have hfin₁ : ∀ᵐ p ∂((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)),
      P₁.rnDeriv (balancedLaw P₁ Q₁) p.1 < ⊤ := by
    have h : ∀ᵐ x ∂(((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)).map Prod.fst),
        P₁.rnDeriv (balancedLaw P₁ Q₁) x < ⊤ := by
      rw [← Measure.fst, Measure.fst_prod]
      exact Measure.rnDeriv_lt_top _ _
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt (Measure.measurable_rnDeriv _ _) measurable_const)).mp h
  have hfin₂ : ∀ᵐ p ∂((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)),
      P₂.rnDeriv (balancedLaw P₂ Q₂) p.2 < ⊤ := by
    have h : ∀ᵐ y ∂(((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)).map Prod.snd),
        P₂.rnDeriv (balancedLaw P₂ Q₂) y < ⊤ := by
      rw [← Measure.snd, Measure.snd_prod]
      exact Measure.rnDeriv_lt_top _ _
    exact (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_lt (Measure.measurable_rnDeriv _ _) measurable_const)).mp h
  filter_upwards [rnDeriv_prod P₁ (balancedLaw P₁ Q₁) P₂ (balancedLaw P₂ Q₂)
      (absolutelyContinuous_balancedLaw_left P₁ Q₁)
      (absolutelyContinuous_balancedLaw_left P₂ Q₂), hfin₁, hfin₂] with p h h1 h2
  rw [h, ENNReal.toReal_mul, rnDeriv_left_toReal, rnDeriv_left_toReal]

/-- The reflected product density in contrast coordinates. -/
theorem toReal_rnDeriv_prod_right [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂] :
    (fun p => ((Q₁.prod Q₂).rnDeriv ((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)) p).toReal)
      =ᵐ[(balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)]
        fun p => (1 - posteriorContrast P₁ Q₁ p.1) * (1 - posteriorContrast P₂ Q₂ p.2) := by
  have hfin₁ : ∀ᵐ p ∂((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)),
      Q₁.rnDeriv (balancedLaw P₁ Q₁) p.1 < ⊤ := by
    have h : ∀ᵐ x ∂(((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)).map Prod.fst),
        Q₁.rnDeriv (balancedLaw P₁ Q₁) x < ⊤ := by
      rw [← Measure.fst, Measure.fst_prod]; exact Measure.rnDeriv_lt_top _ _
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt (Measure.measurable_rnDeriv _ _) measurable_const)).mp h
  have hfin₂ : ∀ᵐ p ∂((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)),
      Q₂.rnDeriv (balancedLaw P₂ Q₂) p.2 < ⊤ := by
    have h : ∀ᵐ y ∂(((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)).map Prod.snd),
        Q₂.rnDeriv (balancedLaw P₂ Q₂) y < ⊤ := by
      rw [← Measure.snd, Measure.snd_prod]; exact Measure.rnDeriv_lt_top _ _
    exact (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_lt (Measure.measurable_rnDeriv _ _) measurable_const)).mp h
  have hr₁ : ∀ᵐ p ∂((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)),
      (Q₁.rnDeriv (balancedLaw P₁ Q₁) p.1).toReal = 1 - posteriorContrast P₁ Q₁ p.1 := by
    have h : ∀ᵐ x ∂(((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)).map Prod.fst),
        (Q₁.rnDeriv (balancedLaw P₁ Q₁) x).toReal = 1 - posteriorContrast P₁ Q₁ x := by
      rw [← Measure.fst, Measure.fst_prod]; exact rnDeriv_right_toReal P₁ Q₁
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_eq_fun ((Measure.measurable_rnDeriv _ _).ennreal_toReal)
        (measurable_const.sub (measurable_posteriorContrast _ _)))).mp h
  have hr₂ : ∀ᵐ p ∂((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)),
      (Q₂.rnDeriv (balancedLaw P₂ Q₂) p.2).toReal = 1 - posteriorContrast P₂ Q₂ p.2 := by
    have h : ∀ᵐ y ∂(((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)).map Prod.snd),
        (Q₂.rnDeriv (balancedLaw P₂ Q₂) y).toReal = 1 - posteriorContrast P₂ Q₂ y := by
      rw [← Measure.snd, Measure.snd_prod]; exact rnDeriv_right_toReal P₂ Q₂
    exact (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_eq_fun ((Measure.measurable_rnDeriv _ _).ennreal_toReal)
        (measurable_const.sub (measurable_posteriorContrast _ _)))).mp h
  filter_upwards [rnDeriv_prod Q₁ (balancedLaw P₁ Q₁) Q₂ (balancedLaw P₂ Q₂)
      (absolutelyContinuous_balancedLaw_right P₁ Q₁)
      (absolutelyContinuous_balancedLaw_right P₂ Q₂), hfin₁, hfin₂, hr₁, hr₂]
    with p h h1 h2 h3 h4
  rw [h, ENNReal.toReal_mul, h3, h4]

/-- `(LPC.31)`  The fused balanced law has density `1 + d₁d₂`. -/
theorem withDensity_fusion [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂] :
    ((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)).withDensity
        (fun p => ENNReal.ofReal
          (1 + posteriorContrast P₁ Q₁ p.1 * posteriorContrast P₂ Q₂ p.2))
      = balancedLaw (P₁.prod P₂) (Q₁.prod Q₂) := by
  set ν := (balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂) with hν
  have hac₁ : (P₁.prod P₂) ≪ ν := absolutelyContinuous_prod_balancedLaw P₁ Q₁ P₂ Q₂
  have hac₂ : (Q₁.prod Q₂) ≪ ν := absolutelyContinuous_prod_balancedLaw' P₁ Q₁ P₂ Q₂
  have hdens : (fun p => ENNReal.ofReal
        (1 + posteriorContrast P₁ Q₁ p.1 * posteriorContrast P₂ Q₂ p.2))
      =ᵐ[ν] (2 : ℝ≥0∞)⁻¹ • ((P₁.prod P₂).rnDeriv ν + (Q₁.prod Q₂).rnDeriv ν) := by
    have hfP : ∀ᵐ p ∂ν, (P₁.prod P₂).rnDeriv ν p < ⊤ := Measure.rnDeriv_lt_top _ _
    have hfQ : ∀ᵐ p ∂ν, (Q₁.prod Q₂).rnDeriv ν p < ⊤ := Measure.rnDeriv_lt_top _ _
    filter_upwards [toReal_rnDeriv_prod_left P₁ Q₁ P₂ Q₂,
      toReal_rnDeriv_prod_right P₁ Q₁ P₂ Q₂, hfP, hfQ] with p hP hQ hfP' hfQ'
    have hPe : (P₁.prod P₂).rnDeriv ν p
        = ENNReal.ofReal ((1 + posteriorContrast P₁ Q₁ p.1) * (1 + posteriorContrast P₂ Q₂ p.2)) := by
      rw [← hP, ENNReal.ofReal_toReal hfP'.ne]
    have hQe : (Q₁.prod Q₂).rnDeriv ν p
        = ENNReal.ofReal ((1 - posteriorContrast P₁ Q₁ p.1) * (1 - posteriorContrast P₂ Q₂ p.2)) := by
      rw [← hQ, ENNReal.ofReal_toReal hfQ'.ne]
    have hnn₁ : (0:ℝ) ≤ (1 + posteriorContrast P₁ Q₁ p.1) * (1 + posteriorContrast P₂ Q₂ p.2) := by
      rw [← hP]; positivity
    have hnn₂ : (0:ℝ) ≤ (1 - posteriorContrast P₁ Q₁ p.1) * (1 - posteriorContrast P₂ Q₂ p.2) := by
      rw [← hQ]; positivity
    show _ = (2 : ℝ≥0∞)⁻¹ * ((P₁.prod P₂).rnDeriv ν p + (Q₁.prod Q₂).rnDeriv ν p)
    rw [hPe, hQe, ← ENNReal.ofReal_add hnn₁ hnn₂,
      show ((2 : ℝ≥0∞))⁻¹ = ENNReal.ofReal (2⁻¹ : ℝ) by
        rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [withDensity_congr_ae hdens, withDensity_smul _ (by fun_prop),
    withDensity_add_left (Measure.measurable_rnDeriv _ _),
    Measure.withDensity_rnDeriv_eq _ _ hac₁, Measure.withDensity_rnDeriv_eq _ _ hac₂]
  rfl

theorem measurable_fusionDensity (P₁ Q₁ : Measure X) (P₂ Q₂ : Measure Y) :
    Measurable fun p : X × Y => ENNReal.ofReal
      (1 + posteriorContrast P₁ Q₁ p.1 * posteriorContrast P₂ Q₂ p.2) :=
  ENNReal.measurable_ofReal.comp (measurable_const.add
    (((measurable_posteriorContrast P₁ Q₁).comp measurable_fst).mul
      ((measurable_posteriorContrast P₂ Q₂).comp measurable_snd)))

/-- `(LPC.32)`  The fused posterior contrast is the Einstein-type combination of the two
contrasts. -/
theorem posteriorContrast_prod [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q₂]
    (hpos : ∀ᵐ p ∂((balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂)),
      0 < 1 + posteriorContrast P₁ Q₁ p.1 * posteriorContrast P₂ Q₂ p.2) :
    posteriorContrast (P₁.prod P₂) (Q₁.prod Q₂)
      =ᵐ[balancedLaw (P₁.prod P₂) (Q₁.prod Q₂)]
        fun p => (posteriorContrast P₁ Q₁ p.1 + posteriorContrast P₂ Q₂ p.2)
          / (1 + posteriorContrast P₁ Q₁ p.1 * posteriorContrast P₂ Q₂ p.2) := by
  set ν := (balancedLaw P₁ Q₁).prod (balancedLaw P₂ Q₂) with hν
  set η := balancedLaw (P₁.prod P₂) (Q₁.prod Q₂) with hη
  have hac : η ≪ ν := by
    rw [hη, ← withDensity_fusion P₁ Q₁ P₂ Q₂]
    exact withDensity_absolutelyContinuous _ _
  have hPη : (P₁.prod P₂) ≪ η := absolutelyContinuous_balancedLaw_left _ _
  have hchain : ∀ᵐ p ∂η,
      (P₁.prod P₂).rnDeriv η p * η.rnDeriv ν p = (P₁.prod P₂).rnDeriv ν p :=
    (Measure.rnDeriv_mul_rnDeriv (κ := ν) hPη).filter_mono hac.ae_le
  have hw : ∀ᵐ p ∂η, η.rnDeriv ν p = ENNReal.ofReal
      (1 + posteriorContrast P₁ Q₁ p.1 * posteriorContrast P₂ Q₂ p.2) := by
    refine Filter.Eventually.filter_mono hac.ae_le ?_
    rw [hη, ← withDensity_fusion P₁ Q₁ P₂ Q₂]
    exact Measure.rnDeriv_withDensity _ (measurable_fusionDensity P₁ Q₁ P₂ Q₂)
  have hL : ∀ᵐ p ∂η,
      ((P₁.prod P₂).rnDeriv ν p).toReal
        = (1 + posteriorContrast P₁ Q₁ p.1) * (1 + posteriorContrast P₂ Q₂ p.2) :=
    (toReal_rnDeriv_prod_left P₁ Q₁ P₂ Q₂).filter_mono hac.ae_le
  have hposη : ∀ᵐ p ∂η,
      0 < 1 + posteriorContrast P₁ Q₁ p.1 * posteriorContrast P₂ Q₂ p.2 :=
    hpos.filter_mono hac.ae_le
  filter_upwards [hchain, hw, hL, hposη, Measure.rnDeriv_lt_top (P₁.prod P₂) η]
    with p hc hwp hLp hp hf
  have hmulR := congrArg ENNReal.toReal (hwp ▸ hc)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le, hLp] at hmulR
  have hne : (1 + posteriorContrast P₁ Q₁ p.1 * posteriorContrast P₂ Q₂ p.2) ≠ 0 := hp.ne'
  have hval : ((P₁.prod P₂).rnDeriv η p).toReal
      = ((1 + posteriorContrast P₁ Q₁ p.1) * (1 + posteriorContrast P₂ Q₂ p.2))
        / (1 + posteriorContrast P₁ Q₁ p.1 * posteriorContrast P₂ Q₂ p.2) := by
    field_simp
    linarith [hmulR]
  show ((P₁.prod P₂).rnDeriv η p).toReal - 1 = _
  rw [hval]
  field_simp
  ring

/-- `(LPC.32)`  The visibility fusion identity, in pointwise form. -/
theorem visibility_fusion_real {a b : ℝ} (ha : |a| < 1) (hb : |b| < 1) :
    Real.sqrt (1 - ((a + b) / (1 + a * b)) ^ 2)
      = Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) / (1 + a * b) := by
  rw [abs_lt] at ha hb
  have hpos : 0 < 1 + a * b := by nlinarith [ha.1, ha.2, hb.1, hb.2]
  have h1 : (0:ℝ) ≤ 1 - a ^ 2 := by nlinarith [ha.1, ha.2]
  have h2 : (0:ℝ) ≤ 1 - b ^ 2 := by nlinarith [hb.1, hb.2]
  have hid : 1 - ((a + b) / (1 + a * b)) ^ 2 = (1 - a ^ 2) * (1 - b ^ 2) / (1 + a * b) ^ 2 := by
    field_simp
    ring
  rw [hid, Real.sqrt_div' _ (by positivity), Real.sqrt_mul h1, Real.sqrt_sq hpos.le]

/-- `(LPC.32)`  The rapidity addition law. -/
theorem artanh_fusion {a b : ℝ} (ha : |a| < 1) (hb : |b| < 1) :
    Real.artanh ((a + b) / (1 + a * b)) = Real.artanh a + Real.artanh b := by
  rw [abs_lt] at ha hb
  have hpos : 0 < 1 + a * b := by nlinarith [ha.1, ha.2, hb.1, hb.2]
  have h1a : (0:ℝ) < 1 + a := by linarith [ha.1]
  have h2a : (0:ℝ) < 1 - a := by linarith [ha.2]
  have h1b : (0:ℝ) < 1 + b := by linarith [hb.1]
  have h2b : (0:ℝ) < 1 - b := by linarith [hb.2]
  rw [Real.artanh, Real.artanh, Real.artanh]
  have hnum : 1 + (a + b) / (1 + a * b) = ((1 + a) * (1 + b)) / (1 + a * b) := by
    field_simp; ring
  have hden : 1 - (a + b) / (1 + a * b) = ((1 - a) * (1 - b)) / (1 + a * b) := by
    field_simp; ring
  rw [hnum, hden,
    show (1 + a) * (1 + b) / (1 + a * b) / ((1 - a) * (1 - b) / (1 + a * b))
      = ((1 + a) / (1 - a)) * ((1 + b) / (1 - b)) by field_simp,
    Real.sqrt_mul (by positivity), Real.log_mul (by positivity) (by positivity)]

end

end GaloisForLFunctions.HTGeometry
