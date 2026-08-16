import GaloisForLFunctions.RHTower.WallTailBlockDecomposition
import GaloisForLFunctions.RHTower.WallFrequencyThirdBoundary
import GaloisForLFunctions.RHTower.WallThirdIntegrationByParts

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-! ## Regularity of the third amplitude in the frequency -/

theorem continuousOn_invFamilyDeriv2_position {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {x : ℝ} {S : Set ℝ} (hgap : ∀ L ∈ S, 0 < wallFloor T σ x + L) :
    ContinuousOn (fun L : ℝ =>
      invFamilyDeriv2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
        (wallGeneratorD2 X σ) x) S := by
  have h1 := continuousOn_invFamily_position (T := T) hσ0 hσ1 hgap
  have h : ContinuousOn (fun L : ℝ =>
      invFamily (wallGeneratorShift T σ L) x * wallGeneratorD1 X σ x
          * invFamily (wallGeneratorShift T σ L) x * wallGeneratorD1 X σ x
          * invFamily (wallGeneratorShift T σ L) x
        + invFamily (wallGeneratorShift T σ L) x * wallGeneratorD1 X σ x
          * invFamily (wallGeneratorShift T σ L) x * wallGeneratorD1 X σ x
          * invFamily (wallGeneratorShift T σ L) x
        - invFamily (wallGeneratorShift T σ L) x * wallGeneratorD2 X σ x
          * invFamily (wallGeneratorShift T σ L) x) S :=
    ((((h1.mul continuousOn_const).mul h1).mul continuousOn_const).mul h1).add
        ((((h1.mul continuousOn_const).mul h1).mul continuousOn_const).mul h1) |>.sub
      ((h1.mul continuousOn_const).mul h1)
  exact h

theorem continuousOn_invFamilyProductDeriv_position {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {x : ℝ} {S : Set ℝ} (hgap : ∀ L ∈ S, 0 < wallFloor T σ x + L) :
    ContinuousOn (fun L : ℝ =>
      invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
        (wallGeneratorD2 X σ) x) S := by
  have h1 := continuousOn_invFamily_position (T := T) hσ0 hσ1 hgap
  have h2 := continuousOn_invFamilyDeriv_position (T := T) hσ0 hσ1 hgap
  have h3 := continuousOn_invFamilyDeriv2_position (T := T) hσ0 hσ1 hgap
  have h : ContinuousOn (fun L : ℝ =>
      invFamilyDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x
          * invFamilyDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x
        + invFamily (wallGeneratorShift T σ L) x
          * invFamilyDeriv2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
            (wallGeneratorD2 X σ) x) S := (h2.mul h2).add (h1.mul h3)
  exact h

theorem continuousOn_invFamilyProduct2_position {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {x : ℝ} {S : Set ℝ} (hgap : ∀ L ∈ S, 0 < wallFloor T σ x + L) :
    ContinuousOn (fun L : ℝ =>
      invFamilyProduct2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
        (wallGeneratorD2 X σ) x) S := by
  have h1 := continuousOn_invFamily_position (T := T) hσ0 hσ1 hgap
  have h2 := continuousOn_invFamilyProductDeriv_position (T := T) hσ0 hσ1 hgap
  have h : ContinuousOn (fun L : ℝ =>
      invFamily (wallGeneratorShift T σ L) x
        * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
          (wallGeneratorD2 X σ) x) S := h1.mul h2
  exact h

/-! ## The third step of the expansion, at the wall -/

/-- **The third step alone, for the literal Gamma wall.**  With the two-fold remainder amplitude
`∂D₁` the new boundary term is `D₂ = C⁻¹∂D₁`. -/
theorem wall_phase_ibp_third_step {σ L : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) {a b : ℝ}
    (hgap : ∀ t ∈ uIcc a b, 0 < wallFloor T σ t + L) :
    (∫ t in a..b, wallPhaseMap E T σ L t
        * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
          (wallGeneratorD2 X σ) t)
      = (Complex.I : ℂ) • ((wallPhaseMap E T σ L b * invFamilyProduct2 (wallGeneratorShift T σ L)
              (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) b
            - wallPhaseMap E T σ L a * invFamilyProduct2 (wallGeneratorShift T σ L)
              (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) a)
        - ∫ t in a..b, wallPhaseMap E T σ L t * invFamilyProduct2Deriv
            (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
            (wallGeneratorD3 X σ) t) := by
  refine phase_ibp_third_step_of_continuousOn
    (Eder := fun t => (-(Complex.I) : ℂ) • (wallPhaseMap E T σ L t * wallGeneratorShift T σ L t))
    (fun t _ => rfl) (fun t ht => isUnit_wallGeneratorShift hσ0 hσ1 (hgap t ht))
    (fun t _ => hasDerivAt_wallPhaseMap hEdiff hE hEne hσ0 hσ1 L t)
    (fun t _ => hasDerivAt_wallGeneratorShift T hσ0 hσ1 L t)
    (fun t _ => hasDerivAt_wallGeneratorShiftD1 hσ0 hσ1 t)
    (fun t _ => hasDerivAt_wallGeneratorD2 hσ0 hσ1 t) ?_
  exact (continuous_wallGeneratorD3 hσ0 hσ1).continuousOn

/-! ## The third threshold operator -/

/-- The operator the third step deposits at the fixed endpoint. -/
def thirdThresholdOperator (E : ℂ → ℂ) (T : X →L[ℂ] X) (σ L Y : ℝ) : X →L[ℂ] X :=
  wallPhaseMap E T σ L Y * invFamilyProduct2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
    (wallGeneratorD2 X σ) Y

theorem continuousOn_thirdThresholdOperator_position {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {Y : ℝ} {S : Set ℝ} (hgap : ∀ L ∈ S, 0 < wallFloor T σ Y + L) :
    ContinuousOn (fun L : ℝ => thirdThresholdOperator E T σ L Y) S := by
  have hW : ContinuousOn (fun L : ℝ => wallPhaseMap E T σ L Y) S :=
    (continuousOn_wallPhaseMap_position E T σ Y).continuousOn
  have hQ := continuousOn_invFamilyProduct2_position (T := T) hσ0 hσ1 hgap
  have h : ContinuousOn (fun L : ℝ => wallPhaseMap E T σ L Y
      * invFamilyProduct2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
        (wallGeneratorD2 X σ) Y) S := hW.mul hQ
  exact h

theorem norm_thirdThresholdOperator_le' {σ K₂ μ₀ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ))
    {Y : ℝ} (hY : 1 ≤ |Y|) {L : ℝ} (hfloor : μ₀ ≤ wallFloor T σ Y + L) :
    ‖thirdThresholdOperator E T σ L Y‖
      ≤ (K₂ * (1 + |Y|) ^ (1 / 2 + σ))
        * ((μ₀⁻¹ * wallAmplitudeConst μ₀) * ((1 + |Y|)⁻¹) ^ 2) := by
  have hW : ‖wallPhaseMap E T σ L Y‖ ≤ K₂ * (1 + |Y|) ^ (1 / 2 + σ) := by
    rw [wallPhaseMap, norm_smul, norm_expPhase, one_mul]
    exact hb₂ Y
  have hWnn : (0 : ℝ) ≤ K₂ * (1 + |Y|) ^ (1 / 2 + σ) := le_trans (norm_nonneg _) hW
  have hQ := norm_invFamilyProduct2_wallGeneratorShift_le' (T := T) hσ0 hσ1 hμ hY hfloor
  exact le_trans (norm_mul_le _ _) (mul_le_mul hW hQ (norm_nonneg _) hWnn)

/-- The vector the third step deposits at the fixed endpoint of the block. -/
def thirdThresholdVector (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ Y : ℝ) : X :=
  ∫ L in Icc m (m + 1), thirdThresholdOperator E T σ L Y (g L)

/-- The vector carried by the three-fold remainder over the moving interval. -/
def wallRemainderVector (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ Y x : ℝ) : X :=
  ∫ L in Icc m (m + 1), (∫ t in Y..x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv
    (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
    (wallGeneratorD3 X σ) t) (g L)


/-! ## The three-fold block decomposition -/

variable [Nontrivial X]

/-- **The two-fold remainder is itself a three-term expansion.**  One further integration by parts
inside the block integral turns the tail remainder into a boundary term at the moving endpoint, a
fixed vector deposited at the threshold, and a remainder whose amplitude decays cubically. -/
theorem tailRemainder_third_decomposition
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m Y x μ₀ : ℝ} (hg : IntegrableOn g (Icc m (m + 1)))
    (hx1 : 1 ≤ |x|) (hY1 : 1 ≤ |Y|) (hμ : 0 < μ₀)
    (hgapx : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L)
    (hgapY : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ Y + L)
    (hgapI : ∀ L ∈ Icc m (m + 1), ∀ t ∈ uIcc Y x, 0 < wallFloor T σ t + L) :
    tailRemainder E T g m σ Y x
      = (Complex.I : ℂ) • (thirdBoundary T g m σ x
          - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
              (thirdThresholdVector E T g m σ Y)
          - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
              (wallRemainderVector E T g m σ Y x)) := by
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_stripPropagatorInv_line hT hE hσ0 hσ1
  have hgapx' : ∀ L ∈ Icc m (m + 1), 0 < wallFloor T σ x + L := fun L hL =>
    lt_of_lt_of_le hμ (hgapx L hL)
  have hgapY' : ∀ L ∈ Icc m (m + 1), 0 < wallFloor T σ Y + L := fun L hL =>
    lt_of_lt_of_le hμ (hgapY L hL)
  -- the three integrable pieces of the *two-fold* expansion
  have hI1 : IntegrableOn (fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
      invFamily (wallGeneratorShift T σ L) x (g L)) (Icc m (m + 1)) :=
    integrableOn_phase_apply_of_continuousOn measurableSet_Icc
      (continuousOn_invFamily_position (T := T) hσ0 hσ1 hgapx')
      (fun L hL => norm_invFamily_wallGeneratorShift_le' hσ0 hσ1 hμ (hgapx L hL)) hg
      (continuous_expPhase_block x) (fun L => norm_expPhase L x)
  have hI2 : IntegrableOn (fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
      invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g L))
      (Icc m (m + 1)) :=
    integrableOn_phase_apply_of_continuousOn measurableSet_Icc
      (continuousOn_invFamilyProduct_position (T := T) hσ0 hσ1 hgapx')
      (fun L hL => norm_invFamilyProduct_wallGeneratorShift_le' hσ0 hσ1 hμ hx1 (hgapx L hL)) hg
      (continuous_expPhase_block x) (fun L => norm_expPhase L x)
  have hI3 : IntegrableOn (fun L : ℝ => thresholdOperator E T σ L Y (g L)) (Icc m (m + 1)) := by
    have h := integrableOn_phase_apply_of_continuousOn
      (A := fun L : ℝ => thresholdOperator E T σ L Y) (S := Icc m (m + 1)) measurableSet_Icc
      (continuousOn_thresholdOperator_position (E := E) (T := T) hσ0 hσ1 hgapY')
      (fun L hL => norm_thresholdOperator_le' hσ0 hσ1 hμ hb₂ hY1 (hgapY L hL)) hg
      (φ := fun _ => (1 : ℂ)) continuous_const (fun _ => by simp)
    simpa using h
  have htot : IntegrableOn
      (fun L : ℝ => stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (∫ t in Y..x, wallPhaseMap E T σ L t (g L))) (Icc m (m + 1)) :=
    ((stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)).restrictScalars ℝ).integrable_comp
      (integrableOn_blockPhaseIntegral' hEdiff hE hEne hσ0 hσ1 hg Y x)
  -- the two-fold pointwise expansion
  have hpt2 : ∀ L ∈ Icc m (m + 1),
      stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (∫ t in Y..x, wallPhaseMap E T σ L t (g L))
        = (Complex.I : ℂ) • (Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
              invFamily (wallGeneratorShift T σ L) x (g L))
          + Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
              invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g L)
          - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) (thresholdOperator E T σ L Y (g L))
          - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
              ((∫ t in Y..x, wallPhaseMap E T σ L t
                * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                    (wallGeneratorD2 X σ) t) (g L)) := by
    intro L hL
    rw [integral_wallPhaseMap_apply_ibp hEdiff hE hEne hσ0 hσ1 (hgapI L hL) (g L)]
    exact stripPropagator_expansion_apply hE hσ0 hσ1 L x Y _ (g L)
  have hA : Integrable (fun L : ℝ => (Complex.I : ℂ) •
      (Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
        invFamily (wallGeneratorShift T σ L) x (g L)))
      (volume.restrict (Icc m (m + 1))) := Integrable.smul (Complex.I : ℂ) hI1
  have hC : Integrable (fun L : ℝ => stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
      (thresholdOperator E T σ L Y (g L))) (volume.restrict (Icc m (m + 1))) :=
    ContinuousLinearMap.integrable_comp _ hI3
  have hAB := hA.add hI2
  have hsum := hAB.sub hC
  have hα : IntegrableOn (fun L : ℝ => stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
      ((∫ t in Y..x, wallPhaseMap E T σ L t
        * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
            (wallGeneratorD2 X σ) t) (g L))) (Icc m (m + 1)) := by
    have hcomb := hsum.sub htot
    refine Integrable.congr hcomb ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [hpt2 L hL]
    abel
  -- the two integrable pieces of the *third* step
  have hβ : IntegrableOn (fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
      invFamilyProduct2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
        (wallGeneratorD2 X σ) x (g L)) (Icc m (m + 1)) :=
    integrableOn_phase_apply_of_continuousOn measurableSet_Icc
      (continuousOn_invFamilyProduct2_position (T := T) hσ0 hσ1 hgapx')
      (fun L hL => norm_invFamilyProduct2_wallGeneratorShift_le' hσ0 hσ1 hμ hx1 (hgapx L hL)) hg
      (continuous_expPhase_block x) (fun L => norm_expPhase L x)
  have hγ0 : IntegrableOn (fun L : ℝ => thirdThresholdOperator E T σ L Y (g L)) (Icc m (m + 1)) := by
    have h := integrableOn_phase_apply_of_continuousOn
      (A := fun L : ℝ => thirdThresholdOperator E T σ L Y) (S := Icc m (m + 1)) measurableSet_Icc
      (continuousOn_thirdThresholdOperator_position (E := E) (T := T) hσ0 hσ1 hgapY')
      (fun L hL => norm_thirdThresholdOperator_le' hσ0 hσ1 hμ hb₂ hY1 (hgapY L hL)) hg
      (φ := fun _ => (1 : ℂ)) continuous_const (fun _ => by simp)
    simpa using h
  have hγ : Integrable (fun L : ℝ => stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
      (thirdThresholdOperator E T σ L Y (g L))) (volume.restrict (Icc m (m + 1))) :=
    ContinuousLinearMap.integrable_comp _ hγ0
  -- the third pointwise expansion
  have hpt3 : ∀ L ∈ Icc m (m + 1),
      stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          ((∫ t in Y..x, wallPhaseMap E T σ L t
            * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                (wallGeneratorD2 X σ) t) (g L))
        = (Complex.I : ℂ) • (Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
              invFamilyProduct2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
                (wallGeneratorD2 X σ) x (g L)
            - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (thirdThresholdOperator E T σ L Y (g L))
            - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                ((∫ t in Y..x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv
                  (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
                  (wallGeneratorD3 X σ) t) (g L))) := by
    intro L hL
    rw [wall_phase_ibp_third_step hEdiff hE hEne hσ0 hσ1 (hgapI L hL),
      smul_apply, map_smul]
    congr 1
    rw [sub_apply, sub_apply, map_sub, map_sub]
    congr 1
    congr 1
    rw [← mul_apply_eq_comp, stripPropagator_mul_wallPhaseMap_mul hE hσ0 hσ1,
      smul_apply]
    
  -- integrability of the third remainder
  have hδ : IntegrableOn (fun L : ℝ => stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
      ((∫ t in Y..x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv
        (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
        (wallGeneratorD3 X σ) t) (g L))) (Icc m (m + 1)) := by
    have hcomb := (hβ.sub hγ).sub (hα.smul (-(Complex.I) : ℂ))
    refine Integrable.congr hcomb ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL
    simp only [Pi.sub_apply, Pi.smul_apply]
    rw [hpt3 L hL, smul_sub, smul_sub, smul_smul, smul_smul]
    rw [show (-(Complex.I) : ℂ) * Complex.I = 1 by
      rw [neg_mul, Complex.I_mul_I]; ring]
    simp only [one_smul]
    abel
  -- integrability without the transport
  have hz : ((x : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := shift_ne_zero hσ0 x
  have hEz : E ((x : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := branch_ne_zero hE hσ0 hσ1 x
  have hδ0 : IntegrableOn (fun L : ℝ => (∫ t in Y..x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv
      (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
      (wallGeneratorD3 X σ) t) (g L)) (Icc m (m + 1)) := by
    have h := ContinuousLinearMap.integrable_comp
      (stripPropagatorInv E T ((x : ℂ) + (σ : ℂ) * Complex.I)) hδ
    refine Integrable.congr h ?_
    filter_upwards with L
    exact stripPropagatorInv_stripPropagator hz hEz _
  have hβγ : Integrable (fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
      invFamilyProduct2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
        (wallGeneratorD2 X σ) x (g L)
      - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (thirdThresholdOperator E T σ L Y (g L))) (volume.restrict (Icc m (m + 1))) := hβ.sub hγ
  -- integrate the pointwise expansion over the block
  rw [tailRemainder, setIntegral_congr_fun measurableSet_Icc hpt3, integral_smul,
    integral_sub hβγ hδ, integral_sub hβ hγ,
    ContinuousLinearMap.integral_comp_comm _ hγ0,
    ContinuousLinearMap.integral_comp_comm _ hδ0]
  rfl

end GaloisForLFunctions.RHTower
