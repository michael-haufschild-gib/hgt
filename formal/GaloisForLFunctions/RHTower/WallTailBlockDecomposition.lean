import GaloisForLFunctions.RHTower.WallPropagatedExpansion
import GaloisForLFunctions.RHTower.WallReversedBlockFubini

/-!
# The block decomposition of the propagated tail

Integrating the propagated expansion over the block turns the moving part of the tail into four block
averages:

```text
H(x) int_Y^x H(t)^{-1} b(t) dt
  = -(i/2)[ i (first boundary) + (second boundary)
            - H(x)(threshold vector) - (remainder) ].
```

The two averages at the moving endpoint are transport-free resolvent averages; the threshold terms
collapse into a single fixed vector propagated by the transport; the last is the Hardy tail.

The separation is where the position regularity is used: each of the three named families is
continuous in the position and uniformly bounded on the block, so each term is separately integrable
there, and the fourth is then integrable as a combination.  Splitting is essential rather than
convenient — the first average must be integrated in the position *before* it is estimated, because
its estimate is Plancherel, not a pointwise bound.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- The first boundary term as a block average. -/
def firstBoundaryBlock (T : X →L[ℂ] X) (g : ℝ → X) (m σ x : ℝ) : X :=
  ∫ L in Icc m (m + 1), Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
    • (invFamily (wallGeneratorShift T σ L) x (g L))

/-- The vector accumulated at the threshold by the two boundary terms. -/
def thresholdVector (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ Y : ℝ) : X :=
  ∫ L in Icc m (m + 1), thresholdOperator E T σ L Y (g L)

/-! ## Continuity and uniform bounds of the three block operator families -/

omit [Nontrivial X] in
theorem continuousOn_wallPhaseMap_position (E : ℂ → ℂ) (T : X →L[ℂ] X) (σ Y : ℝ) :
    Continuous fun L : ℝ => wallPhaseMap E T σ L Y := by
  have h : Continuous fun L : ℝ =>
      Complex.exp (-(Complex.I) * (L : ℂ) * (Y : ℂ))
        • stripPropagatorInv E T ((Y : ℂ) + (σ : ℂ) * Complex.I) :=
    (continuous_expPhase_block Y).smul continuous_const
  exact h

omit [Nontrivial X] in
theorem continuousOn_thresholdOperator_position {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {Y : ℝ} {S : Set ℝ} (hgap : ∀ L ∈ S, 0 < wallFloor T σ Y + L) :
    ContinuousOn (fun L : ℝ => thresholdOperator E T σ L Y) S := by
  have hW : ContinuousOn (fun L : ℝ => wallPhaseMap E T σ L Y) S :=
    (continuousOn_wallPhaseMap_position E T σ Y).continuousOn
  have hA := continuousOn_invFamily_position (T := T) hσ0 hσ1 hgap
  have hP := continuousOn_invFamilyProduct_position (T := T) hσ0 hσ1 hgap
  have h : ContinuousOn (fun L : ℝ =>
      (Complex.I : ℂ) • (wallPhaseMap E T σ L Y * invFamily (wallGeneratorShift T σ L) Y)
        + wallPhaseMap E T σ L Y
          * invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) Y) S :=
    ((hW.mul hA).const_smul (Complex.I : ℂ)).add (hW.mul hP)
  exact h

omit [Nontrivial X] in
theorem norm_thresholdOperator_le' {σ K₂ μ₀ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ))
    {Y : ℝ} (hY : 1 ≤ |Y|) {L : ℝ} (hfloor : μ₀ ≤ wallFloor T σ Y + L) :
    ‖thresholdOperator E T σ L Y‖
      ≤ (K₂ * (1 + |Y|) ^ (1 / 2 + σ)) * (μ₀⁻¹ + (μ₀⁻¹) ^ 3 * (3 + Real.pi) * (1 + |Y|)⁻¹) := by
  have hW : ‖wallPhaseMap E T σ L Y‖ ≤ K₂ * (1 + |Y|) ^ (1 / 2 + σ) := by
    rw [wallPhaseMap, norm_smul, norm_expPhase, one_mul]
    exact hb₂ Y
  have hWnn : (0 : ℝ) ≤ K₂ * (1 + |Y|) ^ (1 / 2 + σ) := le_trans (norm_nonneg _) hW
  have hA : ‖invFamily (wallGeneratorShift T σ L) Y‖ ≤ μ₀⁻¹ :=
    norm_invFamily_wallGeneratorShift_le' hσ0 hσ1 hμ hfloor
  have hP : ‖invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) Y‖
      ≤ (μ₀⁻¹) ^ 3 * (3 + Real.pi) * (1 + |Y|)⁻¹ :=
    norm_invFamilyProduct_wallGeneratorShift_le' hσ0 hσ1 hμ hY hfloor
  calc ‖thresholdOperator E T σ L Y‖
      ≤ ‖(Complex.I : ℂ) • (wallPhaseMap E T σ L Y * invFamily (wallGeneratorShift T σ L) Y)‖
        + ‖wallPhaseMap E T σ L Y
            * invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) Y‖ :=
        norm_add_le _ _
    _ ≤ (K₂ * (1 + |Y|) ^ (1 / 2 + σ)) * μ₀⁻¹
        + (K₂ * (1 + |Y|) ^ (1 / 2 + σ)) * ((μ₀⁻¹) ^ 3 * (3 + Real.pi) * (1 + |Y|)⁻¹) := by
        refine add_le_add ?_ ?_
        · rw [norm_smul, Complex.norm_I, one_mul]
          exact le_trans (norm_mul_le _ _) (mul_le_mul hW hA (norm_nonneg _) hWnn)
        · exact le_trans (norm_mul_le _ _) (mul_le_mul hW hP (norm_nonneg _) hWnn)
    _ = (K₂ * (1 + |Y|) ^ (1 / 2 + σ))
          * (μ₀⁻¹ + (μ₀⁻¹) ^ 3 * (3 + Real.pi) * (1 + |Y|)⁻¹) := by ring

omit [Nontrivial X] in
/-- The threshold operator bound on the outward ray. -/
theorem norm_thresholdOperator_le {σ K₂ μ₀ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ))
    {Y : ℝ} (hY : 1 ≤ Y) {L : ℝ} (hfloor : μ₀ ≤ wallFloor T σ Y + L) :
    ‖thresholdOperator E T σ L Y‖
      ≤ (K₂ * (1 + |Y|) ^ (1 / 2 + σ)) * (μ₀⁻¹ + (μ₀⁻¹) ^ 3 * (3 + Real.pi) * (1 + Y)⁻¹) := by
  have hYabs : |Y| = Y := abs_of_nonneg (by linarith)
  refine (norm_thresholdOperator_le' hσ0 hσ1 hμ hb₂ (by rw [hYabs]; exact hY) hfloor).trans
    (le_of_eq ?_)
  rw [hYabs]

/-! ## The decomposition -/

/-- **The moving part of the propagated tail splits into four block averages.**  The two boundary
terms at the moving endpoint lose their transport and become the resolvent averages; the two at the
threshold are a fixed vector propagated by the transport; the remaining integral is the Hardy
tail. -/
theorem stripPropagator_movingTail_decomposition_abs
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m Y x μ₀ : ℝ} (hg : IntegrableOn g (Icc m (m + 1)))
    (hx1 : 1 ≤ |x|) (hY1 : 1 ≤ |Y|) (hμ : 0 < μ₀)
    (hgapx : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L)
    (hgapY : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ Y + L)
    (hgapI : ∀ L ∈ Icc m (m + 1), ∀ t ∈ uIcc Y x, 0 < wallFloor T σ t + L) :
    stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (∫ t in Y..x, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (blockSource g m t))
      = (-(Complex.I) / 2 : ℂ) •
          ((Complex.I : ℂ) • firstBoundaryBlock T g m σ x
            + secondBoundary T g m σ x
            - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) (thresholdVector E T g m σ Y)
            - tailRemainder E T g m σ Y x) := by
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_stripPropagatorInv_line hT hE hσ0 hσ1
  set H : X →L[ℂ] X := stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) with hHdef
  set S : Set ℝ := Icc m (m + 1) with hSdef
  set phase : ℝ → ℂ := fun L => Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) with hphase
  -- the three operator families
  set Ax : ℝ → (X →L[ℂ] X) := fun L => invFamily (wallGeneratorShift T σ L) x with hAx
  set Px : ℝ → (X →L[ℂ] X) :=
    fun L => invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x with hPx
  set Th : ℝ → (X →L[ℂ] X) := fun L => thresholdOperator E T σ L Y with hTh
  have hgapx' : ∀ L ∈ S, 0 < wallFloor T σ x + L := fun L hL =>
    lt_of_lt_of_le hμ (hgapx L hL)
  have hgapY' : ∀ L ∈ S, 0 < wallFloor T σ Y + L := fun L hL =>
    lt_of_lt_of_le hμ (hgapY L hL)
  -- integrability of the three named pieces
  have hI1 : IntegrableOn (fun L => phase L • Ax L (g L)) S :=
    integrableOn_phase_apply_of_continuousOn measurableSet_Icc
      (continuousOn_invFamily_position (T := T) hσ0 hσ1 hgapx')
      (fun L hL => norm_invFamily_wallGeneratorShift_le' hσ0 hσ1 hμ (hgapx L hL)) hg
      (continuous_expPhase_block x) (fun L => norm_expPhase L x)
  have hI2 : IntegrableOn (fun L => phase L • Px L (g L)) S :=
    integrableOn_phase_apply_of_continuousOn measurableSet_Icc
      (continuousOn_invFamilyProduct_position (T := T) hσ0 hσ1 hgapx')
      (fun L hL => norm_invFamilyProduct_wallGeneratorShift_le' hσ0 hσ1 hμ hx1 (hgapx L hL)) hg
      (continuous_expPhase_block x) (fun L => norm_expPhase L x)
  have hI3 : IntegrableOn (fun L => Th L (g L)) S := by
    have h := integrableOn_phase_apply_of_continuousOn (A := Th) (S := S) measurableSet_Icc
      (continuousOn_thresholdOperator_position (E := E) (T := T) hσ0 hσ1 hgapY')
      (fun L hL => norm_thresholdOperator_le' hσ0 hσ1 hμ hb₂ hY1 (hgapY L hL)) hg
      (φ := fun _ => (1 : ℂ)) continuous_const (fun _ => by simp)
    simpa using h
  have htot : IntegrableOn
      (fun L => H (∫ t in Y..x, wallPhaseMap E T σ L t (g L))) S :=
    (H.restrictScalars ℝ).integrable_comp
      (integrableOn_blockPhaseIntegral' hEdiff hE hEne hσ0 hσ1 hg Y x)
  set α₄ : ℝ → X := fun L => H ((∫ t in Y..x, wallPhaseMap E T σ L t
      * invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
          (wallGeneratorD2 X σ) t) (g L)) with hα₄
  -- the pointwise expansion
  have hpt : ∀ L ∈ S, H (∫ t in Y..x, wallPhaseMap E T σ L t (g L))
      = (Complex.I : ℂ) • (phase L • Ax L (g L)) + phase L • Px L (g L)
        - H (Th L (g L)) - α₄ L := by
    intro L hL
    rw [integral_wallPhaseMap_apply_ibp hEdiff hE hEne hσ0 hσ1 (hgapI L hL) (g L)]
    exact stripPropagator_expansion_apply hE hσ0 hσ1 L x Y _ (g L)
  -- integrability of the remaining piece
  have hA : Integrable (fun L => (Complex.I : ℂ) • (phase L • Ax L (g L)))
      (volume.restrict S) := Integrable.smul (Complex.I : ℂ) hI1
  have hC : Integrable (fun L => H (Th L (g L))) (volume.restrict S) :=
    ContinuousLinearMap.integrable_comp H hI3
  have hAB : Integrable (fun L => (Complex.I : ℂ) • (phase L • Ax L (g L))
      + phase L • Px L (g L)) (volume.restrict S) := Integrable.add hA hI2
  have hsum : Integrable (fun L => (Complex.I : ℂ) • (phase L • Ax L (g L))
      + phase L • Px L (g L) - H (Th L (g L))) (volume.restrict S) :=
    Integrable.sub hAB hC
  have hI4 : IntegrableOn α₄ S := by
    have hcomb : Integrable (fun L =>
        ((Complex.I : ℂ) • (phase L • Ax L (g L)) + phase L • Px L (g L)
          - H (Th L (g L))) - H (∫ t in Y..x, wallPhaseMap E T σ L t (g L)))
        (volume.restrict S) := Integrable.sub hsum htot
    refine Integrable.congr hcomb ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL
    have h := hpt L hL
    rw [h]
    abel
  -- split the block integral
  have hsplit : (∫ L in S, H (∫ t in Y..x, wallPhaseMap E T σ L t (g L)))
      = ((Complex.I : ℂ) • ∫ L in S, phase L • Ax L (g L))
        + (∫ L in S, phase L • Px L (g L))
        - (∫ L in S, H (Th L (g L))) - ∫ L in S, α₄ L := by
    rw [setIntegral_congr_fun measurableSet_Icc hpt, integral_sub hsum hI4,
      integral_sub hAB hC, integral_add hA hI2, integral_smul]
  -- assemble
  have hcomm : (∫ L in S, H (∫ t in Y..x, wallPhaseMap E T σ L t (g L)))
      = H (∫ L in S, ∫ t in Y..x, wallPhaseMap E T σ L t (g L)) :=
    ContinuousLinearMap.integral_comp_comm H
      (integrableOn_blockPhaseIntegral' hEdiff hE hEne hσ0 hσ1 hg Y x)
  have hTh : (∫ L in S, H (Th L (g L))) = H (thresholdVector E T g m σ Y) :=
    ContinuousLinearMap.integral_comp_comm H hI3
  rw [integral_blockSource_swap' hEdiff hE hEne hσ0 hσ1 hg Y x, map_smul]
  congr 1
  rw [← hcomm, hsplit, hTh]
  rfl

/-- **The moving part of the propagated tail, on the outward ray.** -/
theorem stripPropagator_movingTail_decomposition
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m Y x μ₀ : ℝ} (hg : IntegrableOn g (Icc m (m + 1)))
    (hYx : Y ≤ x) (hY1 : 1 ≤ Y) (hμ : 0 < μ₀)
    (hgapx : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L)
    (hgapY : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ Y + L)
    (hgapI : ∀ L ∈ Icc m (m + 1), ∀ t ∈ uIcc Y x, 0 < wallFloor T σ t + L) :
    stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (∫ t in Y..x, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (blockSource g m t))
      = (-(Complex.I) / 2 : ℂ) •
          ((Complex.I : ℂ) • firstBoundaryBlock T g m σ x
            + secondBoundary T g m σ x
            - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) (thresholdVector E T g m σ Y)
            - tailRemainder E T g m σ Y x) :=
  stripPropagator_movingTail_decomposition_abs hEdiff hE hEne hT hσ0 hσ1 hg
    (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]; linarith)
    (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Y)]; exact hY1) hμ hgapx hgapY hgapI

end GaloisForLFunctions.RHTower
