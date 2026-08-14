import GaloisForLFunctions.RHTower.SuzukiOnePrimeTerminalSimilarityTransport
import GaloisForLFunctions.RHTower.SuzukiGammaForcedStripHardy
import GaloisForLFunctions.HTGeometry.CompoundExponentialTransport

/-!
# Forced Gamma-strip Hardy transport for the literal one-prime terminal block

The physical one-prime terminal adjacency is nonnormal, so the corpus self-adjoint forced-strip
theorem cannot be applied to it directly.  This module promotes the diagonal matrix similarity to
a continuous linear equivalence on the literal two-coordinate Hilbert state, conjugates the full
complex-frequency propagator and its inverse, and commutes that equivalence through the Bochner
variation-of-constants integral.

Consequently the literal forced solution is exactly the similarity image of a self-adjoint swap
solution.  Its two-sided shifted-line `L²` admission follows from the first moment of the original
forcing, with no self-adjointness assumption on the physical adjacency and no transformed-source
hypothesis.
-/

open Complex MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.L2Operator

namespace RHTower

noncomputable section

abbrev OnePrimeTerminalState := EuclideanSpace ℂ (Fin 2)

def onePrimeTerminalAdjacencyCLM : OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) onePrimeTerminalAdjacency

def onePrimeTerminalSymmetricAdjacencyCLM :
    OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) onePrimeTerminalSymmetricAdjacency

def onePrimeTerminalSimilarityCLM : OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) onePrimeTerminalSimilarity

def onePrimeTerminalSimilarityInvCLM : OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) onePrimeTerminalSimilarityInv

def onePrimeTerminalSimilarityCLMUnit :
    (OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState)ˣ :=
  Units.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).toMonoidHom
    onePrimeTerminalSimilarityUnit

@[simp] theorem coe_onePrimeTerminalSimilarityCLMUnit :
    (onePrimeTerminalSimilarityCLMUnit :
      OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState) = onePrimeTerminalSimilarityCLM := by
  rfl

@[simp] theorem coe_onePrimeTerminalSimilarityCLMUnit_inv :
    ((onePrimeTerminalSimilarityCLMUnit⁻¹ :
      (OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState)ˣ) :
        OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState) =
      onePrimeTerminalSimilarityInvCLM := by
  rfl

def onePrimeTerminalSimilarityCLE : OnePrimeTerminalState ≃L[ℂ] OnePrimeTerminalState :=
  ContinuousLinearEquiv.mk
    (LinearEquiv.ofLinear onePrimeTerminalSimilarityCLM.toLinearMap
      onePrimeTerminalSimilarityInvCLM.toLinearMap
      (by
        apply LinearMap.ext
        intro v
        change onePrimeTerminalSimilarityCLM
          (onePrimeTerminalSimilarityInvCLM v) = v
        change Matrix.toEuclideanCLM (𝕜 := ℂ)
          onePrimeTerminalSimilarity
            (Matrix.toEuclideanCLM (𝕜 := ℂ)
              onePrimeTerminalSimilarityInv v) = v
        have hmap := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
            Matrix.toEuclideanCLM (𝕜 := ℂ) M)
          onePrimeTerminalSimilarity_mul_inv
        simpa using congrArg
          (fun T : OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState => T v) hmap)
      (by
        apply LinearMap.ext
        intro v
        change onePrimeTerminalSimilarityInvCLM
          (onePrimeTerminalSimilarityCLM v) = v
        change Matrix.toEuclideanCLM (𝕜 := ℂ)
          onePrimeTerminalSimilarityInv
            (Matrix.toEuclideanCLM (𝕜 := ℂ)
              onePrimeTerminalSimilarity v) = v
        have hmap := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
            Matrix.toEuclideanCLM (𝕜 := ℂ) M)
          onePrimeTerminalSimilarityInv_mul
        simpa using congrArg
          (fun T : OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState => T v) hmap))
    onePrimeTerminalSimilarityCLM.continuous
    onePrimeTerminalSimilarityInvCLM.continuous

@[simp] theorem onePrimeTerminalSimilarityCLE_apply (v : OnePrimeTerminalState) :
    onePrimeTerminalSimilarityCLE v = onePrimeTerminalSimilarityCLM v := rfl

@[simp] theorem onePrimeTerminalSimilarityCLE_symm_apply (v : OnePrimeTerminalState) :
    onePrimeTerminalSimilarityCLE.symm v = onePrimeTerminalSimilarityInvCLM v := rfl

theorem onePrimeTerminalAdjacencyCLM_eq_similarity :
    onePrimeTerminalAdjacencyCLM =
      onePrimeTerminalSimilarityCLM * onePrimeTerminalSymmetricAdjacencyCLM *
        onePrimeTerminalSimilarityInvCLM := by
  change Matrix.toEuclideanCLM (𝕜 := ℂ) onePrimeTerminalAdjacency = _
  rw [onePrimeTerminalAdjacency_eq_similarity]
  simp [onePrimeTerminalSimilarityCLM, onePrimeTerminalSymmetricAdjacencyCLM,
    onePrimeTerminalSimilarityInvCLM]

theorem onePrimeTerminalSymmetricAdjacencyCLM_isSelfAdjoint :
    IsSelfAdjoint onePrimeTerminalSymmetricAdjacencyCLM := by
  exact GaloisForLFunctions.HTGeometry.isSelfAdjoint_toEuclideanCLM
    onePrimeTerminalSymmetricAdjacency_isHermitian

theorem exp_smul_onePrimeTerminalAdjacencyCLM_eq_similarity (alpha : ℂ) :
    NormedSpace.exp (alpha • onePrimeTerminalAdjacencyCLM) =
      onePrimeTerminalSimilarityCLM *
        NormedSpace.exp (alpha • onePrimeTerminalSymmetricAdjacencyCLM) *
          onePrimeTerminalSimilarityInvCLM := by
  letI : NormedAlgebra ℚ
      (OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState) :=
    .restrictScalars ℚ ℂ _
  have harg : alpha • onePrimeTerminalAdjacencyCLM =
      (onePrimeTerminalSimilarityCLMUnit :
          OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState) *
        (alpha • onePrimeTerminalSymmetricAdjacencyCLM) *
          ((onePrimeTerminalSimilarityCLMUnit⁻¹ :
            (OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState)ˣ) :
              OnePrimeTerminalState →L[ℂ] OnePrimeTerminalState) := by
    rw [coe_onePrimeTerminalSimilarityCLMUnit,
      coe_onePrimeTerminalSimilarityCLMUnit_inv,
      onePrimeTerminalAdjacencyCLM_eq_similarity]
    ext v
    simp
  rw [harg]
  exact NormedSpace.exp_units_conj onePrimeTerminalSimilarityCLMUnit
    (alpha • onePrimeTerminalSymmetricAdjacencyCLM)

@[simp] theorem onePrimeTerminalSimilarityInvCLM_apply_similarityCLM
    (v : OnePrimeTerminalState) :
    onePrimeTerminalSimilarityInvCLM (onePrimeTerminalSimilarityCLM v) = v := by
  exact onePrimeTerminalSimilarityCLE.symm_apply_apply v

@[simp] theorem onePrimeTerminalSimilarityCLM_apply_invCLM
    (v : OnePrimeTerminalState) :
    onePrimeTerminalSimilarityCLM (onePrimeTerminalSimilarityInvCLM v) = v := by
  exact onePrimeTerminalSimilarityCLE.apply_symm_apply v

/-- The full shifted Gamma propagator for the literal terminal block is conjugate to the
self-adjoint swap propagator at every complex frequency. -/
theorem stripPropagator_onePrimeTerminalAdjacencyCLM_eq_similarity
    (E : ℂ → ℂ) (z : ℂ) :
    GaloisForLFunctions.RHTower.stripPropagator E onePrimeTerminalAdjacencyCLM z =
      onePrimeTerminalSimilarityCLM *
        GaloisForLFunctions.RHTower.stripPropagator E
          onePrimeTerminalSymmetricAdjacencyCLM z *
            onePrimeTerminalSimilarityInvCLM := by
  have halpha : -(Complex.I / 2) * z = -(Complex.I / 2 * z) := by ring
  have hphase : (-(Complex.I / 2 * z)) •
      onePrimeTerminalSymmetricAdjacencyCLM =
      -((Complex.I / 2 * z) • onePrimeTerminalSymmetricAdjacencyCLM) :=
    by ext v; simp
  rw [GaloisForLFunctions.RHTower.stripPropagator,
    GaloisForLFunctions.RHTower.stripTransport,
    exp_smul_onePrimeTerminalAdjacencyCLM_eq_similarity]
  rw [halpha, hphase]
  ext v
  simp [GaloisForLFunctions.RHTower.stripPropagator,
    GaloisForLFunctions.RHTower.stripTransport, neg_smul]

/-- The inverse shifted Gamma propagator obeys the same exact similarity. -/
theorem stripPropagatorInv_onePrimeTerminalAdjacencyCLM_eq_similarity
    (E : ℂ → ℂ) (z : ℂ) :
    GaloisForLFunctions.RHTower.stripPropagatorInv E onePrimeTerminalAdjacencyCLM z =
      onePrimeTerminalSimilarityCLM *
        GaloisForLFunctions.RHTower.stripPropagatorInv E
          onePrimeTerminalSymmetricAdjacencyCLM z *
            onePrimeTerminalSimilarityInvCLM := by
  rw [GaloisForLFunctions.RHTower.stripPropagatorInv,
    exp_smul_onePrimeTerminalAdjacencyCLM_eq_similarity]
  ext v
  simp [GaloisForLFunctions.RHTower.stripPropagatorInv]

/-- Exact variation-of-constants transport.  Both the state and forcing are transformed by the
inverse diagonal similarity, and the literal nonnormal solution is the forward image of the
self-adjoint one. -/
theorem forcedStripRay_onePrimeTerminalAdjacencyCLM_eq_similarity
    (E : ℂ → ℂ) (c : OnePrimeTerminalState) (b : ℝ → OnePrimeTerminalState)
    (σ ε x : ℝ) :
    GaloisForLFunctions.RHTower.forcedStripRay E onePrimeTerminalAdjacencyCLM
        c b σ ε x =
      onePrimeTerminalSimilarityCLM
        (GaloisForLFunctions.RHTower.forcedStripRay E
          onePrimeTerminalSymmetricAdjacencyCLM
          (onePrimeTerminalSimilarityInvCLM c)
          (fun t => onePrimeTerminalSimilarityInvCLM (b t)) σ ε x) := by
  have hintegrand :
      (fun t : ℝ =>
        GaloisForLFunctions.RHTower.stripPropagatorInv E
          onePrimeTerminalAdjacencyCLM
          ((((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I)) (b (ε * t))) =
      fun t : ℝ => onePrimeTerminalSimilarityCLM
        (GaloisForLFunctions.RHTower.stripPropagatorInv E
          onePrimeTerminalSymmetricAdjacencyCLM
          ((((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I))
            (onePrimeTerminalSimilarityInvCLM (b (ε * t)))) := by
    funext t
    rw [stripPropagatorInv_onePrimeTerminalAdjacencyCLM_eq_similarity]
    simp
  have hint :
      (∫ t in Ioc (1 : ℝ) x,
        GaloisForLFunctions.RHTower.stripPropagatorInv E
          onePrimeTerminalAdjacencyCLM
          ((((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I)) (b (ε * t))) =
      onePrimeTerminalSimilarityCLM
        (∫ t in Ioc (1 : ℝ) x,
          GaloisForLFunctions.RHTower.stripPropagatorInv E
            onePrimeTerminalSymmetricAdjacencyCLM
            ((((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I))
              (onePrimeTerminalSimilarityInvCLM (b (ε * t)))) := by
    rw [hintegrand]
    exact onePrimeTerminalSimilarityCLE.integral_comp_comm _
  rw [GaloisForLFunctions.RHTower.forcedStripRay,
    GaloisForLFunctions.RHTower.forcedStripRay,
    stripPropagator_onePrimeTerminalAdjacencyCLM_eq_similarity, hint]
  simp

/-- The literal nonnormal terminal block inherits the full forced Gamma-strip Hardy theorem.
The only analytic input is the first-moment condition on the original physical forcing; the
similarity transform introduces no new source hypothesis. -/
theorem lintegral_enorm_sq_forcedStripRay_onePrimeTerminal_lt_top
    {E : ℂ → ℂ}
    (hE : ∀ z ∈ GaloisForLFunctions.RHTower.imStrip (-1) 1,
      E z ^ 2 = GaloisForLFunctions.RHTower.gammaRatio z)
    (c : OnePrimeTerminalState) (b : ℝ → OnePrimeTerminalState)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {ε : ℝ} (hε : |ε| = 1)
    (hmeas : AEStronglyMeasurable (fun t : ℝ => b (ε * t))
      (volume.restrict (Ioi (1 : ℝ))))
    (hmom : ∫⁻ t in Ioi (1 : ℝ), ‖(t : ℝ) • b (ε * t)‖ₑ ^ 2 < ⊤) :
    ∫⁻ x in Ioi (1 : ℝ),
      ‖GaloisForLFunctions.RHTower.forcedStripRay E onePrimeTerminalAdjacencyCLM
        c b σ ε x‖ₑ ^ 2 < ⊤ := by
  let b' : ℝ → OnePrimeTerminalState :=
    fun t => onePrimeTerminalSimilarityInvCLM (b t)
  have hmeas' : AEMeasurable (fun t : ℝ => ‖b' (ε * t)‖ₑ)
      (volume.restrict (Ioi (1 : ℝ))) := by
    exact (onePrimeTerminalSimilarityInvCLM.continuous.comp_aestronglyMeasurable
      hmeas).enorm
  set Kin : ℝ≥0∞ := ENNReal.ofReal ‖onePrimeTerminalSimilarityInvCLM‖ with hKin
  have hmom' : ∫⁻ t in Ioi (1 : ℝ), ‖(t : ℝ) • b' (ε * t)‖ₑ ^ 2 < ⊤ := by
    have hpoint : ∀ t : ℝ,
        ‖(t : ℝ) • b' (ε * t)‖ₑ ^ 2 ≤
          Kin ^ 2 * ‖(t : ℝ) • b (ε * t)‖ₑ ^ 2 := by
      intro t
      have hnorm : ‖(t : ℝ) • b' (ε * t)‖ ≤
          ‖onePrimeTerminalSimilarityInvCLM‖ * ‖(t : ℝ) • b (ε * t)‖ := by
        have hout : (((t : ℝ) : ℂ)) •
            onePrimeTerminalSimilarityInvCLM (b (ε * t)) =
            (t : ℝ) • onePrimeTerminalSimilarityInvCLM (b (ε * t)) := by
          rw [← Complex.coe_algebraMap, algebraMap_smul]
        have hin : (((t : ℝ) : ℂ)) • b (ε * t) =
            (t : ℝ) • b (ε * t) := by
          rw [← Complex.coe_algebraMap, algebraMap_smul]
        change ‖(t : ℝ) • onePrimeTerminalSimilarityInvCLM (b (ε * t))‖ ≤ _
        rw [← hout, ← hin, ← map_smul]
        exact ContinuousLinearMap.le_opNorm _ _
      have henorm : ‖(t : ℝ) • b' (ε * t)‖ₑ ≤
          Kin * ‖(t : ℝ) • b (ε * t)‖ₑ := by
        rw [hKin, ← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_mul (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hnorm
      calc
        ‖(t : ℝ) • b' (ε * t)‖ₑ ^ 2 ≤
            (Kin * ‖(t : ℝ) • b (ε * t)‖ₑ) ^ 2 := by gcongr
        _ = Kin ^ 2 * ‖(t : ℝ) • b (ε * t)‖ₑ ^ 2 := by ring
    calc
      (∫⁻ t in Ioi (1 : ℝ), ‖(t : ℝ) • b' (ε * t)‖ₑ ^ 2) ≤
          ∫⁻ t in Ioi (1 : ℝ),
            Kin ^ 2 * ‖(t : ℝ) • b (ε * t)‖ₑ ^ 2 :=
        setLIntegral_mono' measurableSet_Ioi fun t _ => hpoint t
      _ = Kin ^ 2 *
          ∫⁻ t in Ioi (1 : ℝ), ‖(t : ℝ) • b (ε * t)‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ (by simp [hKin])]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hmom
  have hbase :=
    GaloisForLFunctions.RHTower.lintegral_enorm_sq_forcedStripRay_lt_top
      onePrimeTerminalSymmetricAdjacencyCLM_isSelfAdjoint hE
      (onePrimeTerminalSimilarityInvCLM c) b' hσ0 hσ1 hε hmeas' hmom'
  set Kout : ℝ≥0∞ := ENNReal.ofReal ‖onePrimeTerminalSimilarityCLM‖ with hKout
  have hpointOut : ∀ x : ℝ,
      ‖GaloisForLFunctions.RHTower.forcedStripRay E onePrimeTerminalAdjacencyCLM
          c b σ ε x‖ₑ ^ 2 ≤
        Kout ^ 2 *
          ‖GaloisForLFunctions.RHTower.forcedStripRay E
            onePrimeTerminalSymmetricAdjacencyCLM
            (onePrimeTerminalSimilarityInvCLM c) b' σ ε x‖ₑ ^ 2 := by
    intro x
    rw [forcedStripRay_onePrimeTerminalAdjacencyCLM_eq_similarity]
    have hnorm := ContinuousLinearMap.le_opNorm onePrimeTerminalSimilarityCLM
      (GaloisForLFunctions.RHTower.forcedStripRay E
        onePrimeTerminalSymmetricAdjacencyCLM
        (onePrimeTerminalSimilarityInvCLM c) b' σ ε x)
    have henorm :
        ‖onePrimeTerminalSimilarityCLM
          (GaloisForLFunctions.RHTower.forcedStripRay E
            onePrimeTerminalSymmetricAdjacencyCLM
            (onePrimeTerminalSimilarityInvCLM c) b' σ ε x)‖ₑ ≤
          Kout * ‖GaloisForLFunctions.RHTower.forcedStripRay E
            onePrimeTerminalSymmetricAdjacencyCLM
            (onePrimeTerminalSimilarityInvCLM c) b' σ ε x‖ₑ := by
      rw [hKout, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hnorm
    calc
      ‖onePrimeTerminalSimilarityCLM
          (GaloisForLFunctions.RHTower.forcedStripRay E
            onePrimeTerminalSymmetricAdjacencyCLM
            (onePrimeTerminalSimilarityInvCLM c) b' σ ε x)‖ₑ ^ 2 ≤
          (Kout * ‖GaloisForLFunctions.RHTower.forcedStripRay E
            onePrimeTerminalSymmetricAdjacencyCLM
            (onePrimeTerminalSimilarityInvCLM c) b' σ ε x‖ₑ) ^ 2 := by gcongr
      _ = Kout ^ 2 *
          ‖GaloisForLFunctions.RHTower.forcedStripRay E
            onePrimeTerminalSymmetricAdjacencyCLM
            (onePrimeTerminalSimilarityInvCLM c) b' σ ε x‖ₑ ^ 2 := by ring
  calc
    (∫⁻ x in Ioi (1 : ℝ),
      ‖GaloisForLFunctions.RHTower.forcedStripRay E onePrimeTerminalAdjacencyCLM
        c b σ ε x‖ₑ ^ 2) ≤
        ∫⁻ x in Ioi (1 : ℝ), Kout ^ 2 *
          ‖GaloisForLFunctions.RHTower.forcedStripRay E
            onePrimeTerminalSymmetricAdjacencyCLM
            (onePrimeTerminalSimilarityInvCLM c) b' σ ε x‖ₑ ^ 2 :=
      setLIntegral_mono' measurableSet_Ioi fun x _ => hpointOut x
    _ = Kout ^ 2 *
        ∫⁻ x in Ioi (1 : ℝ),
          ‖GaloisForLFunctions.RHTower.forcedStripRay E
            onePrimeTerminalSymmetricAdjacencyCLM
            (onePrimeTerminalSimilarityInvCLM c) b' σ ε x‖ₑ ^ 2 := by
      rw [lintegral_const_mul' _ _ (by simp [hKout])]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hbase

end

end RHTower
