import GaloisForLFunctions.HilbertMetric.CCRCompletionWitness
import GaloisForLFunctions.HilbertMetric.CCRPowerConcavity

/-!
# The scale calibration of a CCR family

The scale-sandwich law calibrates an abstract log-volume against a CCR family through two
hypotheses: its logarithmic scale mean is the mean energy, and its logarithmic scale variance is the
number variance.  The two are not independent.  Differentiating the first turns the second into a
statement about the family alone — the mean energy has logarithmic derivative equal to the number
variance — and that is the whole content of the calibration.

Scalar compressions with the mode-indexed unit leakage make the calibration explicit: their number
variance *equals* their mean energy, so the corpus bound `variance ≤ |I| · mean` is attained exactly
in one mode, and rescaling them by `√t` realizes the calibration pair on an actual CCR family.

* **`ccr_calibration_energy_law`** — the two calibrations are one differential law;
* **`ccrNumberVariance_scalar_eq_ccrMeanEnergy`** — equality of the two energies for scalar
  compressions;
* **`ccr_scaleSandwich_sqrtScalar`** — an unconditional instance of the scale-sandwich law.
-/

namespace GaloisForLFunctions.HilbertMetric

open scoped BigOperators

noncomputable section

variable {I n m : Type*} [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

/-! ## The calibration pair is one differential law -/

omit [DecidableEq I] [DecidableEq n] in
/-- The mean calibration alone already differentiates: the mean energy of the family inherits the
derivative of `t · F₁ t`. -/
theorem hasDerivAt_ccrMeanEnergy_of_meanCalibration
    (A : ℝ → I → Matrix n n ℝ) {F₁ F₂ : ℝ → ℝ}
    (hF₁ : ∀ t, 0 < t → HasDerivAt F₁ (F₂ t) t)
    (hmean : ∀ t, 0 < t → logarithmicScaleMean F₁ t = ccrMeanEnergy (A t))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ccrMeanEnergy (A s)) (F₁ t + t * F₂ t) t := by
  have hprod : HasDerivAt (fun s => s * F₁ s) (1 * F₁ t + t * F₂ t) t :=
    (hasDerivAt_id t).mul (hF₁ t ht)
  have heq : (fun s => ccrMeanEnergy (A s)) =ᶠ[nhds t] fun s => s * F₁ s := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact (hmean s hs).symm
  have := hprod.congr_of_eventuallyEq heq
  simpa using this

omit [DecidableEq I] [DecidableEq n] [DecidableEq m] in
/-- **The two scale calibrations are a single differential law of the family.**  A calibrated CCR
family has mean energy whose logarithmic derivative is the number variance; no property of the
log-volume survives beyond this. -/
theorem ccr_calibration_energy_law
    (A : ℝ → I → Matrix n n ℝ) (B : ℝ → I → Matrix n m ℝ) {F₁ F₂ : ℝ → ℝ}
    (hF₁ : ∀ t, 0 < t → HasDerivAt F₁ (F₂ t) t)
    (hmean : ∀ t, 0 < t → logarithmicScaleMean F₁ t = ccrMeanEnergy (A t))
    (hvariance : ∀ t, 0 < t →
      logarithmicScaleVariance F₁ F₂ t = ccrNumberVariance (A t) (B t))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ccrMeanEnergy (A s))
      (ccrNumberVariance (A t) (B t) / t) t := by
  have h := hasDerivAt_ccrMeanEnergy_of_meanCalibration A hF₁ hmean ht
  have hv : ccrNumberVariance (A t) (B t) / t = F₁ t + t * F₂ t := by
    rw [← hvariance t ht, logarithmicScaleVariance]
    field_simp
  rwa [hv]

/-! ## Scalar compressions -/

omit [DecidableEq I] in
/-- The Hilbert–Schmidt energy of a scalar matrix. -/
theorem matrixHilbertSchmidtEnergy_smul_one (c : ℝ) :
    matrixHilbertSchmidtEnergy (c • (1 : Matrix n n ℝ)) =
      (Fintype.card n : ℝ) * c ^ 2 := by
  have hentry : ∀ a b : n, (c • (1 : Matrix n n ℝ)) a b ^ 2 =
      if a = b then c ^ 2 else 0 := by
    intro a b
    by_cases hab : a = b <;> simp [hab]
  simp only [matrixHilbertSchmidtEnergy]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hentry a b]
  simp [Finset.sum_ite_eq, Finset.card_univ]

omit [DecidableEq I] in
/-- The mean energy of a scalar compression tuple. -/
theorem ccrMeanEnergy_scalar (c : I → ℝ) :
    ccrMeanEnergy (fun i => c i • (1 : Matrix n n ℝ)) =
      (Fintype.card n : ℝ) * ∑ i, (c i) ^ 2 := by
  simp only [ccrMeanEnergy]
  rw [Finset.sum_congr rfl fun i _ => matrixHilbertSchmidtEnergy_smul_one (n := n) (c i),
    ← Finset.mul_sum]

/-- The leakage trace of a scalar compression against the mode-indexed unit leakage. -/
theorem ccrLeakageTrace_scalar (c : I → ℝ) (p : I × n) (a : n) :
    ccrLeakageTrace (fun i => c i • (1 : Matrix n n ℝ))
        (unitModeLeakage (I := I) (n := n)) p a =
      if p.2 = a then c p.1 else 0 := by
  obtain ⟨j, q⟩ := p
  simp only [ccrLeakageTrace, unitModeLeakage, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Prod.mk.injEq]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single q]
  · rw [Finset.sum_eq_single j]
    · by_cases hqa : q = a <;> simp [hqa]
    · intro i _ hi
      simp [Ne.symm hi]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ q) h

/-- **The number variance of a scalar compression equals its mean energy.**  Hence the corpus bound
`variance ≤ |I| · mean` is attained exactly when the tuple has one mode. -/
theorem ccrNumberVariance_scalar_eq_ccrMeanEnergy (c : I → ℝ) :
    ccrNumberVariance (fun i => c i • (1 : Matrix n n ℝ))
        (unitModeLeakage (I := I) (n := n)) =
      ccrMeanEnergy (fun i => c i • (1 : Matrix n n ℝ)) := by
  rw [ccrMeanEnergy_scalar, ccrNumberVariance, rectangularMatrixHilbertSchmidtEnergy]
  have hentry : ∀ (p : I × n) (a : n),
      ccrLeakageTrace (fun i => c i • (1 : Matrix n n ℝ))
          (unitModeLeakage (I := I) (n := n)) p a ^ 2 =
        if p.2 = a then (c p.1) ^ 2 else 0 := by
    intro p a
    rw [ccrLeakageTrace_scalar]
    by_cases hpa : p.2 = a <;> simp [hpa]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => hentry p a]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]

/-! ## An explicit calibrated family -/

/-- The scalar compression tuple scaled so that its mean energy is linear in the scale. -/
def sqrtScalarCompression (I : Type*) [Fintype I] (n : Type*) [Fintype n] [DecidableEq n]
    (t : ℝ) : I → Matrix n n ℝ :=
  fun _ => Real.sqrt (t / Fintype.card I) • (1 : Matrix n n ℝ)

omit [DecidableEq I] in
theorem ccrMeanEnergy_sqrtScalarCompression [Nonempty I] {t : ℝ} (ht : 0 ≤ t) :
    ccrMeanEnergy (sqrtScalarCompression I n t) = (Fintype.card n : ℝ) * t := by
  have hI : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have hnn : (0 : ℝ) ≤ t / Fintype.card I := div_nonneg ht hI.le
  show ccrMeanEnergy
      (fun _ : I => Real.sqrt (t / (Fintype.card I : ℝ)) • (1 : Matrix n n ℝ)) = _
  rw [ccrMeanEnergy_scalar]
  rw [Finset.sum_congr rfl fun i _ => Real.sq_sqrt hnn]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem ccrNumberVariance_sqrtScalarCompression [Nonempty I] {t : ℝ} (ht : 0 ≤ t) :
    ccrNumberVariance (sqrtScalarCompression I n t) (unitModeLeakage (I := I) (n := n)) =
      (Fintype.card n : ℝ) * t := by
  show ccrNumberVariance
      (fun _ : I => Real.sqrt (t / (Fintype.card I : ℝ)) • (1 : Matrix n n ℝ))
      (unitModeLeakage (I := I) (n := n)) = _
  rw [ccrNumberVariance_scalar_eq_ccrMeanEnergy]
  exact ccrMeanEnergy_sqrtScalarCompression (I := I) (n := n) ht

/-- **An unconditional instance of the CCR scale-sandwich law.**  The `√t`-scaled scalar
compressions with the mode-indexed unit leakage satisfy both calibrations with the linear
log-volume `F t = |n| · t`, so the sandwich law applies with no hypothesis at all. -/
theorem ccr_scaleSandwich_sqrtScalar [Nonempty I] :
    ConvexOn ℝ Set.univ
        (logarithmicReparametrization (fun t => (Fintype.card n : ℝ) * t)) ∧
      ConcaveOn ℝ (Set.Ioi 0)
        (dimensionPowerReparametrization (Fintype.card I : ℝ)
          (fun t => (Fintype.card n : ℝ) * t)) := by
  refine ccr_logarithmicConvex_dimensionPowerConcave
    (sqrtScalarCompression I n) (fun _ => unitModeLeakage)
    (fun t _ => isCommutingCCRCompression_scalar _)
    (fun t _ => isCCRCompletion_scalar _)
    Fintype.card_pos
    (F₁ := fun _ => (Fintype.card n : ℝ)) (F₂ := fun _ => 0)
    (fun t _ => by simpa using (hasDerivAt_id t).const_mul ((Fintype.card n : ℝ)))
    (fun t _ => hasDerivAt_const t ((Fintype.card n : ℝ))) ?_ ?_
  · intro t ht
    rw [logarithmicScaleMean, ccrMeanEnergy_sqrtScalarCompression (I := I) (n := n) ht.le]
    ring
  · intro t ht
    rw [logarithmicScaleVariance,
      ccrNumberVariance_sqrtScalarCompression (I := I) (n := n) ht.le]
    ring

/-- **The calibration pair is jointly realizable.**  A commuting CCR family with a completion, and
a log-volume whose logarithmic scale mean and variance are its mean energy and number variance,
exist together — so the calibrated scale laws are not vacuous. -/
theorem exists_calibrated_ccrFamily [Nonempty I] :
    ∃ (A : ℝ → I → Matrix n n ℝ) (B : ℝ → I → Matrix n (I × n) ℝ) (F F₁ F₂ : ℝ → ℝ),
      (∀ t, 0 < t → IsCommutingCCRCompression (A t)) ∧
      (∀ t, 0 < t → IsCCRCompletion (A t) (B t)) ∧
      (∀ t, 0 < t → HasDerivAt F (F₁ t) t) ∧
      (∀ t, 0 < t → HasDerivAt F₁ (F₂ t) t) ∧
      (∀ t, 0 < t → logarithmicScaleMean F₁ t = ccrMeanEnergy (A t)) ∧
      (∀ t, 0 < t → logarithmicScaleVariance F₁ F₂ t = ccrNumberVariance (A t) (B t)) := by
  refine ⟨sqrtScalarCompression I n, fun _ => unitModeLeakage,
    fun t => (Fintype.card n : ℝ) * t, fun _ => (Fintype.card n : ℝ), fun _ => 0,
    fun t _ => isCommutingCCRCompression_scalar _,
    fun t _ => isCCRCompletion_scalar _,
    fun t _ => by simpa using (hasDerivAt_id t).const_mul ((Fintype.card n : ℝ)),
    fun t _ => hasDerivAt_const t ((Fintype.card n : ℝ)), ?_, ?_⟩
  · intro t ht
    rw [logarithmicScaleMean, ccrMeanEnergy_sqrtScalarCompression (I := I) (n := n) ht.le]
    ring
  · intro t ht
    rw [logarithmicScaleVariance,
      ccrNumberVariance_sqrtScalarCompression (I := I) (n := n) ht.le]
    ring

/-! ## The same calibration on the full block interface -/

/-- The block tuple assembled from the `√t`-scaled scalar compression and the unit leakage. -/
def sqrtScalarBlockTuple (I : Type*) [Fintype I] [DecidableEq I] (n : Type*) [Fintype n]
    [DecidableEq n] (t : ℝ) : I → Matrix (n ⊕ (I × n)) (n ⊕ (I × n)) ℝ :=
  blockCCRTuple (sqrtScalarCompression I n t) unitModeLeakage

/-- **The full-tuple calibration is jointly realizable.**  The invariant block tuple of the
`√t`-scaled scalar compression satisfies every premise of the block-interface scale-sandwich law,
including both calibrations. -/
theorem exists_calibrated_fullCCRTuple [Nonempty I] :
    ∃ (T : ℝ → I → Matrix (n ⊕ (I × n)) (n ⊕ (I × n)) ℝ) (F F₁ F₂ : ℝ → ℝ),
      (∀ t, 0 < t → IsInvariantFullCompression (T t)) ∧
      (∀ t, 0 < t → IsCommutingCCRCompression (fullCCRCompressionBlock (T t))) ∧
      (∀ t, 0 < t → IsBlockCCRMatrixTuple (T t)) ∧
      (∀ t, 0 < t → HasDerivAt F (F₁ t) t) ∧
      (∀ t, 0 < t → HasDerivAt F₁ (F₂ t) t) ∧
      (∀ t, 0 < t →
        logarithmicScaleMean F₁ t = ccrMeanEnergy (fullCCRCompressionBlock (T t))) ∧
      (∀ t, 0 < t → logarithmicScaleVariance F₁ F₂ t =
        ccrNumberVariance (fullCCRCompressionBlock (T t)) (fullCCRLeakageBlock (T t))) := by
  refine ⟨sqrtScalarBlockTuple I n, fun t => (Fintype.card n : ℝ) * t,
    fun _ => (Fintype.card n : ℝ), fun _ => 0,
    fun t _ => blockCCRTuple_isInvariantFullCompression _ _, ?_,
    fun t _ => blockCCRTuple_isBlockCCRMatrixTuple _ _ (isCCRCompletion_scalar _),
    fun t _ => by simpa using (hasDerivAt_id t).const_mul ((Fintype.card n : ℝ)),
    fun t _ => hasDerivAt_const t ((Fintype.card n : ℝ)), ?_, ?_⟩
  · intro t _
    rw [sqrtScalarBlockTuple, blockCCRTuple_compressionBlock]
    exact isCommutingCCRCompression_scalar _
  · intro t ht
    rw [sqrtScalarBlockTuple, blockCCRTuple_compressionBlock, logarithmicScaleMean,
      ccrMeanEnergy_sqrtScalarCompression (I := I) (n := n) ht.le]
    ring
  · intro t ht
    rw [sqrtScalarBlockTuple, blockCCRTuple_compressionBlock, blockCCRTuple_leakageBlock,
      logarithmicScaleVariance,
      ccrNumberVariance_sqrtScalarCompression (I := I) (n := n) ht.le]
    ring

end

end GaloisForLFunctions.HilbertMetric
