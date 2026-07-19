import GaloisForLFunctions.RHTower.SemilocalEulerPhasePolarization
import GaloisForLFunctions.RHTower.XiPrimeSeamCofinalAnchoredEssentialNormDecay

/-!
# FE--Schwarz reflection of the finite Sonin--Euler orientation

The canonical prime-seam coefficient is odd under centered FE--Schwarz reflection, Schwarz
conjugation conjugates its value, and functional-equation reflection is negative value
conjugation.  This module lifts that exact scalar table through every finite Euler packet.

For the finite orientation Gram `G_p(rho)` and its compressed-source commutator `T_p(rho)`, Lean
proves

`G_p(conj rho) = -G_p(rho)†`,
`G_p(1-rho) = G_p(rho)†`, and
`G_p(1-conj rho) = -G_p(rho)`,

with the same identities for `T_p`.  Compactness and essential norm are therefore invariant on
the complete reflection orbit.  This is an equivariance and Prop-interface theorem: it preserves
the live Calkin obstruction and does not prove that the obstruction vanishes.
-/

open Complex

namespace RHTower

noncomputable section

open ContinuousLinearMap Metric

/-! ## Adjoint interfaces for the compact ideal and essential norm -/

/-- Compactness is invariant under Hilbert-space adjoint. -/
theorem isCompactOperator_adjoint_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    IsCompactOperator (ContinuousLinearMap.adjoint T) ↔ IsCompactOperator T := by
  constructor
  · intro h
    have h' := isCompactOperator_adjoint (ContinuousLinearMap.adjoint T) h
    simpa only [adjoint_adjoint] using h'
  · exact isCompactOperator_adjoint T

/-- Negation preserves compactness in both directions. -/
theorem isCompactOperator_neg_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) : IsCompactOperator (-T) ↔ IsCompactOperator T := by
  constructor
  · intro h
    have h' := h.neg
    have heq : -(fun x ↦ (-T) x) = (fun x ↦ T x) := by
      funext x
      simp
    rw [heq] at h'
    exact h'
  · exact fun h ↦ h.neg

/-- Taking an adjoint cannot increase distance to the compact ideal. -/
theorem essentialNorm_adjoint_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    essentialNorm (ContinuousLinearMap.adjoint T) ≤ essentialNorm T := by
  apply csInf_le_csInf
    (essentialNorm_set_bddBelow (ContinuousLinearMap.adjoint T))
    (essentialNorm_set_nonempty T)
  rintro r ⟨K, hK, rfl⟩
  refine ⟨ContinuousLinearMap.adjoint K, isCompactOperator_adjoint K hK, ?_⟩
  change ‖star T - star K‖ = ‖T - K‖
  rw [← star_sub, norm_star]

/-- The essential norm is invariant under Hilbert-space adjoint. -/
theorem essentialNorm_adjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    essentialNorm (ContinuousLinearMap.adjoint T) = essentialNorm T := by
  apply le_antisymm (essentialNorm_adjoint_le T)
  have h := essentialNorm_adjoint_le (ContinuousLinearMap.adjoint T)
  simpa only [adjoint_adjoint] using h

/-! ## Canonical finite prime-packet operators -/

/-- The finite Sonin--Euler orientation Gram with the canonical FE--Schwarz seam coefficients. -/
def orbitwiseFinitePrimeEulerOrientationGram
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (rho : ℂ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  finiteArchimedeanEulerOrientationGram a (fun i ↦ (p i : ℝ))
    (fun i ↦ orbitwiseNatPrimeSeamCharge (p i) rho)

/-- The commutator of the seam-weighted and universal finite Euler source compressions. -/
def orbitwiseFinitePrimeEulerCompressionCommutator
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (rho : ℂ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ))
      (fun i ↦ orbitwiseNatPrimeSeamCharge (p i) rho) *
    finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) (fun _ ↦ 1) -
  finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ)) (fun _ ↦ 1) *
    finiteArchimedeanEulerCompression a (fun i ↦ (p i : ℝ))
      (fun i ↦ orbitwiseNatPrimeSeamCharge (p i) rho)

/-- Centered FE--Schwarz reflection negates every finite prime-seam orientation Gram. -/
theorem orbitwiseFinitePrimeEulerOrientationGram_lineReflect
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (rho : ℂ) :
    orbitwiseFinitePrimeEulerOrientationGram a p
        (1 - (starRingEnd ℂ) rho) =
      -orbitwiseFinitePrimeEulerOrientationGram a p rho := by
  unfold orbitwiseFinitePrimeEulerOrientationGram
  rw [← finiteArchimedeanEulerOrientationGram_neg]
  congr 2
  funext i
  exact orbitwiseNatPrimeSeamCharge_lineReflect (p i) rho

/-- Schwarz reflection of the coefficient point is negative Hilbert adjoint on the finite
orientation Gram. -/
theorem adjoint_orbitwiseFinitePrimeEulerOrientationGram
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (rho : ℂ) :
    ContinuousLinearMap.adjoint
        (orbitwiseFinitePrimeEulerOrientationGram a p rho) =
      -orbitwiseFinitePrimeEulerOrientationGram a p
        ((starRingEnd ℂ) rho) := by
  unfold orbitwiseFinitePrimeEulerOrientationGram
  rw [adjoint_finiteArchimedeanEulerOrientationGram]
  congr 2
  funext i
  exact (orbitwiseNatPrimeSeamCharge_conj (p i) (hp i) rho).symm

/-- Value-reflection form of the preceding adjoint law. -/
theorem orbitwiseFinitePrimeEulerOrientationGram_conj
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (rho : ℂ) :
    orbitwiseFinitePrimeEulerOrientationGram a p ((starRingEnd ℂ) rho) =
      -ContinuousLinearMap.adjoint
        (orbitwiseFinitePrimeEulerOrientationGram a p rho) := by
  have h := congrArg Neg.neg
    (adjoint_orbitwiseFinitePrimeEulerOrientationGram a p hp rho)
  simpa only [neg_neg] using h.symm

/-- Functional-equation reflection is exactly Hilbert adjoint on the finite orientation Gram. -/
theorem orbitwiseFinitePrimeEulerOrientationGram_one_sub
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (rho : ℂ) :
    orbitwiseFinitePrimeEulerOrientationGram a p (1 - rho) =
      ContinuousLinearMap.adjoint
        (orbitwiseFinitePrimeEulerOrientationGram a p rho) := by
  rw [adjoint_orbitwiseFinitePrimeEulerOrientationGram a p hp rho]
  unfold orbitwiseFinitePrimeEulerOrientationGram
  rw [← finiteArchimedeanEulerOrientationGram_neg]
  congr 2
  funext i
  rw [orbitwiseNatPrimeSeamCharge_one_sub (p i) (hp i) rho,
    ← orbitwiseNatPrimeSeamCharge_conj (p i) (hp i) rho]

/-- The canonical finite orientation Gram is the negative compressed-source commutator. -/
theorem orbitwiseFinitePrimeEulerOrientationGram_eq_neg_compressionCommutator
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (rho : ℂ) :
    orbitwiseFinitePrimeEulerOrientationGram a p rho =
      -orbitwiseFinitePrimeEulerCompressionCommutator a p rho := by
  exact finiteArchimedeanEulerOrientationGram_eq_neg_compression_commutator
    a (fun i ↦ (p i : ℝ)) (fun i ↦ by
      change (1 : ℝ) < (p i : ℝ)
      exact_mod_cast (hp i).one_lt)
      (fun i ↦ orbitwiseNatPrimeSeamCharge (p i) rho)

/-- Equivalent orientation form of the source identity. -/
theorem orbitwiseFinitePrimeEulerCompressionCommutator_eq_neg_orientationGram
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (rho : ℂ) :
    orbitwiseFinitePrimeEulerCompressionCommutator a p rho =
      -orbitwiseFinitePrimeEulerOrientationGram a p rho := by
  have h := congrArg Neg.neg
    (orbitwiseFinitePrimeEulerOrientationGram_eq_neg_compressionCommutator
      a p hp rho)
  simpa only [neg_neg] using h.symm

/-- Centered FE--Schwarz reflection negates the actual finite compressed-source commutator. -/
theorem orbitwiseFinitePrimeEulerCompressionCommutator_lineReflect
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (rho : ℂ) :
    orbitwiseFinitePrimeEulerCompressionCommutator a p
        (1 - (starRingEnd ℂ) rho) =
      -orbitwiseFinitePrimeEulerCompressionCommutator a p rho := by
  have href := orbitwiseFinitePrimeEulerOrientationGram_lineReflect a p rho
  rw [orbitwiseFinitePrimeEulerOrientationGram_eq_neg_compressionCommutator
      a p hp, orbitwiseFinitePrimeEulerOrientationGram_eq_neg_compressionCommutator
      a p hp] at href
  simpa only [neg_neg] using neg_injective href

/-- Schwarz reflection is negative Hilbert adjoint on the compressed-source commutator. -/
theorem adjoint_orbitwiseFinitePrimeEulerCompressionCommutator
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (rho : ℂ) :
    ContinuousLinearMap.adjoint
        (orbitwiseFinitePrimeEulerCompressionCommutator a p rho) =
      -orbitwiseFinitePrimeEulerCompressionCommutator a p
        ((starRingEnd ℂ) rho) := by
  rw [orbitwiseFinitePrimeEulerCompressionCommutator_eq_neg_orientationGram
      a p hp rho,
    orbitwiseFinitePrimeEulerCompressionCommutator_eq_neg_orientationGram
      a p hp ((starRingEnd ℂ) rho)]
  change star (-orbitwiseFinitePrimeEulerOrientationGram a p rho) =
    -(-orbitwiseFinitePrimeEulerOrientationGram a p ((starRingEnd ℂ) rho))
  rw [star_neg]
  change -ContinuousLinearMap.adjoint
      (orbitwiseFinitePrimeEulerOrientationGram a p rho) =
    -(-orbitwiseFinitePrimeEulerOrientationGram a p ((starRingEnd ℂ) rho))
  rw [adjoint_orbitwiseFinitePrimeEulerOrientationGram a p
    (fun i ↦ (hp i).pos) rho]

/-- Functional-equation reflection is Hilbert adjoint on the compressed-source commutator. -/
theorem orbitwiseFinitePrimeEulerCompressionCommutator_one_sub
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (rho : ℂ) :
    orbitwiseFinitePrimeEulerCompressionCommutator a p (1 - rho) =
      ContinuousLinearMap.adjoint
        (orbitwiseFinitePrimeEulerCompressionCommutator a p rho) := by
  rw [orbitwiseFinitePrimeEulerCompressionCommutator_eq_neg_orientationGram
      a p hp (1 - rho),
    orbitwiseFinitePrimeEulerCompressionCommutator_eq_neg_orientationGram
      a p hp rho,
    orbitwiseFinitePrimeEulerOrientationGram_one_sub a p
      (fun i ↦ (hp i).pos) rho]
  change -star (orbitwiseFinitePrimeEulerOrientationGram a p rho) =
    star (-orbitwiseFinitePrimeEulerOrientationGram a p rho)
  rw [star_neg]

/-! ## Reflection-invariant Calkin interfaces -/

/-- Centered reflection preserves the finite orientation essential norm. -/
theorem essentialNorm_orbitwiseFinitePrimeEulerOrientationGram_lineReflect
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (rho : ℂ) :
    essentialNorm (orbitwiseFinitePrimeEulerOrientationGram a p
        (1 - (starRingEnd ℂ) rho)) =
      essentialNorm (orbitwiseFinitePrimeEulerOrientationGram a p rho) := by
  rw [orbitwiseFinitePrimeEulerOrientationGram_lineReflect, essentialNorm_neg]

/-- Schwarz reflection preserves the finite orientation essential norm. -/
theorem essentialNorm_orbitwiseFinitePrimeEulerOrientationGram_conj
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (rho : ℂ) :
    essentialNorm (orbitwiseFinitePrimeEulerOrientationGram a p
        ((starRingEnd ℂ) rho)) =
      essentialNorm (orbitwiseFinitePrimeEulerOrientationGram a p rho) := by
  rw [orbitwiseFinitePrimeEulerOrientationGram_conj a p hp rho,
    essentialNorm_neg, essentialNorm_adjoint]

/-- Functional-equation reflection preserves the finite orientation essential norm. -/
theorem essentialNorm_orbitwiseFinitePrimeEulerOrientationGram_one_sub
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (rho : ℂ) :
    essentialNorm (orbitwiseFinitePrimeEulerOrientationGram a p (1 - rho)) =
      essentialNorm (orbitwiseFinitePrimeEulerOrientationGram a p rho) := by
  rw [orbitwiseFinitePrimeEulerOrientationGram_one_sub a p hp rho,
    essentialNorm_adjoint]

/-- Centered reflection preserves compactness of the finite orientation Gram. -/
theorem orbitwiseFinitePrimeEulerOrientationGram_lineReflect_isCompactOperator_iff
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (rho : ℂ) :
    IsCompactOperator (orbitwiseFinitePrimeEulerOrientationGram a p
        (1 - (starRingEnd ℂ) rho)) ↔
      IsCompactOperator (orbitwiseFinitePrimeEulerOrientationGram a p rho) := by
  rw [orbitwiseFinitePrimeEulerOrientationGram_lineReflect,
    isCompactOperator_neg_iff]

/-- Schwarz reflection preserves compactness of the finite orientation Gram. -/
theorem orbitwiseFinitePrimeEulerOrientationGram_conj_isCompactOperator_iff
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (rho : ℂ) :
    IsCompactOperator (orbitwiseFinitePrimeEulerOrientationGram a p
        ((starRingEnd ℂ) rho)) ↔
      IsCompactOperator (orbitwiseFinitePrimeEulerOrientationGram a p rho) := by
  rw [orbitwiseFinitePrimeEulerOrientationGram_conj a p hp rho,
    isCompactOperator_neg_iff, isCompactOperator_adjoint_iff]

/-- Functional-equation reflection preserves compactness of the finite orientation Gram. -/
theorem orbitwiseFinitePrimeEulerOrientationGram_one_sub_isCompactOperator_iff
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, 0 < p i) (rho : ℂ) :
    IsCompactOperator (orbitwiseFinitePrimeEulerOrientationGram a p (1 - rho)) ↔
      IsCompactOperator (orbitwiseFinitePrimeEulerOrientationGram a p rho) := by
  rw [orbitwiseFinitePrimeEulerOrientationGram_one_sub a p hp rho,
    isCompactOperator_adjoint_iff]

/-- Centered reflection preserves the compressed-source commutator essential norm. -/
theorem essentialNorm_orbitwiseFinitePrimeEulerCompressionCommutator_lineReflect
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (rho : ℂ) :
    essentialNorm (orbitwiseFinitePrimeEulerCompressionCommutator a p
        (1 - (starRingEnd ℂ) rho)) =
      essentialNorm (orbitwiseFinitePrimeEulerCompressionCommutator a p rho) := by
  rw [orbitwiseFinitePrimeEulerCompressionCommutator_lineReflect a p hp rho,
    essentialNorm_neg]

/-- Functional-equation reflection preserves the compressed-source commutator essential norm. -/
theorem essentialNorm_orbitwiseFinitePrimeEulerCompressionCommutator_one_sub
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (rho : ℂ) :
    essentialNorm (orbitwiseFinitePrimeEulerCompressionCommutator a p (1 - rho)) =
      essentialNorm (orbitwiseFinitePrimeEulerCompressionCommutator a p rho) := by
  rw [orbitwiseFinitePrimeEulerCompressionCommutator_one_sub a p hp rho,
    essentialNorm_adjoint]

end

end RHTower
