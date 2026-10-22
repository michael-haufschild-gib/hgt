import GaloisForLFunctions.RHTower.Suzuki.SuzukiOnePrimeTerminalPrunedPropagator
import GaloisForLFunctions.HTGeometry.HighFrequencyTransportBound
import GaloisForLFunctions.HTGeometry.CompoundOperatorOrder

/-!
# Similarity transport for the literal one-prime terminal block

The terminal weighted adjacency is nonnormal in the standard two-coordinate norm, but it is
exactly similar to the Hermitian swap matrix.  Conjugating the complete Gamma frequency
propagator through that similarity transfers the existing self-adjoint high-frequency theorem to
the literal Suzuki block.  The resulting denominator is the spectral one, `L - 1/2`, and
nonnormality costs only the fixed condition number of the diagonal similarity.

The final theorems commute the conjugated matrix integral with evaluation on a literal
two-coordinate Euclidean state.  Thus the result is not only an operator estimate: it is the
vector-valued Bochner estimate needed by the one-prime Gamma channel on both frequency rays.
-/

open scoped Matrix Matrix.Norms.L2Operator
open Complex MeasureTheory intervalIntegral Set

namespace RHTower

noncomputable section

/-- Diagonal similarity which removes the fractional carrier weight from the terminal block. -/
def onePrimeTerminalSimilarity : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(onePrimeTerminalRatio : ℂ), 0; 0, 1]

/-- Explicit inverse of the terminal diagonal similarity. -/
def onePrimeTerminalSimilarityInv : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((onePrimeTerminalRatio : ℂ)⁻¹), 0; 0, 1]

/-- Hermitian swap matrix similar to the literal weighted terminal adjacency. -/
def onePrimeTerminalSymmetricAdjacency : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 1, 0]

theorem onePrimeTerminalSimilarity_mul_inv :
    onePrimeTerminalSimilarity * onePrimeTerminalSimilarityInv = 1 := by
  have hr : (onePrimeTerminalRatio : ℂ) ≠ 0 := by
    exact_mod_cast onePrimeTerminalRatio_pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [onePrimeTerminalSimilarity, onePrimeTerminalSimilarityInv,
      Matrix.mul_apply, Fin.sum_univ_two, hr]

theorem onePrimeTerminalSimilarityInv_mul :
    onePrimeTerminalSimilarityInv * onePrimeTerminalSimilarity = 1 := by
  have hr : (onePrimeTerminalRatio : ℂ) ≠ 0 := by
    exact_mod_cast onePrimeTerminalRatio_pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [onePrimeTerminalSimilarity, onePrimeTerminalSimilarityInv,
      Matrix.mul_apply, Fin.sum_univ_two, hr]

/-- The diagonal terminal similarity bundled as a unit of the matrix algebra. -/
def onePrimeTerminalSimilarityUnit : (Matrix (Fin 2) (Fin 2) ℂ)ˣ where
  val := onePrimeTerminalSimilarity
  inv := onePrimeTerminalSimilarityInv
  val_inv := onePrimeTerminalSimilarity_mul_inv
  inv_val := onePrimeTerminalSimilarityInv_mul

@[simp] theorem coe_onePrimeTerminalSimilarityUnit :
    (onePrimeTerminalSimilarityUnit : Matrix (Fin 2) (Fin 2) ℂ) =
      onePrimeTerminalSimilarity := rfl

@[simp] theorem coe_onePrimeTerminalSimilarityUnit_inv :
    ((onePrimeTerminalSimilarityUnit⁻¹ : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) :
      Matrix (Fin 2) (Fin 2) ℂ) = onePrimeTerminalSimilarityInv := rfl

/-- Exact similarity between the literal nonnormal adjacency and the Hermitian swap. -/
theorem onePrimeTerminalAdjacency_eq_similarity :
    onePrimeTerminalAdjacency = onePrimeTerminalSimilarity *
      onePrimeTerminalSymmetricAdjacency * onePrimeTerminalSimilarityInv := by
  have hr : (onePrimeTerminalRatio : ℂ) ≠ 0 := by
    exact_mod_cast onePrimeTerminalRatio_pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [onePrimeTerminalAdjacency, onePrimeTerminalSimilarity,
      onePrimeTerminalSimilarityInv, onePrimeTerminalSymmetricAdjacency,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem onePrimeTerminalSymmetricAdjacency_isHermitian :
    onePrimeTerminalSymmetricAdjacency.IsHermitian := by
  change star onePrimeTerminalSymmetricAdjacency = onePrimeTerminalSymmetricAdjacency
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [onePrimeTerminalSymmetricAdjacency, Matrix.star_apply]

/-- The full operator phase, not merely its generator, is transported by the exact similarity. -/
theorem opPhase_onePrimeTerminalAdjacency_eq_similarity (eta : ℝ) :
    GaloisForLFunctions.HTGeometry.opPhase onePrimeTerminalAdjacency eta =
      onePrimeTerminalSimilarity *
        GaloisForLFunctions.HTGeometry.opPhase onePrimeTerminalSymmetricAdjacency eta *
          onePrimeTerminalSimilarityInv := by
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
    .restrictScalars ℚ ℂ _
  rw [GaloisForLFunctions.HTGeometry.opPhase,
    GaloisForLFunctions.HTGeometry.opPhase]
  rw [onePrimeTerminalAdjacency_eq_similarity]
  have harg :
      eta • ((-I / 2 : ℂ) •
          (onePrimeTerminalSimilarity * onePrimeTerminalSymmetricAdjacency *
            onePrimeTerminalSimilarityInv)) =
        onePrimeTerminalSimilarity *
          (eta • ((-I / 2 : ℂ) • onePrimeTerminalSymmetricAdjacency)) *
            onePrimeTerminalSimilarityInv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [onePrimeTerminalSimilarity, onePrimeTerminalSimilarityInv,
        onePrimeTerminalSymmetricAdjacency, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [harg]
  exact NormedSpace.exp_units_conj onePrimeTerminalSimilarityUnit
    (eta • ((-I / 2 : ℂ) • onePrimeTerminalSymmetricAdjacency))

/-- Exact conjugacy of the complete Gamma frequency propagator. -/
theorem freqPropagator_onePrimeTerminalAdjacency_eq_similarity
    (L : ℝ) (Rint : ℝ → ℝ) (eta : ℝ) :
    GaloisForLFunctions.HTGeometry.freqPropagator L Rint onePrimeTerminalAdjacency eta =
      onePrimeTerminalSimilarity *
        GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalSymmetricAdjacency eta * onePrimeTerminalSimilarityInv := by
  rw [GaloisForLFunctions.HTGeometry.freqPropagator,
    GaloisForLFunctions.HTGeometry.freqPropagator,
    opPhase_onePrimeTerminalAdjacency_eq_similarity]
  rw [← smul_mul_assoc, ← mul_smul_comm]

theorem onePrimeTerminalSymmetricAdjacency_mul_self :
    onePrimeTerminalSymmetricAdjacency * onePrimeTerminalSymmetricAdjacency = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [onePrimeTerminalSymmetricAdjacency, Matrix.mul_apply, Fin.sum_univ_two]

theorem onePrimeTerminalSymmetricAdjacency_mem_unitary :
    onePrimeTerminalSymmetricAdjacency ∈
      unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Unitary.mem_iff]
  have hs : star onePrimeTerminalSymmetricAdjacency =
      onePrimeTerminalSymmetricAdjacency :=
    onePrimeTerminalSymmetricAdjacency_isHermitian
  rw [hs, onePrimeTerminalSymmetricAdjacency_mul_self]
  exact ⟨rfl, rfl⟩

/-- The Hermitian terminal generator has exact operator norm one. -/
@[simp] theorem norm_onePrimeTerminalSymmetricAdjacency :
    ‖onePrimeTerminalSymmetricAdjacency‖ = 1 :=
  CStarRing.norm_of_mem_unitary onePrimeTerminalSymmetricAdjacency_mem_unitary

/-- Bochner integration commutes with the fixed terminal similarity. -/
theorem intervalIntegral_onePrimeTerminal_freqPropagator_eq_similarity
    {f : ℝ → ℝ} {L epsilon R : ℝ} {Rint : ℝ → ℝ}
    (hint : IntervalIntegrable
      (fun eta => f eta • GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalSymmetricAdjacency eta) volume epsilon R) :
    (∫ eta in epsilon..R, f eta •
        GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalAdjacency eta) =
      onePrimeTerminalSimilarity *
        (∫ eta in epsilon..R, f eta •
          GaloisForLFunctions.HTGeometry.freqPropagator L Rint
            onePrimeTerminalSymmetricAdjacency eta) *
        onePrimeTerminalSimilarityInv := by
  let C : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
    ContinuousLinearMap.mulLeftRight ℂ _ onePrimeTerminalSimilarity
      onePrimeTerminalSimilarityInv
  change (∫ eta in epsilon..R, f eta •
      GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalAdjacency eta) = C
    (∫ eta in epsilon..R, f eta •
      GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalSymmetricAdjacency eta)
  have hcomm := C.intervalIntegral_comp_comm hint
  rw [← hcomm]
  apply intervalIntegral.integral_congr
  intro eta _
  change f eta • GaloisForLFunctions.HTGeometry.freqPropagator L Rint
      onePrimeTerminalAdjacency eta = C
    (f eta • GaloisForLFunctions.HTGeometry.freqPropagator L Rint
      onePrimeTerminalSymmetricAdjacency eta)
  rw [freqPropagator_onePrimeTerminalAdjacency_eq_similarity]
  change f eta • (onePrimeTerminalSimilarity *
      GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalSymmetricAdjacency eta * onePrimeTerminalSimilarityInv) =
    onePrimeTerminalSimilarity *
      (f eta • GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalSymmetricAdjacency eta) * onePrimeTerminalSimilarityInv
  rw [← smul_mul_assoc, ← mul_smul_comm]

/-- High-frequency transport for the literal nonnormal terminal generator.  Similarity improves
the direct Neumann denominator to the exact spectral threshold `L - 1/2`. -/
theorem norm_integral_onePrimeTerminal_freqPropagator_le
    {r r' Rint f f' : ℝ → ℝ} {L epsilon R M : ℝ}
    (hL : 1 / 2 < L) (hepsilonR : epsilon ≤ R)
    (hr : ∀ x ∈ uIcc epsilon R, HasDerivAt r (r' x) x)
    (hrnn : ∀ x ∈ uIcc epsilon R, 0 ≤ r x)
    (hr'mono : (∀ x ∈ uIcc epsilon R, 0 ≤ r' x) ∨
      (∀ x ∈ uIcc epsilon R, r' x ≤ 0))
    (hr'c : ContinuousOn r' (uIcc epsilon R))
    (hRint : ∀ x ∈ uIcc epsilon R, HasDerivAt Rint (r x) x)
    (hf : ∀ x ∈ uIcc epsilon R, HasDerivAt f (f' x) x)
    (hf'c : ContinuousOn f' (uIcc epsilon R))
    (hfb : ∀ x ∈ uIcc epsilon R, |f x| ≤ M) :
    ‖∫ eta in epsilon..R, f eta •
        GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalAdjacency eta‖ ≤
      (‖onePrimeTerminalSimilarity‖ * ‖onePrimeTerminalSimilarityInv‖) *
        ((|f epsilon| + |f R| + (∫ eta in epsilon..R, |f' eta|) + M) *
          (L - 1 / 2)⁻¹) := by
  have hT : IsSelfAdjoint onePrimeTerminalSymmetricAdjacency :=
    onePrimeTerminalSymmetricAdjacency_isHermitian
  have hTL : ‖onePrimeTerminalSymmetricAdjacency‖ / 2 < L := by
    rw [norm_onePrimeTerminalSymmetricAdjacency]
    norm_num at hL ⊢
    exact hL
  have hbase := GaloisForLFunctions.HTGeometry.norm_integral_freqPropagator_le
    (T := onePrimeTerminalSymmetricAdjacency) hT hTL hepsilonR hr hrnn hr'mono hr'c
      hRint hf hf'c hfb
  have hWc : ContinuousOn
      (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalSymmetricAdjacency) (uIcc epsilon R) := by
    intro x hx
    exact (GaloisForLFunctions.HTGeometry.hasDerivAt_freqPropagator
      (L := L) (Rint := Rint) (r := r) onePrimeTerminalSymmetricAdjacency
      (hRint x hx)).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (uIcc epsilon R) := by
    intro x hx
    exact (hf x hx).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun eta => f eta • GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalSymmetricAdjacency eta) volume epsilon R :=
    (hfc.smul hWc).intervalIntegrable
  rw [intervalIntegral_onePrimeTerminal_freqPropagator_eq_similarity hint]
  calc
    ‖onePrimeTerminalSimilarity *
        (∫ eta in epsilon..R, f eta •
          GaloisForLFunctions.HTGeometry.freqPropagator L Rint
            onePrimeTerminalSymmetricAdjacency eta) * onePrimeTerminalSimilarityInv‖
        ≤ ‖onePrimeTerminalSimilarity‖ *
            ‖∫ eta in epsilon..R, f eta •
              GaloisForLFunctions.HTGeometry.freqPropagator L Rint
                onePrimeTerminalSymmetricAdjacency eta‖ *
            ‖onePrimeTerminalSimilarityInv‖ := by
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖onePrimeTerminalSimilarity‖ *
          ((|f epsilon| + |f R| + (∫ eta in epsilon..R, |f' eta|) + M) *
            (L - ‖onePrimeTerminalSymmetricAdjacency‖ / 2)⁻¹) *
          ‖onePrimeTerminalSimilarityInv‖ := by
        gcongr
    _ = (‖onePrimeTerminalSimilarity‖ * ‖onePrimeTerminalSimilarityInv‖) *
          ((|f epsilon| + |f R| + (∫ eta in epsilon..R, |f' eta|) + M) *
            (L - 1 / 2)⁻¹) := by
        rw [norm_onePrimeTerminalSymmetricAdjacency]
        ring

/-- Condition-number estimate for conjugation by the terminal similarity. -/
theorem norm_onePrimeTerminal_similarity_conjugate_le
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖onePrimeTerminalSimilarity * A * onePrimeTerminalSimilarityInv‖ ≤
      (‖onePrimeTerminalSimilarity‖ * ‖onePrimeTerminalSimilarityInv‖) * ‖A‖ := by
  calc
    ‖onePrimeTerminalSimilarity * A * onePrimeTerminalSimilarityInv‖
        ≤ ‖onePrimeTerminalSimilarity‖ * ‖A‖ * ‖onePrimeTerminalSimilarityInv‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = (‖onePrimeTerminalSimilarity‖ * ‖onePrimeTerminalSimilarityInv‖) * ‖A‖ := by
      ring

/-- Positive-ray half-power estimate for the literal terminal operator. -/
theorem norm_integral_halfPower_onePrimeTerminal_freqPropagator_le
    {r r' Rint : ℝ → ℝ} {L epsilon R : ℝ}
    (hL : 1 / 2 < L) (hepsilon : 0 < epsilon) (hepsilonR : epsilon ≤ R)
    (hr : ∀ x ∈ uIcc epsilon R, HasDerivAt r (r' x) x)
    (hrnn : ∀ x ∈ uIcc epsilon R, 0 ≤ r x)
    (hr'nn : ∀ x ∈ uIcc epsilon R, 0 ≤ r' x)
    (hr'c : ContinuousOn r' (uIcc epsilon R))
    (hRint : ∀ x ∈ uIcc epsilon R, HasDerivAt Rint (r x) x) :
    ‖∫ eta in epsilon..R, (eta ^ (-(1 : ℝ) / 2)) •
        GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalAdjacency eta‖ ≤
      (‖onePrimeTerminalSimilarity‖ * ‖onePrimeTerminalSimilarityInv‖) *
        ((3 * epsilon ^ (-(1 : ℝ) / 2) + R ^ (-(1 : ℝ) / 2)) *
          (L - 1 / 2)⁻¹) := by
  have hT : IsSelfAdjoint onePrimeTerminalSymmetricAdjacency :=
    onePrimeTerminalSymmetricAdjacency_isHermitian
  have hTL : ‖onePrimeTerminalSymmetricAdjacency‖ / 2 < L := by
    rw [norm_onePrimeTerminalSymmetricAdjacency]
    norm_num at hL ⊢
    exact hL
  have hbase := GaloisForLFunctions.HTGeometry.norm_integral_halfPower_freqPropagator_le
    (T := onePrimeTerminalSymmetricAdjacency) hT hTL hepsilon hepsilonR hr hrnn hr'nn
      hr'c hRint
  have hIcc : uIcc epsilon R = Icc epsilon R := uIcc_of_le hepsilonR
  have hpos : ∀ x ∈ uIcc epsilon R, 0 < x := by
    intro x hx
    rw [hIcc] at hx
    exact lt_of_lt_of_le hepsilon hx.1
  have ha : ContinuousOn (fun x : ℝ => x ^ (-(1 : ℝ) / 2))
      (uIcc epsilon R) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x (-(1 : ℝ) / 2)
      (Or.inl (ne_of_gt (hpos x hx)))).continuousWithinAt
  have hW : ContinuousOn
      (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalSymmetricAdjacency) (uIcc epsilon R) := by
    intro x hx
    exact (GaloisForLFunctions.HTGeometry.hasDerivAt_freqPropagator
      (L := L) (Rint := Rint) (r := r) onePrimeTerminalSymmetricAdjacency
      (hRint x hx)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun eta => (eta ^ (-(1 : ℝ) / 2)) •
        GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalSymmetricAdjacency eta) volume epsilon R :=
    (ha.smul hW).intervalIntegrable
  rw [intervalIntegral_onePrimeTerminal_freqPropagator_eq_similarity hint]
  refine (norm_onePrimeTerminal_similarity_conjugate_le _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [norm_onePrimeTerminalSymmetricAdjacency] at hbase
  simpa using hbase

/-- Reflected half-power estimate for the literal terminal operator. -/
theorem norm_integral_halfPower_onePrimeTerminal_freqPropagator_neg_le
    {r r' Rint : ℝ → ℝ} {L epsilon R : ℝ}
    (hL : 1 / 2 < L) (hepsilon : 0 < epsilon) (hepsilonR : epsilon ≤ R)
    (hr : ∀ x ∈ uIcc (-R) (-epsilon), HasDerivAt r (r' x) x)
    (hrnn : ∀ x ∈ uIcc (-R) (-epsilon), 0 ≤ r x)
    (hr'mono : (∀ x ∈ uIcc (-R) (-epsilon), 0 ≤ r' x) ∨
      (∀ x ∈ uIcc (-R) (-epsilon), r' x ≤ 0))
    (hr'c : ContinuousOn r' (uIcc (-R) (-epsilon)))
    (hRint : ∀ x ∈ uIcc (-R) (-epsilon), HasDerivAt Rint (r x) x) :
    ‖∫ eta in (-R)..(-epsilon), ((-eta) ^ (-(1 : ℝ) / 2)) •
        GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalAdjacency eta‖ ≤
      (‖onePrimeTerminalSimilarity‖ * ‖onePrimeTerminalSimilarityInv‖) *
        ((3 * epsilon ^ (-(1 : ℝ) / 2) + R ^ (-(1 : ℝ) / 2)) *
          (L - 1 / 2)⁻¹) := by
  have hT : IsSelfAdjoint onePrimeTerminalSymmetricAdjacency :=
    onePrimeTerminalSymmetricAdjacency_isHermitian
  have hTL : ‖onePrimeTerminalSymmetricAdjacency‖ / 2 < L := by
    rw [norm_onePrimeTerminalSymmetricAdjacency]
    norm_num at hL ⊢
    exact hL
  have hbase := GaloisForLFunctions.HTGeometry.norm_integral_halfPower_freqPropagator_neg_le
    (T := onePrimeTerminalSymmetricAdjacency) hT hTL hepsilon hepsilonR hr hrnn
      hr'mono hr'c hRint
  have hIcc : uIcc (-R) (-epsilon) = Icc (-R) (-epsilon) :=
    uIcc_of_le (by linarith)
  have hneg : ∀ x ∈ uIcc (-R) (-epsilon), 0 < -x := by
    intro x hx
    rw [hIcc] at hx
    linarith [hx.2]
  have ha : ContinuousOn (fun x : ℝ => (-x) ^ (-(1 : ℝ) / 2))
      (uIcc (-R) (-epsilon)) := by
    intro x hx
    exact ((Real.continuousAt_rpow_const (-x) (-(1 : ℝ) / 2)
      (Or.inl (ne_of_gt (hneg x hx)))).comp continuousAt_neg).continuousWithinAt
  have hW : ContinuousOn
      (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalSymmetricAdjacency) (uIcc (-R) (-epsilon)) := by
    intro x hx
    exact (GaloisForLFunctions.HTGeometry.hasDerivAt_freqPropagator
      (L := L) (Rint := Rint) (r := r) onePrimeTerminalSymmetricAdjacency
      (hRint x hx)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun eta => ((-eta) ^ (-(1 : ℝ) / 2)) •
        GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalSymmetricAdjacency eta) volume (-R) (-epsilon) :=
    (ha.smul hW).intervalIntegrable
  rw [intervalIntegral_onePrimeTerminal_freqPropagator_eq_similarity hint]
  refine (norm_onePrimeTerminal_similarity_conjugate_le _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [norm_onePrimeTerminalSymmetricAdjacency] at hbase
  simpa using hbase

/-- A matrix-valued terminal transport estimate acts on a literal two-coordinate state with no
extra loss beyond the state norm. -/
theorem norm_intervalIntegral_onePrimeTerminal_freqPropagator_apply_le
    {f : ℝ → ℝ} {L epsilon R C : ℝ} {Rint : ℝ → ℝ}
    (hint : IntervalIntegrable
      (fun eta => f eta • GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalAdjacency eta) volume epsilon R)
    (hbound : ‖∫ eta in epsilon..R, f eta •
        GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalAdjacency eta‖ ≤ C)
    (v : EuclideanSpace ℂ (Fin 2)) :
    ‖∫ eta in epsilon..R, f eta •
        (Matrix.toEuclideanCLM (𝕜 := ℂ)
          (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
            onePrimeTerminalAdjacency eta) v)‖ ≤ C * ‖v‖ := by
  let PhiLin : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
    (LinearMap.applyₗ (R := ℂ) v).comp
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin 2) (n := Fin 2)).toLinearMap
  let Phi : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    LinearMap.toContinuousLinearMap PhiLin
  have hPhi (A : Matrix (Fin 2) (Fin 2) ℂ) :
      Phi A = Matrix.toEuclideanCLM (𝕜 := ℂ) A v := by
    rfl
  have hcomm := Phi.intervalIntegral_comp_comm hint
  have hrewrite :
      (∫ eta in epsilon..R, f eta •
        (Matrix.toEuclideanCLM (𝕜 := ℂ)
          (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
            onePrimeTerminalAdjacency eta) v)) =
        Phi (∫ eta in epsilon..R, f eta •
          GaloisForLFunctions.HTGeometry.freqPropagator L Rint
            onePrimeTerminalAdjacency eta) := by
    rw [← hcomm]
    apply intervalIntegral.integral_congr
    intro eta _
    change f eta • Matrix.toEuclideanCLM (𝕜 := ℂ)
        (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalAdjacency eta) v = Phi
      (f eta • GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalAdjacency eta)
    rw [hPhi]
    have hv : (((f eta : ℝ) : ℂ)) •
        Matrix.toEuclideanCLM (𝕜 := ℂ)
          (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
            onePrimeTerminalAdjacency eta) v =
        f eta • Matrix.toEuclideanCLM (𝕜 := ℂ)
          (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
            onePrimeTerminalAdjacency eta) v := by
      rw [← Complex.coe_algebraMap, algebraMap_smul]
    have hm : (((f eta : ℝ) : ℂ)) •
        GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalAdjacency eta =
        f eta • GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalAdjacency eta := by
      rw [← Complex.coe_algebraMap, algebraMap_smul]
    rw [← hv, ← hm, map_smul]
    rfl
  rw [hrewrite]
  rw [hPhi]
  calc
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (∫ eta in epsilon..R, f eta •
          GaloisForLFunctions.HTGeometry.freqPropagator L Rint
            onePrimeTerminalAdjacency eta) v‖
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
            (∫ eta in epsilon..R, f eta •
              GaloisForLFunctions.HTGeometry.freqPropagator L Rint
                onePrimeTerminalAdjacency eta)‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ v
    _ = ‖∫ eta in epsilon..R, f eta •
          GaloisForLFunctions.HTGeometry.freqPropagator L Rint
            onePrimeTerminalAdjacency eta‖ * ‖v‖ := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
    _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

/-- Positive-ray half-power estimate on a literal terminal state. -/
theorem norm_integral_halfPower_onePrimeTerminal_freqPropagator_apply_le
    {r r' Rint : ℝ → ℝ} {L epsilon R : ℝ}
    (v : EuclideanSpace ℂ (Fin 2))
    (hL : 1 / 2 < L) (hepsilon : 0 < epsilon) (hepsilonR : epsilon ≤ R)
    (hr : ∀ x ∈ uIcc epsilon R, HasDerivAt r (r' x) x)
    (hrnn : ∀ x ∈ uIcc epsilon R, 0 ≤ r x)
    (hr'nn : ∀ x ∈ uIcc epsilon R, 0 ≤ r' x)
    (hr'c : ContinuousOn r' (uIcc epsilon R))
    (hRint : ∀ x ∈ uIcc epsilon R, HasDerivAt Rint (r x) x) :
    ‖∫ eta in epsilon..R, (eta ^ (-(1 : ℝ) / 2)) •
        (Matrix.toEuclideanCLM (𝕜 := ℂ)
          (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
            onePrimeTerminalAdjacency eta) v)‖ ≤
      ((‖onePrimeTerminalSimilarity‖ * ‖onePrimeTerminalSimilarityInv‖) *
        ((3 * epsilon ^ (-(1 : ℝ) / 2) + R ^ (-(1 : ℝ) / 2)) *
          (L - 1 / 2)⁻¹)) * ‖v‖ := by
  have hmatrix := norm_integral_halfPower_onePrimeTerminal_freqPropagator_le
    hL hepsilon hepsilonR hr hrnn hr'nn hr'c hRint
  have hIcc : uIcc epsilon R = Icc epsilon R := uIcc_of_le hepsilonR
  have hpos : ∀ x ∈ uIcc epsilon R, 0 < x := by
    intro x hx
    rw [hIcc] at hx
    exact lt_of_lt_of_le hepsilon hx.1
  have ha : ContinuousOn (fun x : ℝ => x ^ (-(1 : ℝ) / 2))
      (uIcc epsilon R) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x (-(1 : ℝ) / 2)
      (Or.inl (ne_of_gt (hpos x hx)))).continuousWithinAt
  have hW : ContinuousOn
      (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalAdjacency) (uIcc epsilon R) := by
    intro x hx
    exact (GaloisForLFunctions.HTGeometry.hasDerivAt_freqPropagator
      (L := L) (Rint := Rint) (r := r) onePrimeTerminalAdjacency
      (hRint x hx)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun eta => (eta ^ (-(1 : ℝ) / 2)) •
        GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalAdjacency eta) volume epsilon R :=
    (ha.smul hW).intervalIntegrable
  exact norm_intervalIntegral_onePrimeTerminal_freqPropagator_apply_le hint hmatrix v

/-- Negative-ray half-power estimate on a literal terminal state. -/
theorem norm_integral_halfPower_onePrimeTerminal_freqPropagator_neg_apply_le
    {r r' Rint : ℝ → ℝ} {L epsilon R : ℝ}
    (v : EuclideanSpace ℂ (Fin 2))
    (hL : 1 / 2 < L) (hepsilon : 0 < epsilon) (hepsilonR : epsilon ≤ R)
    (hr : ∀ x ∈ uIcc (-R) (-epsilon), HasDerivAt r (r' x) x)
    (hrnn : ∀ x ∈ uIcc (-R) (-epsilon), 0 ≤ r x)
    (hr'mono : (∀ x ∈ uIcc (-R) (-epsilon), 0 ≤ r' x) ∨
      (∀ x ∈ uIcc (-R) (-epsilon), r' x ≤ 0))
    (hr'c : ContinuousOn r' (uIcc (-R) (-epsilon)))
    (hRint : ∀ x ∈ uIcc (-R) (-epsilon), HasDerivAt Rint (r x) x) :
    ‖∫ eta in (-R)..(-epsilon), ((-eta) ^ (-(1 : ℝ) / 2)) •
        (Matrix.toEuclideanCLM (𝕜 := ℂ)
          (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
            onePrimeTerminalAdjacency eta) v)‖ ≤
      ((‖onePrimeTerminalSimilarity‖ * ‖onePrimeTerminalSimilarityInv‖) *
        ((3 * epsilon ^ (-(1 : ℝ) / 2) + R ^ (-(1 : ℝ) / 2)) *
          (L - 1 / 2)⁻¹)) * ‖v‖ := by
  have hmatrix := norm_integral_halfPower_onePrimeTerminal_freqPropagator_neg_le
    hL hepsilon hepsilonR hr hrnn hr'mono hr'c hRint
  have hIcc : uIcc (-R) (-epsilon) = Icc (-R) (-epsilon) :=
    uIcc_of_le (by linarith)
  have hneg : ∀ x ∈ uIcc (-R) (-epsilon), 0 < -x := by
    intro x hx
    rw [hIcc] at hx
    linarith [hx.2]
  have ha : ContinuousOn (fun x : ℝ => (-x) ^ (-(1 : ℝ) / 2))
      (uIcc (-R) (-epsilon)) := by
    intro x hx
    exact ((Real.continuousAt_rpow_const (-x) (-(1 : ℝ) / 2)
      (Or.inl (ne_of_gt (hneg x hx)))).comp continuousAt_neg).continuousWithinAt
  have hW : ContinuousOn
      (GaloisForLFunctions.HTGeometry.freqPropagator L Rint
        onePrimeTerminalAdjacency) (uIcc (-R) (-epsilon)) := by
    intro x hx
    exact (GaloisForLFunctions.HTGeometry.hasDerivAt_freqPropagator
      (L := L) (Rint := Rint) (r := r) onePrimeTerminalAdjacency
      (hRint x hx)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun eta => ((-eta) ^ (-(1 : ℝ) / 2)) •
        GaloisForLFunctions.HTGeometry.freqPropagator L Rint
          onePrimeTerminalAdjacency eta) volume (-R) (-epsilon) :=
    (ha.smul hW).intervalIntegrable
  exact norm_intervalIntegral_onePrimeTerminal_freqPropagator_apply_le hint hmatrix v

end

end RHTower
