import GaloisForLFunctions.RHTower.SourceHorizontalSharedReservoirAmplification
import Mathlib.Algebra.Order.Chebyshev

/-!
# Formation-complete positivity and reflected Gram fracture

Weighted codiagonal recovery, the shared-reservoir interaction, and functional-equation
reflection form one exact Gram law.  The two reflected completions jointly reconstruct diagonal
energy and reservoir interaction.  Their positive orientation has universal positivity exactly
through formation depth two; depth three detects every nonzero horizontal Xi grade.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

def formationDiagonalEnergy {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  ∑ i, (Real.sqrt (w i) * x i) ^ 2

def formationCodiagonalResponse {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  ∑ i, Real.sqrt (w i) * x i

def formationReflectedGramPlus {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  formationDiagonalEnergy w x + reservoirWeightedForm w x

def formationReflectedGramMinus {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  formationDiagonalEnergy w x - reservoirWeightedForm w x

theorem reservoirWeightedForm_eq_formationGramDefect
    {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) :
    reservoirWeightedForm w x =
      formationDiagonalEnergy w x - formationCodiagonalResponse w x ^ 2 := by
  rw [reservoirWeightedForm, QuadraticMap.comp_apply, reservoirBaseForm_apply]
  rfl

theorem formationReflectedGramMinus_eq_sq
    {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) :
    formationReflectedGramMinus w x = formationCodiagonalResponse w x ^ 2 := by
  rw [formationReflectedGramMinus, reservoirWeightedForm_eq_formationGramDefect]
  ring

theorem formationReflectedGramMinus_nonneg
    {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) :
    0 ≤ formationReflectedGramMinus w x := by
  rw [formationReflectedGramMinus_eq_sq]
  positivity

theorem formationReflectedGramPlus_eq
    {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) :
    formationReflectedGramPlus w x =
      2 * formationDiagonalEnergy w x - formationCodiagonalResponse w x ^ 2 := by
  rw [formationReflectedGramPlus, reservoirWeightedForm_eq_formationGramDefect]
  ring

/-- Adding reflected completions conserves exactly twice diagonal packet energy. -/
theorem formationReflectedGramPlus_add_minus
    {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) :
    formationReflectedGramPlus w x + formationReflectedGramMinus w x =
      2 * formationDiagonalEnergy w x := by
  rw [formationReflectedGramPlus, formationReflectedGramMinus]
  ring

/-- Subtracting reflected completions reconstructs exactly twice reservoir interaction. -/
theorem formationReflectedGramPlus_sub_minus
    {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) :
    formationReflectedGramPlus w x - formationReflectedGramMinus w x =
      2 * reservoirWeightedForm w x := by
  rw [formationReflectedGramPlus, formationReflectedGramMinus]
  ring

theorem formationCodiagonalResponse_sq_le_card_mul_diagonalEnergy
    {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) :
    formationCodiagonalResponse w x ^ 2 ≤
      (m : ℝ) * formationDiagonalEnergy w x := by
  simpa [formationCodiagonalResponse, formationDiagonalEnergy] using
    (sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun i : Fin m => Real.sqrt (w i) * x i))

theorem formationReflectedGramPlus_nonneg_of_card_le_two
    {m : ℕ} (hm : m ≤ 2) (w : Fin m → ℝ) (x : Fin m → ℝ) :
    0 ≤ formationReflectedGramPlus w x := by
  rw [formationReflectedGramPlus_eq]
  have hcs := formationCodiagonalResponse_sq_le_card_mul_diagonalEnergy w x
  have hmR : (m : ℝ) ≤ 2 := by exact_mod_cast hm
  have henergy : 0 ≤ formationDiagonalEnergy w x := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

def formationReciprocalSqrtWitness {m : ℕ} (w : Fin m → ℝ) : Fin m → ℝ :=
  fun i => (Real.sqrt (w i))⁻¹

theorem formationDiagonalEnergy_reciprocalSqrtWitness
    {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    formationDiagonalEnergy w (formationReciprocalSqrtWitness w) = m := by
  simp [formationDiagonalEnergy, formationReciprocalSqrtWitness,
    ne_of_gt (Real.sqrt_pos.2 (hw _))]

theorem formationCodiagonalResponse_reciprocalSqrtWitness
    {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    formationCodiagonalResponse w (formationReciprocalSqrtWitness w) = m := by
  simp [formationCodiagonalResponse, formationReciprocalSqrtWitness,
    ne_of_gt (Real.sqrt_pos.2 (hw _))]

theorem formationReflectedGramPlus_reciprocalSqrtWitness
    {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    formationReflectedGramPlus w (formationReciprocalSqrtWitness w) =
      (m : ℝ) * (2 - m) := by
  rw [formationReflectedGramPlus_eq,
    formationDiagonalEnergy_reciprocalSqrtWitness hw,
    formationCodiagonalResponse_reciprocalSqrtWitness hw]
  ring

theorem formationReflectedGramPlus_not_nonneg_of_three_le
    {m : ℕ} (hm : 3 ≤ m) {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    ¬ ∀ x, 0 ≤ formationReflectedGramPlus w x := by
  intro h
  have hbad := h (formationReciprocalSqrtWitness w)
  rw [formationReflectedGramPlus_reciprocalSqrtWitness hw] at hbad
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  nlinarith

/-- Formation depth two is exact universal positivity threshold for positive weights. -/
theorem formationReflectedGramPlus_nonneg_iff_card_le_two
    {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    (∀ x, 0 ≤ formationReflectedGramPlus w x) ↔ m ≤ 2 := by
  constructor
  · intro hnonneg
    by_contra hnot
    exact formationReflectedGramPlus_not_nonneg_of_three_le (by omega) hw hnonneg
  · intro hm x
    exact formationReflectedGramPlus_nonneg_of_card_le_two hm w x

theorem not_both_formationReflectedGramCompletions_nonneg
    {m : ℕ} (hm : 3 ≤ m) {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    ¬ ((∀ x, 0 ≤ formationReflectedGramPlus w x) ∧
       (∀ x, 0 ≤ formationReflectedGramMinus w x)) := by
  intro h
  exact formationReflectedGramPlus_not_nonneg_of_three_le hm hw h.1

/-- Diagonal packet energy remains nonnegative after adding source-horizontal shared-reservoir
interaction for every three-channel prime packet. -/
def SourceZeroHorizontalFormationCompletePositiveAt (q : XiZeroCopy) : Prop :=
  ∀ (p : Fin 3 → Nat.Primes) (x : Fin 3 → ℝ),
    0 ≤ formationDiagonalEnergy (sourceZeroHorizontalSharedWeights q p) x +
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x

/-- Reflection-complete formation positivity on every multiplicity-exact Xi zero. -/
def SourceZeroHorizontalFormationCompletePositive : Prop :=
  ∀ q : XiZeroCopy, SourceZeroHorizontalFormationCompletePositiveAt q

private def formationThreePrimePacket : Fin 3 → Nat.Primes :=
  fun _ => ⟨2, Nat.prime_two⟩

private theorem formationCompletePositiveAt_not_left
    (q : XiZeroCopy) (hpos : SourceZeroHorizontalFormationCompletePositiveAt q) :
    ¬ (q.1 : ℂ).re < 1 / 2 := by
  intro hleft
  let p : Fin 3 → Nat.Primes := formationThreePrimePacket
  let w : Fin 3 → ℝ := sourceZeroHorizontalSharedWeights q p
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := ne_of_lt hleft
  have hw : ∀ i, 0 < w i := sourceZeroHorizontalSharedWeights_pos q hoff p
  have hreservoir :
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' =
        reservoirWeightedForm w := by
    rw [sourceZeroHorizontalSharedReservoirMatrix,
      sourceZeroHorizontalOrientation_eq_one_of_left q hleft]
    simpa [w] using orientedSourceSharedReservoirMatrix_toQuadraticForm_one
      (fun i => (hw i).le)
  have hnonneg : ∀ x, 0 ≤ formationReflectedGramPlus w x := by
    intro x
    have hx := hpos p x
    rw [hreservoir] at hx
    exact hx
  exact formationReflectedGramPlus_not_nonneg_of_three_le (by norm_num) hw hnonneg

private theorem sourceZeroHorizontal_reflection_left_of_right
    (q : XiZeroCopy) (hright : 1 / 2 < (q.1 : ℂ).re) :
    ((xiZeroCopyLineConjEquiv q).1 : ℂ).re < 1 / 2 := by
  change (1 - (starRingEnd ℂ) (q.1 : ℂ)).re < 1 / 2
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  linarith

/-- Three-channel formation positivity for a zero and its functional-equation reflection forces
critical-line placement. -/
theorem sourceZeroHorizontal_formationCompletePositive_reflection_selector
    (q : XiZeroCopy)
    (hpos : SourceZeroHorizontalFormationCompletePositiveAt q)
    (hreflected : SourceZeroHorizontalFormationCompletePositiveAt
      (xiZeroCopyLineConjEquiv q)) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoff
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · exact formationCompletePositiveAt_not_left q hpos hleft
  · exact formationCompletePositiveAt_not_left (xiZeroCopyLineConjEquiv q) hreflected
      (sourceZeroHorizontal_reflection_left_of_right q hright)

/-- Global formation-complete positivity closes exact RH selection gap. -/
theorem riemannHypothesis_of_sourceZeroHorizontalFormationCompletePositive
    (hpos : SourceZeroHorizontalFormationCompletePositive) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  intro z hz
  let rho : XiDivisorSupport :=
    ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
  let q : XiZeroCopy := ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
  simpa [q] using
    sourceZeroHorizontal_formationCompletePositive_reflection_selector q
      (hpos q) (hpos (xiZeroCopyLineConjEquiv q))

/-- Closed certificate collecting route-independent conservation, sharp fracture, and Xi
selection laws. It has no external hypotheses. -/
def FormationCompletePositivityReflectedGramFractureLaw : Prop :=
  (∀ {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ),
      formationReflectedGramPlus w x + formationReflectedGramMinus w x =
        2 * formationDiagonalEnergy w x) ∧
  (∀ {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ),
      formationReflectedGramPlus w x - formationReflectedGramMinus w x =
        2 * reservoirWeightedForm w x) ∧
  (∀ {m : ℕ} {w : Fin m → ℝ}, (∀ i, 0 < w i) →
      ((∀ x, 0 ≤ formationReflectedGramPlus w x) ↔ m ≤ 2)) ∧
  (SourceZeroHorizontalFormationCompletePositive → RiemannHypothesis)

theorem formationCompletePositivityReflectedGramFractureLaw :
    FormationCompletePositivityReflectedGramFractureLaw := by
  refine ⟨formationReflectedGramPlus_add_minus,
    formationReflectedGramPlus_sub_minus, ?_,
    riemannHypothesis_of_sourceZeroHorizontalFormationCompletePositive⟩
  intro m w hw
  exact formationReflectedGramPlus_nonneg_iff_card_le_two hw

end

end RHTower
