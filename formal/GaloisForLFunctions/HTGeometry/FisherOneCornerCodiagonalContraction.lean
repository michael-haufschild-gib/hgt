import GaloisForLFunctions.HTGeometry.FisherOneCornerCoareaTransform

/-!
# Universal joined-codiagonal contraction

The lower Fisher cutoff corner has coefficients
`sqrt (2 pᵢ pⱼ) (hᵢ + hⱼ - 2m)` on pairs straddling the cutoff.  A joined
endpoint reporter with vertex phases of norm at most one has coefficients
`sqrt (pᵢ pⱼ / 2) (dᵢ + dⱼ)` on the same pairs.

The reporter has squared norm at most `1 / 2`, uniformly in the finite
probability space, heights, cutoff, and phases.  Consequently its
codiagonal pairing with the Fisher corner has squared norm at most one half
of the corner energy.  This is the exact source-side constant: the proof is
the probability identity `2 F (1-F) ≤ 1/2`.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι]

/-- Fisher source vector carried by the ordered pairs straddling a cutoff. -/
def finiteFisherOneCornerSourceVector
    (p h : ι → ℝ) (m u : ℝ) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 (fun q =>
    if h q.2 < u ∧ u ≤ h q.1 then
      ((Real.sqrt (2 * p q.1 * p q.2) *
        (h q.1 + h q.2 - 2 * m) : ℝ) : ℂ)
    else 0)

/-- Joined endpoint reporter carried by the same cutoff corner. -/
def finiteFisherOneCornerJoinedReporter
    (p h : ι → ℝ) (d : ι → ℂ) (u : ℝ) :
    EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 (fun q =>
    if h q.2 < u ∧ u ≤ h q.1 then
      (Real.sqrt (p q.1 * p q.2 / 2) : ℂ) * (d q.1 + d q.2)
    else 0)

/-- Joined codiagonal of the Fisher corner against vertex phases `d`. -/
def finiteFisherOneCornerJoinedCodiagonal
    (p h : ι → ℝ) (m : ℝ) (d : ι → ℂ) (u : ℝ) : ℂ :=
  ∑ i, ∑ j, if h j < u ∧ u ≤ h i then
    (p i * p j * (h i + h j - 2 * m) : ℝ) * (d i + d j)
  else 0

/-- The source-vector norm is exactly the one-corner coarea density. -/
theorem finiteFisherOneCornerSourceVector_norm_sq
    (p h : ι → ℝ) (m u : ℝ) (hp : ∀ i, 0 ≤ p i) :
    ‖finiteFisherOneCornerSourceVector p h m u‖ ^ 2 =
      finiteFisherOneCornerCoareaDensity p h m u := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [finiteFisherOneCornerSourceVector]
  unfold finiteFisherOneCornerCoareaDensity finiteFisherPairAmplitudeSq
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hs
  · have hsqrt : 0 ≤ 2 * p i * p j := by
      have hij : 0 ≤ p i * p j := mul_nonneg (hp i) (hp j)
      nlinarith
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
      Real.sq_sqrt hsqrt]
    ring
  · simp

/-- An ordered pair straddles the cutoff with doubled probability at most
`1/2`.  Equality occurs at a balanced lower/upper split. -/
theorem finiteFisherOneCorner_crossProbability_le_half
    (p h : ι → ℝ) (u : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpone : ∑ i, p i = 1) :
    (∑ i, ∑ j, if h j < u ∧ u ≤ h i then 2 * p i * p j else 0) ≤
      1 / 2 := by
  have hL0 : 0 ≤ ∑ i, if h i < u then p i else 0 :=
    Finset.sum_nonneg (fun i _ => by
      split_ifs
      · exact hp i
      · norm_num)
  have hR0 : 0 ≤ ∑ i, if u ≤ h i then p i else 0 :=
    Finset.sum_nonneg (fun i _ => by
      split_ifs
      · exact hp i
      · norm_num)
  have hLR :
      (∑ i, if h i < u then p i else 0) +
        (∑ i, if u ≤ h i then p i else 0) = 1 := by
    rw [← hpone, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hlt : h i < u
    · simp [hlt, not_le.mpr hlt]
    · have hle : u ≤ h i := le_of_not_gt hlt
      simp [hlt, hle]
  have hcross :
      (∑ i, ∑ j, if h j < u ∧ u ≤ h i then 2 * p i * p j else 0) =
        2 * (∑ i, if u ≤ h i then p i else 0) *
          (∑ j, if h j < u then p j else 0) := by
    calc
      (∑ i, ∑ j, if h j < u ∧ u ≤ h i then 2 * p i * p j else 0) =
          ∑ i, (if u ≤ h i then
            2 * p i * (∑ j, if h j < u then p j else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hui : u ≤ h i
        · simp only [hui, and_true, if_true, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : h j < u <;> simp [hji]
        · simp [hui]
      _ = (∑ i, if u ≤ h i then 2 * p i else 0) *
          (∑ j, if h j < u then p j else 0) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hui : u ≤ h i <;> simp [hui]
      _ = 2 * (∑ i, if u ≤ h i then p i else 0) *
          (∑ j, if h j < u then p j else 0) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hui : u ≤ h i <;> simp [hui]
  rw [hcross]
  nlinarith [sq_nonneg
    ((∑ i, if h i < u then p i else 0) -
      (∑ i, if u ≤ h i then p i else 0))]

/-- Every joined endpoint reporter with unit-bounded vertex phases uses at
most half a unit of Hilbert energy. -/
theorem finiteFisherOneCornerJoinedReporter_norm_sq_le_half
    (p h : ι → ℝ) (d : ι → ℂ) (u : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpone : ∑ i, p i = 1)
    (hd : ∀ i, ‖d i‖ ≤ 1) :
    ‖finiteFisherOneCornerJoinedReporter p h d u‖ ^ 2 ≤ 1 / 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [finiteFisherOneCornerJoinedReporter]
  rw [Fintype.sum_prod_type]
  calc
    (∑ i, ∑ j, ‖if h j < u ∧ u ≤ h i then
        (Real.sqrt (p i * p j / 2) : ℂ) * (d i + d j) else 0‖ ^ 2) ≤
      ∑ i, ∑ j, if h j < u ∧ u ≤ h i then 2 * p i * p j else 0 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · have hpij : 0 ≤ p i * p j / 2 :=
            div_nonneg (mul_nonneg (hp i) (hp j)) (by norm_num)
          have hadd : ‖d i + d j‖ ≤ 2 := by
            calc
              ‖d i + d j‖ ≤ ‖d i‖ + ‖d j‖ := norm_add_le _ _
              _ ≤ 1 + 1 := add_le_add (hd i) (hd j)
              _ = 2 := by norm_num
          have haddsq : ‖d i + d j‖ ^ 2 ≤ 4 := by
            nlinarith [norm_nonneg (d i + d j)]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
            Real.sq_sqrt hpij]
          have hmul := mul_le_mul_of_nonneg_left haddsq hpij
          nlinarith
        · simp
    _ ≤ 1 / 2 :=
      finiteFisherOneCorner_crossProbability_le_half p h u hp hpone

/-- The joined codiagonal is the Hilbert pairing of the exact Fisher source
with its endpoint reporter. -/
theorem inner_finiteFisherOneCornerSourceVector_joinedReporter
    (p h : ι → ℝ) (m : ℝ) (d : ι → ℂ) (u : ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    inner ℂ (finiteFisherOneCornerSourceVector p h m u)
        (finiteFisherOneCornerJoinedReporter p h d u) =
      finiteFisherOneCornerJoinedCodiagonal p h m d u := by
  rw [finiteFisherOneCornerSourceVector,
    finiteFisherOneCornerJoinedReporter, EuclideanSpace.inner_toLp_toLp]
  unfold dotProduct finiteFisherOneCornerJoinedCodiagonal
  simp only [Pi.star_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · have hpij : 0 ≤ p i * p j := mul_nonneg (hp i) (hp j)
    have hs1 : Real.sqrt (p i * p j / 2) ^ 2 = p i * p j / 2 :=
      Real.sq_sqrt (div_nonneg hpij (by norm_num))
    have hs2 : Real.sqrt (2 * p i * p j) ^ 2 = 2 * p i * p j :=
      Real.sq_sqrt (by nlinarith)
    have hsqrt : Real.sqrt (p i * p j / 2) *
        Real.sqrt (2 * p i * p j) = p i * p j := by
      have hleft : 0 ≤ Real.sqrt (p i * p j / 2) *
          Real.sqrt (2 * p i * p j) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      nlinarith [sq_nonneg (Real.sqrt (p i * p j / 2) *
        Real.sqrt (2 * p i * p j) + p i * p j)]
    push_cast
    change ((Real.sqrt (p i * p j / 2) : ℂ) * (d i + d j)) *
      (starRingEnd ℂ) (((Real.sqrt (2 * p i * p j) : ℂ) *
        (((h i : ℂ) + (h j : ℂ)) - 2 * (m : ℂ)))) =
        ((p i : ℂ) * (p j : ℂ) *
          (((h i : ℂ) + (h j : ℂ)) - 2 * (m : ℂ))) * (d i + d j)
    rw [map_mul, Complex.conj_ofReal, map_sub, map_add,
      Complex.conj_ofReal, Complex.conj_ofReal, map_mul, map_ofNat,
      Complex.conj_ofReal]
    have hsqrtC :
        (Real.sqrt (p i * p j / 2) : ℂ) *
          (Real.sqrt (2 * p i * p j) : ℂ) =
            ((p i * p j : ℝ) : ℂ) := by
      exact_mod_cast hsqrt
    calc
      (Real.sqrt (p i * p j / 2) : ℂ) * (d i + d j) *
          ((Real.sqrt (2 * p i * p j) : ℂ) *
            (((h i : ℂ) + (h j : ℂ)) - 2 * (m : ℂ))) =
          ((Real.sqrt (p i * p j / 2) : ℂ) *
            (Real.sqrt (2 * p i * p j) : ℂ)) *
              (((h i : ℂ) + (h j : ℂ)) - 2 * (m : ℂ)) *
                (d i + d j) := by ring
      _ = ((p i : ℂ) * (p j : ℂ) *
          (((h i : ℂ) + (h j : ℂ)) - 2 * (m : ℂ))) *
            (d i + d j) := by rw [hsqrtC]; push_cast; rfl
  · simp

/-- **Universal joined-codiagonal contraction.**  The squared magnitude of
every unit-phase joined codiagonal is at most one half of the physical
one-corner Fisher coarea density. -/
theorem norm_sq_finiteFisherOneCornerJoinedCodiagonal_le_half_density
    (p h : ι → ℝ) (m : ℝ) (d : ι → ℂ) (u : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpone : ∑ i, p i = 1)
    (hd : ∀ i, ‖d i‖ ≤ 1) :
    ‖finiteFisherOneCornerJoinedCodiagonal p h m d u‖ ^ 2 ≤
      (1 / 2 : ℝ) * finiteFisherOneCornerCoareaDensity p h m u := by
  rw [← inner_finiteFisherOneCornerSourceVector_joinedReporter
      p h m d u hp,
    ← finiteFisherOneCornerSourceVector_norm_sq p h m u hp]
  have hinner := norm_inner_le_norm (𝕜 := ℂ)
    (finiteFisherOneCornerSourceVector p h m u)
    (finiteFisherOneCornerJoinedReporter p h d u)
  have hsq :
      ‖inner ℂ (finiteFisherOneCornerSourceVector p h m u)
        (finiteFisherOneCornerJoinedReporter p h d u)‖ ^ 2 ≤
      (‖finiteFisherOneCornerSourceVector p h m u‖ *
        ‖finiteFisherOneCornerJoinedReporter p h d u‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
  have hrep :=
    finiteFisherOneCornerJoinedReporter_norm_sq_le_half
      p h d u hp hpone hd
  rw [show
      (‖finiteFisherOneCornerSourceVector p h m u‖ *
        ‖finiteFisherOneCornerJoinedReporter p h d u‖) ^ 2 =
      ‖finiteFisherOneCornerSourceVector p h m u‖ ^ 2 *
        ‖finiteFisherOneCornerJoinedReporter p h d u‖ ^ 2 by ring] at hsq
  calc
    ‖inner ℂ (finiteFisherOneCornerSourceVector p h m u)
        (finiteFisherOneCornerJoinedReporter p h d u)‖ ^ 2 ≤
        ‖finiteFisherOneCornerSourceVector p h m u‖ ^ 2 *
          ‖finiteFisherOneCornerJoinedReporter p h d u‖ ^ 2 := hsq
    _ ≤ ‖finiteFisherOneCornerSourceVector p h m u‖ ^ 2 * (1 / 2) :=
      mul_le_mul_of_nonneg_left hrep (sq_nonneg _)
    _ = (1 / 2) * ‖finiteFisherOneCornerSourceVector p h m u‖ ^ 2 := by ring

end GaloisForLFunctions.HTGeometry
