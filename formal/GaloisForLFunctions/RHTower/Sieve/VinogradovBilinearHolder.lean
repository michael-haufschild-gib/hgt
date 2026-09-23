import GaloisForLFunctions.RHTower.Sieve.VinogradovActualMoment

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

theorem norm_fintype_sum_pow_le_card_mul_sum_norm_pow
    {ι : Type*} [Fintype ι] (z : ι → ℂ) (r : ℕ) :
    ‖∑ i : ι, z i‖ ^ (r + 1) ≤
      (Fintype.card ι : ℝ) ^ r * ∑ i : ι, ‖z i‖ ^ (r + 1) := by
  calc
    ‖∑ i : ι, z i‖ ^ (r + 1) ≤
        (∑ i : ι, ‖z i‖) ^ (r + 1) := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa using norm_sum_le Finset.univ z
    _ ≤ (Fintype.card ι : ℝ) ^ r *
        ∑ i : ι, ‖z i‖ ^ (r + 1) := by
      simpa using pow_sum_le_card_mul_sum_pow
        (s := (Finset.univ : Finset ι))
        (f := fun i => ‖z i‖) (fun _ _ => norm_nonneg _) r

def vinogradovBilinearPolynomialPhase
    {X Y k : ℕ} (α : Fin k → ℝ) (l : Fin X) (m : Fin Y) : ℝ :=
  ∑ j : Fin k, α j * (((l.val : ℝ) * (m.val : ℝ)) ^ (j.val + 1))

def vinogradovBilinearSum
    {X Y k : ℕ} (α : Fin k → ℝ) : ℂ :=
  ∑ l : Fin X, finitePhaseSum
    (vinogradovBilinearPolynomialPhase α l : Fin Y → ℝ)

theorem card_vinogradovTuplePair (Y b : ℕ) :
    Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) = Y ^ (2 * b) := by
  rw [Fintype.card_prod]
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [← pow_add]
  congr 1
  omega

theorem vinogradovBilinearPolynomialPhase_tupleDifference
    {X Y b k : ℕ} (α : Fin k → ℝ) (l : Fin X)
    (uv : (Fin b → Fin Y) × (Fin b → Fin Y)) :
    (∑ i : Fin b, vinogradovBilinearPolynomialPhase α l (uv.1 i)) -
        ∑ i : Fin b, vinogradovBilinearPolynomialPhase α l (uv.2 i) =
      vinogradovActualPolynomialPhase α uv l := by
  unfold vinogradovBilinearPolynomialPhase
  unfold vinogradovActualPolynomialPhase finiteVinogradovPolynomialPhase
  have hleft :
      (∑ i : Fin b, ∑ j : Fin k,
        α j * (((l.val : ℝ) * ((uv.1 i).val : ℝ)) ^ (j.val + 1))) =
      ∑ j : Fin k, ∑ i : Fin b,
        α j * (((l.val : ℝ) * ((uv.1 i).val : ℝ)) ^ (j.val + 1)) :=
    Finset.sum_comm
  have hright :
      (∑ i : Fin b, ∑ j : Fin k,
        α j * (((l.val : ℝ) * ((uv.2 i).val : ℝ)) ^ (j.val + 1))) =
      ∑ j : Fin k, ∑ i : Fin b,
        α j * (((l.val : ℝ) * ((uv.2 i).val : ℝ)) ^ (j.val + 1)) :=
    Finset.sum_comm
  rw [hleft, hright, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold vinogradovActualDifference
  simp_rw [mul_pow, ← Finset.mul_sum]
  ring

theorem sum_bilinearInnerMoment_eq_sum_actualPolynomialPhase
    {X Y b k : ℕ} (α : Fin k → ℝ) :
    (((∑ l : Fin X, Complex.normSq (finitePhaseSum
        (vinogradovBilinearPolynomialPhase α l : Fin Y → ℝ)) ^ b : ℝ) : ℝ) : ℂ) =
      ∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
        finitePhaseSum (vinogradovActualPolynomialPhase α uv : Fin X → ℝ) := by
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_pow]
  simp_rw [finitePhaseMoment_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro uv _
  unfold finitePhaseSum
  apply Finset.sum_congr rfl
  intro l _
  rw [vinogradovBilinearPolynomialPhase_tupleDifference]

theorem sum_bilinearInnerMoment_le_sum_norm_actualPolynomialPhase
    {X Y b k : ℕ} (α : Fin k → ℝ) :
    (∑ l : Fin X, Complex.normSq (finitePhaseSum
        (vinogradovBilinearPolynomialPhase α l : Fin Y → ℝ)) ^ b) ≤
      ∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
        ‖finitePhaseSum (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)‖ := by
  let A : ℝ := ∑ l : Fin X, Complex.normSq (finitePhaseSum
    (vinogradovBilinearPolynomialPhase α l : Fin Y → ℝ)) ^ b
  have hA : 0 ≤ A := by
    exact Finset.sum_nonneg fun l _ => pow_nonneg (Complex.normSq_nonneg _) _
  have heq := sum_bilinearInnerMoment_eq_sum_actualPolynomialPhase
    (X := X) (Y := Y) (b := b) α
  calc
    (∑ l : Fin X, Complex.normSq (finitePhaseSum
        (vinogradovBilinearPolynomialPhase α l : Fin Y → ℝ)) ^ b) =
        ‖((A : ℝ) : ℂ)‖ := by
      change A = ‖(A : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
    _ = ‖∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
        finitePhaseSum (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)‖ := by
      rw [heq]
    _ ≤ ∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
        ‖finitePhaseSum (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)‖ := by
      simpa using norm_sum_le Finset.univ
        (fun uv : (Fin b → Fin Y) × (Fin b → Fin Y) =>
          finitePhaseSum (vinogradovActualPolynomialPhase α uv : Fin X → ℝ))

/-- First outer Hölder step in MV24.7, with exact finite cardinality and no
logarithmic endpoint loss. -/
theorem norm_vinogradovBilinearSum_pow_le_firstHolder
    {X Y b k : ℕ} (hb : b ≠ 0) (α : Fin k → ℝ) :
    ‖vinogradovBilinearSum (X := X) (Y := Y) α‖ ^ (2 * b) ≤
      (X : ℝ) ^ (2 * b - 1) *
        ∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
          ‖finitePhaseSum
            (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)‖ := by
  let z : Fin X → ℂ := fun l => finitePhaseSum
    (vinogradovBilinearPolynomialPhase α l : Fin Y → ℝ)
  have hexp : 2 * b - 1 + 1 = 2 * b := by omega
  have hholder := norm_fintype_sum_pow_le_card_mul_sum_norm_pow
    z (2 * b - 1)
  rw [hexp] at hholder
  calc
    ‖vinogradovBilinearSum (X := X) (Y := Y) α‖ ^ (2 * b) ≤
        (X : ℝ) ^ (2 * b - 1) * ∑ l : Fin X, ‖z l‖ ^ (2 * b) := by
      simpa [vinogradovBilinearSum, z] using hholder
    _ = (X : ℝ) ^ (2 * b - 1) *
        ∑ l : Fin X, Complex.normSq (finitePhaseSum
          (vinogradovBilinearPolynomialPhase α l : Fin Y → ℝ)) ^ b := by
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      simp only [Complex.normSq_eq_norm_sq]
      rw [← pow_mul]
    _ ≤ (X : ℝ) ^ (2 * b - 1) *
        ∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
          ‖finitePhaseSum
            (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)‖ := by
      gcongr
      exact sum_bilinearInnerMoment_le_sum_norm_actualPolynomialPhase α

/-- Both outer Hölder steps, followed by both exact Vinogradov groupings.
The remaining factor is precisely the tensor product of one-dimensional
Fejér kernel sums. -/
theorem norm_vinogradovBilinearSum_pow_le_coordinateProduct
    {X Y b k : ℕ} (hb : b ≠ 0) (hX : X ≠ 0) (hY : Y ≠ 0)
    (α : Fin k → ℝ) :
    ‖vinogradovBilinearSum (X := X) (Y := Y) α‖ ^ (4 * b ^ (2 : ℕ)) ≤
      (((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) ^ (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k,
              ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
                vinogradovCoordinateKernelWeight (Y := Y) α j g := by
  let z : ((Fin b → Fin Y) × (Fin b → Fin Y)) → ℂ := fun uv =>
    finitePhaseSum (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)
  have hfirst := norm_vinogradovBilinearSum_pow_le_firstHolder
    (X := X) (Y := Y) hb α
  have hraised := pow_le_pow_left₀
    (pow_nonneg (norm_nonneg _) _) hfirst (2 * b)
  have hexp : 2 * b - 1 + 1 = 2 * b := by omega
  have hsecond := pow_sum_le_card_mul_sum_pow
    (s := (Finset.univ : Finset ((Fin b → Fin Y) × (Fin b → Fin Y))))
    (f := fun uv => ‖z uv‖) (fun _ _ => norm_nonneg _) (2 * b - 1)
  rw [hexp] at hsecond
  have hmoment :
      (∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y), ‖z uv‖ ^ (2 * b)) =
        ∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
          Complex.normSq (finitePhaseSum
            (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)) ^ b := by
    apply Finset.sum_congr rfl
    intro uv _
    unfold z
    simp only [Complex.normSq_eq_norm_sq]
    rw [← pow_mul]
  calc
    ‖vinogradovBilinearSum (X := X) (Y := Y) α‖ ^ (4 * b ^ (2 : ℕ)) =
        (‖vinogradovBilinearSum (X := X) (Y := Y) α‖ ^ (2 * b)) ^
          (2 * b) := by rw [← pow_mul]; congr 1; ring
    _ ≤ (((X : ℝ) ^ (2 * b - 1)) *
        ∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y), ‖z uv‖) ^ (2 * b) := by
      simpa [z] using hraised
    _ = ((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y), ‖z uv‖) ^ (2 * b) := by
      rw [mul_pow]
    _ ≤ ((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        ((Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) ^
          (2 * b - 1) * ∑ uv, ‖z uv‖ ^ (2 * b)) := by
      exact mul_le_mul_of_nonneg_left hsecond (by positivity)
    _ = (((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) ^
          (2 * b - 1)) *
            ∑ uv : (Fin b → Fin Y) × (Fin b → Fin Y),
              Complex.normSq (finitePhaseSum
                (vinogradovActualPolynomialPhase α uv : Fin X → ℝ)) ^ b := by
      rw [hmoment]
      ring
    _ ≤ (((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) ^
          (2 * b - 1)) *
        (((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k,
              ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
                vinogradovCoordinateKernelWeight (Y := Y) α j g) := by
      apply mul_le_mul_of_nonneg_left
        (sum_vinogradovActualPolynomialMoment_le_coordinateProduct hX hY α)
      positivity
    _ = (((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) ^
          (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k,
              ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
                vinogradovCoordinateKernelWeight (Y := Y) α j g := by ring

theorem norm_vinogradovBilinearSum_pow_le_rationalProduct
    {X Y b k : ℕ} (hb : b ≠ 0) (hX : X ≠ 0) (hY : Y ≠ 0)
    (α : Fin k → ℝ) (a q : Fin k → ℕ)
    (hq : ∀ j, 0 < q j) (hcop : ∀ j, Nat.Coprime (a j) (q j))
    (happrox : ∀ j,
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ (2 : ℕ)) :
    ‖vinogradovBilinearSum (X := X) (Y := Y) α‖ ^ (4 * b ^ (2 : ℕ)) ≤
      (((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) ^ (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k,
              vinogradovRationalCoordinateCost X Y b (q j) j := by
  calc
    _ ≤ (((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) ^
          (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k,
              ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
                vinogradovCoordinateKernelWeight (Y := Y) α j g :=
      norm_vinogradovBilinearSum_pow_le_coordinateProduct hb hX hY α
    _ ≤ (((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) ^
          (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k,
              vinogradovRationalCoordinateCost X Y b (q j) j := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.prod_le_prod
        · intro j _
          exact Finset.sum_nonneg fun g _ =>
            vinogradovCoordinateKernelWeight_nonneg α j g
        · intro j _
          exact sum_vinogradovCoordinateKernelWeight_le_rationalApprox
            hX (hq j) α j (hcop j) (happrox j)
      · positivity

def vinogradovMixedCoordinateCost
    {k : ℕ} (U : Fin k → Prop) [DecidablePred U]
    (X Y b : ℕ) (q : Fin k → ℕ) (j : Fin k) : ℝ :=
  if U j then vinogradovRationalCoordinateCost X Y b (q j) j
  else vinogradovTrivialCoordinateCost X Y b j

theorem vinogradovMixedCoordinateCost_nonneg
    {k : ℕ} (U : Fin k → Prop) [DecidablePred U]
    (X Y b : ℕ) (q : Fin k → ℕ) (j : Fin k) :
    0 ≤ vinogradovMixedCoordinateCost U X Y b q j := by
  unfold vinogradovMixedCoordinateCost
  split_ifs
  · exact vinogradovRationalCoordinateCost_nonneg X Y b (q j) j
  · exact vinogradovTrivialCoordinateCost_nonneg X Y b j

/-- Mixed MV24.7 bound: rational approximation is consumed only on the
useful coordinates.  Remaining coordinates use the unconditional trivial
kernel mass, so no artificial denominator hypotheses leak into the
single-sum argument. -/
theorem norm_vinogradovBilinearSum_pow_le_mixedProduct
    {X Y b k : ℕ} (hb : b ≠ 0) (hX : X ≠ 0) (hY : Y ≠ 0)
    (α : Fin k → ℝ) (U : Fin k → Prop) [DecidablePred U]
    (a q : Fin k → ℕ)
    (hq : ∀ j, U j → 0 < q j)
    (hcop : ∀ j, U j → Nat.Coprime (a j) (q j))
    (happrox : ∀ j, U j →
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ (2 : ℕ)) :
    ‖vinogradovBilinearSum (X := X) (Y := Y) α‖ ^ (4 * b ^ (2 : ℕ)) ≤
      (((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) ^ (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k, vinogradovMixedCoordinateCost U X Y b q j := by
  calc
    _ ≤ (((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) ^
          (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k,
              ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
                vinogradovCoordinateKernelWeight (Y := Y) α j g :=
      norm_vinogradovBilinearSum_pow_le_coordinateProduct hb hX hY α
    _ ≤ (((X : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y) × (Fin b → Fin Y)) : ℝ) ^
          (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k, vinogradovMixedCoordinateCost U X Y b q j := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.prod_le_prod
        · intro j _
          exact Finset.sum_nonneg fun g _ =>
            vinogradovCoordinateKernelWeight_nonneg α j g
        · intro j _
          unfold vinogradovMixedCoordinateCost
          split_ifs with hj
          · exact sum_vinogradovCoordinateKernelWeight_le_rationalApprox
              hX (hq j hj) α j (hcop j hj) (happrox j hj)
          · exact sum_vinogradovCoordinateKernelWeight_le_trivial hX α j
      · positivity

end

end RHTower.Sieve
