import GaloisForLFunctions.RHTower.Sieve.VinogradovEmbeddedActualMoment
import GaloisForLFunctions.RHTower.Sieve.VinogradovBilinearHolder

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovEmbeddedBilinearPolynomialPhase
    {X₀ X Y₀ Y k : ℕ} (eX : Fin X₀ ↪ Fin X) (eY : Fin Y₀ ↪ Fin Y)
    (α : Fin k → ℝ) (l : Fin X₀) (m : Fin Y₀) : ℝ :=
  vinogradovBilinearPolynomialPhase α (eX l) (eY m)

def vinogradovEmbeddedBilinearSum
    {X₀ X Y₀ Y k : ℕ} (eX : Fin X₀ ↪ Fin X) (eY : Fin Y₀ ↪ Fin Y)
    (α : Fin k → ℝ) : ℂ :=
  ∑ l : Fin X₀, finitePhaseSum
    (vinogradovEmbeddedBilinearPolynomialPhase eX eY α l : Fin Y₀ → ℝ)

theorem vinogradovEmbeddedBilinearPolynomialPhase_tupleDifference
    {X₀ X Y₀ Y b k : ℕ} (eX : Fin X₀ ↪ Fin X) (eY : Fin Y₀ ↪ Fin Y)
    (α : Fin k → ℝ) (l : Fin X₀)
    (uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀)) :
    (∑ i : Fin b, vinogradovEmbeddedBilinearPolynomialPhase eX eY α l (uv.1 i)) -
        ∑ i : Fin b, vinogradovEmbeddedBilinearPolynomialPhase eX eY α l (uv.2 i) =
      vinogradovEmbeddedActualPolynomialPhase eX eY α uv l := by
  unfold vinogradovEmbeddedBilinearPolynomialPhase
  unfold vinogradovEmbeddedActualPolynomialPhase
  exact vinogradovBilinearPolynomialPhase_tupleDifference α (eX l)
    (vinogradovMapTuplePair eY uv)

theorem sum_embeddedBilinearInnerMoment_eq_sum_actualPolynomialPhase
    {X₀ X Y₀ Y b k : ℕ} (eX : Fin X₀ ↪ Fin X) (eY : Fin Y₀ ↪ Fin Y)
    (α : Fin k → ℝ) :
    (((∑ l : Fin X₀, Complex.normSq (finitePhaseSum
        (vinogradovEmbeddedBilinearPolynomialPhase eX eY α l : Fin Y₀ → ℝ)) ^ b : ℝ) : ℝ) : ℂ) =
      ∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀),
        finitePhaseSum (vinogradovEmbeddedActualPolynomialPhase eX eY α uv) := by
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_pow]
  simp_rw [finitePhaseMoment_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro uv _
  unfold finitePhaseSum
  apply Finset.sum_congr rfl
  intro l _
  rw [vinogradovEmbeddedBilinearPolynomialPhase_tupleDifference]

theorem sum_embeddedBilinearInnerMoment_le_sum_norm_actualPolynomialPhase
    {X₀ X Y₀ Y b k : ℕ} (eX : Fin X₀ ↪ Fin X) (eY : Fin Y₀ ↪ Fin Y)
    (α : Fin k → ℝ) :
    (∑ l : Fin X₀, Complex.normSq (finitePhaseSum
        (vinogradovEmbeddedBilinearPolynomialPhase eX eY α l : Fin Y₀ → ℝ)) ^ b) ≤
      ∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀),
        ‖finitePhaseSum (vinogradovEmbeddedActualPolynomialPhase eX eY α uv)‖ := by
  let A : ℝ := ∑ l : Fin X₀, Complex.normSq (finitePhaseSum
    (vinogradovEmbeddedBilinearPolynomialPhase eX eY α l : Fin Y₀ → ℝ)) ^ b
  have hA : 0 ≤ A := Finset.sum_nonneg fun l _ =>
    pow_nonneg (Complex.normSq_nonneg _) _
  have heq := sum_embeddedBilinearInnerMoment_eq_sum_actualPolynomialPhase
    (b := b) eX eY α
  calc
    _ = ‖((A : ℝ) : ℂ)‖ := by
      change A = ‖(A : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
    _ = ‖∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀),
        finitePhaseSum (vinogradovEmbeddedActualPolynomialPhase eX eY α uv)‖ := by
      rw [heq]
    _ ≤ ∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀),
        ‖finitePhaseSum (vinogradovEmbeddedActualPolynomialPhase eX eY α uv)‖ := by
      simpa using norm_sum_le Finset.univ
        (fun uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀) =>
          finitePhaseSum (vinogradovEmbeddedActualPolynomialPhase eX eY α uv))

theorem norm_vinogradovEmbeddedBilinearSum_pow_le_firstHolder
    {X₀ X Y₀ Y b k : ℕ} (hb : b ≠ 0)
    (eX : Fin X₀ ↪ Fin X) (eY : Fin Y₀ ↪ Fin Y) (α : Fin k → ℝ) :
    ‖vinogradovEmbeddedBilinearSum eX eY α‖ ^ (2 * b) ≤
      (X₀ : ℝ) ^ (2 * b - 1) *
        ∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀),
          ‖finitePhaseSum (vinogradovEmbeddedActualPolynomialPhase eX eY α uv)‖ := by
  let z : Fin X₀ → ℂ := fun l => finitePhaseSum
    (vinogradovEmbeddedBilinearPolynomialPhase eX eY α l : Fin Y₀ → ℝ)
  have hexp : 2 * b - 1 + 1 = 2 * b := by omega
  have hholder := norm_fintype_sum_pow_le_card_mul_sum_norm_pow z (2 * b - 1)
  rw [hexp] at hholder
  calc
    _ ≤ (X₀ : ℝ) ^ (2 * b - 1) * ∑ l : Fin X₀, ‖z l‖ ^ (2 * b) := by
      simpa [vinogradovEmbeddedBilinearSum, z] using hholder
    _ = (X₀ : ℝ) ^ (2 * b - 1) *
        ∑ l : Fin X₀, Complex.normSq (finitePhaseSum
          (vinogradovEmbeddedBilinearPolynomialPhase eX eY α l : Fin Y₀ → ℝ)) ^ b := by
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      simp only [Complex.normSq_eq_norm_sq]
      rw [← pow_mul]
    _ ≤ (X₀ : ℝ) ^ (2 * b - 1) *
        ∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀),
          ‖finitePhaseSum (vinogradovEmbeddedActualPolynomialPhase eX eY α uv)‖ := by
      gcongr
      exact sum_embeddedBilinearInnerMoment_le_sum_norm_actualPolynomialPhase
        eX eY α

/-- Complete finite MV24.7 bridge for arbitrary injective interval
embeddings.  Outer Hölder pays actual interval cardinalities `X₀,Y₀`,
while both mean values and coordinate ranges use ambient boxes `X,Y`. -/
theorem norm_vinogradovEmbeddedBilinearSum_pow_le_coordinateProduct
    {X₀ X Y₀ Y b k : ℕ} (hb : b ≠ 0) (hX : X ≠ 0) (hY : Y ≠ 0)
    (eX : Fin X₀ ↪ Fin X) (eY : Fin Y₀ ↪ Fin Y) (α : Fin k → ℝ) :
    ‖vinogradovEmbeddedBilinearSum eX eY α‖ ^ (4 * b ^ 2) ≤
      (((X₀ : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y₀) × (Fin b → Fin Y₀)) : ℝ) ^
          (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k,
              ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
                vinogradovCoordinateKernelWeight (Y := Y) α j g := by
  let z : ((Fin b → Fin Y₀) × (Fin b → Fin Y₀)) → ℂ := fun uv =>
    finitePhaseSum (vinogradovEmbeddedActualPolynomialPhase eX eY α uv)
  have hfirst := norm_vinogradovEmbeddedBilinearSum_pow_le_firstHolder
    hb eX eY α
  have hraised := pow_le_pow_left₀
    (pow_nonneg (norm_nonneg _) _) hfirst (2 * b)
  have hexp : 2 * b - 1 + 1 = 2 * b := by omega
  have hsecond := pow_sum_le_card_mul_sum_pow
    (s := (Finset.univ : Finset ((Fin b → Fin Y₀) × (Fin b → Fin Y₀))))
    (f := fun uv => ‖z uv‖) (fun _ _ => norm_nonneg _) (2 * b - 1)
  rw [hexp] at hsecond
  have hmoment :
      (∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀), ‖z uv‖ ^ (2 * b)) =
        ∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀),
          Complex.normSq (finitePhaseSum
            (vinogradovEmbeddedActualPolynomialPhase eX eY α uv)) ^ b := by
    apply Finset.sum_congr rfl
    intro uv _
    unfold z
    simp only [Complex.normSq_eq_norm_sq]
    rw [← pow_mul]
  calc
    _ = (‖vinogradovEmbeddedBilinearSum eX eY α‖ ^ (2 * b)) ^ (2 * b) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ (((X₀ : ℝ) ^ (2 * b - 1)) *
        ∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀), ‖z uv‖) ^ (2 * b) := by
      simpa [z] using hraised
    _ = ((X₀ : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀), ‖z uv‖) ^ (2 * b) := by
      rw [mul_pow]
    _ ≤ ((X₀ : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        ((Fintype.card ((Fin b → Fin Y₀) × (Fin b → Fin Y₀)) : ℝ) ^
          (2 * b - 1) * ∑ uv, ‖z uv‖ ^ (2 * b)) := by
      exact mul_le_mul_of_nonneg_left hsecond (by positivity)
    _ = (((X₀ : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y₀) × (Fin b → Fin Y₀)) : ℝ) ^
          (2 * b - 1)) *
            ∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀),
              Complex.normSq (finitePhaseSum
                (vinogradovEmbeddedActualPolynomialPhase eX eY α uv)) ^ b := by
      rw [hmoment]
      ring
    _ ≤ (((X₀ : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y₀) × (Fin b → Fin Y₀)) : ℝ) ^
          (2 * b - 1)) *
        (((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k,
              ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
                vinogradovCoordinateKernelWeight (Y := Y) α j g) := by
      gcongr
      exact sum_vinogradovEmbeddedActualPolynomialMoment_le_coordinateProduct
        eX eY hX hY α
    _ = (((X₀ : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y₀) × (Fin b → Fin Y₀)) : ℝ) ^
          (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k,
              ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
                vinogradovCoordinateKernelWeight (Y := Y) α j g := by ring

theorem norm_vinogradovEmbeddedBilinearSum_pow_le_mixedProduct
    {X₀ X Y₀ Y b k : ℕ} (hb : b ≠ 0) (hX : X ≠ 0) (hY : Y ≠ 0)
    (eX : Fin X₀ ↪ Fin X) (eY : Fin Y₀ ↪ Fin Y) (α : Fin k → ℝ)
    (U : Fin k → Prop) [DecidablePred U] (a q : Fin k → ℕ)
    (hq : ∀ j, U j → 0 < q j)
    (hcop : ∀ j, U j → Nat.Coprime (a j) (q j))
    (happrox : ∀ j, U j →
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ 2) :
    ‖vinogradovEmbeddedBilinearSum eX eY α‖ ^ (4 * b ^ 2) ≤
      (((X₀ : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y₀) × (Fin b → Fin Y₀)) : ℝ) ^
          (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k, vinogradovMixedCoordinateCost U X Y b q j := by
  calc
    _ ≤ (((X₀ : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y₀) × (Fin b → Fin Y₀)) : ℝ) ^
          (2 * b - 1)) *
        ((Fintype.card (VinogradovDiagonalSolution Y b k) : ℝ) *
          Fintype.card (VinogradovDiagonalSolution X b k)) *
            ∏ j : Fin k,
              ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
                vinogradovCoordinateKernelWeight (Y := Y) α j g :=
      norm_vinogradovEmbeddedBilinearSum_pow_le_coordinateProduct
        hb hX hY eX eY α
    _ ≤ (((X₀ : ℝ) ^ (2 * b - 1)) ^ (2 * b) *
        (Fintype.card ((Fin b → Fin Y₀) × (Fin b → Fin Y₀)) : ℝ) ^
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
