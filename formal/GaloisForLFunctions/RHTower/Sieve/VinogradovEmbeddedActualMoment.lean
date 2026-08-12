import GaloisForLFunctions.RHTower.Sieve.VinogradovActualMoment

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovMapTuple {A N b : ℕ} (e : Fin A ↪ Fin N)
    (u : Fin b → Fin A) : Fin b → Fin N :=
  fun i => e (u i)

theorem vinogradovMapTuple_injective {A N b : ℕ} (e : Fin A ↪ Fin N) :
    Function.Injective (vinogradovMapTuple (b := b) e) := by
  intro u v huv
  funext i
  exact e.injective (congrFun huv i)

def vinogradovMapTuplePair {A N b : ℕ} (e : Fin A ↪ Fin N)
    (uv : (Fin b → Fin A) × (Fin b → Fin A)) :
      (Fin b → Fin N) × (Fin b → Fin N) :=
  (vinogradovMapTuple e uv.1, vinogradovMapTuple e uv.2)

theorem vinogradovMapTuplePair_injective {A N b : ℕ} (e : Fin A ↪ Fin N) :
    Function.Injective (vinogradovMapTuplePair (b := b) e) := by
  intro uv xy h
  apply Prod.ext
  · exact vinogradovMapTuple_injective e (congrArg Prod.fst h)
  · exact vinogradovMapTuple_injective e (congrArg Prod.snd h)

def vinogradovEmbeddedActualPolynomialPhase
    {X₀ X Y₀ Y b k : ℕ} (eX : Fin X₀ ↪ Fin X) (eY : Fin Y₀ ↪ Fin Y)
    (α : Fin k → ℝ) (uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀)) :
      Fin X₀ → ℝ :=
  fun l => vinogradovActualPolynomialPhase α
    (vinogradovMapTuplePair eY uv) (eX l)

def vinogradovEmbeddedFejerPolynomialPhase
    {X₀ X Y b k : ℕ} (eX : Fin X₀ ↪ Fin X) (α : Fin k → ℝ)
    (l : Fin k → Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius Y b k))) : Fin X₀ → ℝ :=
  fun n => vinogradovFejerPolynomialPhase α l (eX n)

def vinogradovEmbeddedWideDifferenceSignature
    {Y₀ Y b k : ℕ} (eY : Fin Y₀ ↪ Fin Y) (hY : Y ≠ 0) :
    ((Fin b → Fin Y₀) × (Fin b → Fin Y₀)) →
      (Fin k → Fin (vinogradovWideDifferenceBoxSize
        (vinogradovFejerRadius Y b k))) :=
  fun uv => vinogradovWideDifferenceSignature hY
    (vinogradovRawDifference_le_fejerRadius Y b k)
    (vinogradovMapTuplePair eY uv)

def vinogradovEmbeddedWideDifferenceFiberEmbedding
    {Y₀ Y b k : ℕ} (eY : Fin Y₀ ↪ Fin Y) (hY : Y ≠ 0)
    (l : Fin k → Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius Y b k))) :
    {uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀) //
      vinogradovEmbeddedWideDifferenceSignature eY hY uv = l} ↪
    {uv : (Fin b → Fin Y) × (Fin b → Fin Y) //
      vinogradovWideDifferenceSignature hY
        (vinogradovRawDifference_le_fejerRadius Y b k) uv = l} where
  toFun uv := ⟨vinogradovMapTuplePair eY uv.1, uv.2⟩
  inj' := by
    intro u v huv
    apply Subtype.ext
    exact vinogradovMapTuplePair_injective eY
      (congrArg (fun z => z.1) huv)

theorem card_vinogradovEmbeddedWideDifferenceFiber_le_moment
    {Y₀ Y b k : ℕ} (eY : Fin Y₀ ↪ Fin Y) (hY : Y ≠ 0)
    (l : Fin k → Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius Y b k))) :
    Fintype.card {uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀) //
      vinogradovEmbeddedWideDifferenceSignature eY hY uv = l} ≤
      Fintype.card (VinogradovDiagonalSolution Y b k) := by
  calc
    _ ≤ Fintype.card {uv : (Fin b → Fin Y) × (Fin b → Fin Y) //
        vinogradovWideDifferenceSignature hY
          (vinogradovRawDifference_le_fejerRadius Y b k) uv = l} :=
      Fintype.card_le_of_embedding
        (vinogradovEmbeddedWideDifferenceFiberEmbedding eY hY l)
    _ ≤ Fintype.card (VinogradovDiagonalSolution Y b k) :=
      card_vinogradovWideDifferenceFiber_le_moment hY _ l

/-- First embedded grouping: restricting the summation interval changes
neither the Fejér majorant nor the full-box Vinogradov fibre cost. -/
theorem sum_vinogradovEmbeddedActualPolynomialMoment_le_smoothed
    {X₀ X Y₀ Y b k : ℕ} (eX : Fin X₀ ↪ Fin X) (eY : Fin Y₀ ↪ Fin Y)
    (hY : Y ≠ 0) (α : Fin k → ℝ) :
    (∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀),
      Complex.normSq (finitePhaseSum
        (vinogradovEmbeddedActualPolynomialPhase eX eY α uv)) ^ b) ≤
      Fintype.card (VinogradovDiagonalSolution Y b k) *
        ∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
            (vinogradovFejerRadius Y b k)),
          vinogradovFejerWeight hY l *
            Complex.normSq (finitePhaseSum
              (vinogradovEmbeddedFejerPolynomialPhase eX α l)) ^ b := by
  let sig := vinogradovEmbeddedWideDifferenceSignature (b := b) (k := k) eY hY
  let moment : (Fin k → Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius Y b k))) → ℝ := fun l =>
    Complex.normSq (finitePhaseSum
      (vinogradovEmbeddedFejerPolynomialPhase eX α l)) ^ b
  let weighted : (Fin k → Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius Y b k))) → ℝ := fun l =>
    vinogradovFejerWeight hY l * moment l
  have hweighted : ∀ l, 0 ≤ weighted l := by
    intro l
    exact mul_nonneg (vinogradovFejerWeight_nonneg hY l)
      (pow_nonneg (Complex.normSq_nonneg _) _)
  have hpoint : ∀ uv,
      Complex.normSq (finitePhaseSum
        (vinogradovEmbeddedActualPolynomialPhase eX eY α uv)) ^ b ≤
        weighted (sig uv) := by
    intro uv
    have hphase := vinogradovFejerPolynomialPhase_signature
      (X := X) hY α (vinogradovMapTuplePair eY uv)
    have hphaseEmbedded :
        vinogradovEmbeddedFejerPolynomialPhase eX α (sig uv) =
          vinogradovEmbeddedActualPolynomialPhase eX eY α uv := by
      funext n
      exact congrFun hphase (eX n)
    have hone := one_le_vinogradovFejerWeight_signature (k := k) hY
      (vinogradovMapTuplePair eY uv)
    unfold weighted moment
    rw [hphaseEmbedded]
    exact le_mul_of_one_le_left
      (pow_nonneg (Complex.normSq_nonneg _) _) hone
  calc
    _ ≤ ∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀), weighted (sig uv) :=
      Finset.sum_le_sum fun uv _ => hpoint uv
    _ ≤ Fintype.card (VinogradovDiagonalSolution Y b k) *
        ∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
          (vinogradovFejerRadius Y b k)), weighted l :=
      sum_comp_le_uniform_fiber_mul sig weighted hweighted _
        (card_vinogradovEmbeddedWideDifferenceFiber_le_moment eY hY)
    _ = Fintype.card (VinogradovDiagonalSolution Y b k) *
        ∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
            (vinogradovFejerRadius Y b k)),
          vinogradovFejerWeight hY l *
            Complex.normSq (finitePhaseSum
              (vinogradovEmbeddedFejerPolynomialPhase eX α l)) ^ b := by rfl

def vinogradovEmbeddedBoundedDifferenceSignature
    {X₀ X b k : ℕ} (eX : Fin X₀ ↪ Fin X) (hX : X ≠ 0) :
    ((Fin b → Fin X₀) × (Fin b → Fin X₀)) →
      (Fin k → Fin (vinogradovDifferenceBoxSize X b k)) :=
  fun uv => vinogradovBoundedDifferenceSignature hX
    (vinogradovMapTuplePair eX uv)

def vinogradovEmbeddedBoundedDifferenceFiberEmbedding
    {X₀ X b k : ℕ} (eX : Fin X₀ ↪ Fin X) (hX : X ≠ 0)
    (l : Fin k → Fin (vinogradovDifferenceBoxSize X b k)) :
    {uv : (Fin b → Fin X₀) × (Fin b → Fin X₀) //
      vinogradovEmbeddedBoundedDifferenceSignature eX hX uv = l} ↪
    {uv : (Fin b → Fin X) × (Fin b → Fin X) //
      vinogradovBoundedDifferenceSignature hX uv = l} where
  toFun uv := ⟨vinogradovMapTuplePair eX uv.1, uv.2⟩
  inj' := by
    intro u v huv
    apply Subtype.ext
    exact vinogradovMapTuplePair_injective eX
      (congrArg (fun z => z.1) huv)

theorem card_vinogradovEmbeddedBoundedDifferenceFiber_le_moment
    {X₀ X b k : ℕ} (eX : Fin X₀ ↪ Fin X) (hX : X ≠ 0)
    (l : Fin k → Fin (vinogradovDifferenceBoxSize X b k)) :
    Fintype.card {uv : (Fin b → Fin X₀) × (Fin b → Fin X₀) //
      vinogradovEmbeddedBoundedDifferenceSignature eX hX uv = l} ≤
      Fintype.card (VinogradovDiagonalSolution X b k) := by
  calc
    _ ≤ Fintype.card {uv : (Fin b → Fin X) × (Fin b → Fin X) //
        vinogradovBoundedDifferenceSignature hX uv = l} :=
      Fintype.card_le_of_embedding
        (vinogradovEmbeddedBoundedDifferenceFiberEmbedding eX hX l)
    _ ≤ Fintype.card (VinogradovDiagonalSolution X b k) :=
      card_vinogradovBoundedDifferenceFiber_le_moment hX l

theorem sum_vinogradovEmbeddedFejerWeight_mul_polynomialMoment_eq
    {X₀ X Y b k : ℕ} (eX : Fin X₀ ↪ Fin X) (hX : X ≠ 0) (hY : Y ≠ 0)
    (α : Fin k → ℝ) :
    (∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
        (vinogradovFejerRadius Y b k)),
      vinogradovFejerWeight hY l *
        Complex.normSq (finitePhaseSum
          (vinogradovEmbeddedFejerPolynomialPhase eX α l)) ^ b) =
      ∑ uv : (Fin b → Fin X₀) × (Fin b → Fin X₀),
        vinogradovRectangularKernelWeight (Y := Y) α
          (vinogradovEmbeddedBoundedDifferenceSignature eX hX uv) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, Complex.ofReal_pow]
  simp_rw [finitePhaseMoment_expansion]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro uv _
  have hphase : ∀ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius Y b k)),
      (∑ i : Fin b, vinogradovEmbeddedFejerPolynomialPhase eX α l (uv.1 i)) -
          ∑ i : Fin b, vinogradovEmbeddedFejerPolynomialPhase eX α l (uv.2 i) =
        ∑ j : Fin k, vinogradovFejerCenteredCoordinate (l j) *
          (α j *
            ((∑ i : Fin b, ((eX (uv.1 i)).val : ℝ) ^ (j.val + 1)) -
              ∑ i : Fin b, ((eX (uv.2 i)).val : ℝ) ^ (j.val + 1))) := by
    intro l
    unfold vinogradovEmbeddedFejerPolynomialPhase vinogradovFejerPolynomialPhase
    unfold finiteVinogradovPolynomialPhase
    rw [show (∑ i : Fin b, ∑ j : Fin k,
        α j * vinogradovFejerCenteredCoordinate (l j) *
          ((eX (uv.1 i)).val : ℝ) ^ (j.val + 1)) =
        ∑ j : Fin k, ∑ i : Fin b,
          α j * vinogradovFejerCenteredCoordinate (l j) *
            ((eX (uv.1 i)).val : ℝ) ^ (j.val + 1) from Finset.sum_comm]
    rw [show (∑ i : Fin b, ∑ j : Fin k,
        α j * vinogradovFejerCenteredCoordinate (l j) *
          ((eX (uv.2 i)).val : ℝ) ^ (j.val + 1)) =
        ∑ j : Fin k, ∑ i : Fin b,
          α j * vinogradovFejerCenteredCoordinate (l j) *
            ((eX (uv.2 i)).val : ℝ) ^ (j.val + 1) from Finset.sum_comm]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  simp_rw [hphase]
  rw [sum_vinogradovFejerWeight_mul_phase hY]
  rw [← Complex.ofReal_prod]
  exact congrArg Complex.ofReal
    (vinogradovRectangularKernelWeight_signature hX α
      (vinogradovMapTuplePair eX uv)).symm

/-- Second embedded grouping.  Injectivity of the interval embedding is
the exact reason restriction cannot increase any power-difference fibre. -/
theorem sum_vinogradovEmbeddedFejerWeight_mul_polynomialMoment_le
    {X₀ X Y b k : ℕ} (eX : Fin X₀ ↪ Fin X) (hX : X ≠ 0) (hY : Y ≠ 0)
    (α : Fin k → ℝ) :
    (∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
        (vinogradovFejerRadius Y b k)),
      vinogradovFejerWeight hY l *
        Complex.normSq (finitePhaseSum
          (vinogradovEmbeddedFejerPolynomialPhase eX α l)) ^ b) ≤
      Fintype.card (VinogradovDiagonalSolution X b k) *
        ∑ g : Fin k → Fin (vinogradovDifferenceBoxSize X b k),
          vinogradovRectangularKernelWeight (Y := Y) α g := by
  rw [sum_vinogradovEmbeddedFejerWeight_mul_polynomialMoment_eq eX hX hY α]
  exact sum_comp_le_uniform_fiber_mul
    (vinogradovEmbeddedBoundedDifferenceSignature eX hX)
    (vinogradovRectangularKernelWeight (Y := Y) α)
    (vinogradovRectangularKernelWeight_nonneg α)
    (Fintype.card (VinogradovDiagonalSolution X b k))
    (card_vinogradovEmbeddedBoundedDifferenceFiber_le_moment eX hX)

theorem sum_vinogradovEmbeddedActualPolynomialMoment_le_coordinateProduct
    {X₀ X Y₀ Y b k : ℕ} (eX : Fin X₀ ↪ Fin X) (eY : Fin Y₀ ↪ Fin Y)
    (hX : X ≠ 0) (hY : Y ≠ 0) (α : Fin k → ℝ) :
    (∑ uv : (Fin b → Fin Y₀) × (Fin b → Fin Y₀),
      Complex.normSq (finitePhaseSum
        (vinogradovEmbeddedActualPolynomialPhase eX eY α uv)) ^ b) ≤
      (Fintype.card (VinogradovDiagonalSolution Y b k) *
        Fintype.card (VinogradovDiagonalSolution X b k)) *
          ∏ j : Fin k,
            ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
              vinogradovCoordinateKernelWeight (Y := Y) α j g := by
  calc
    _ ≤ Fintype.card (VinogradovDiagonalSolution Y b k) *
        ∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize
            (vinogradovFejerRadius Y b k)),
          vinogradovFejerWeight hY l *
            Complex.normSq (finitePhaseSum
              (vinogradovEmbeddedFejerPolynomialPhase eX α l)) ^ b :=
      sum_vinogradovEmbeddedActualPolynomialMoment_le_smoothed eX eY hY α
    _ ≤ Fintype.card (VinogradovDiagonalSolution Y b k) *
        (Fintype.card (VinogradovDiagonalSolution X b k) *
          ∑ g : Fin k → Fin (vinogradovDifferenceBoxSize X b k),
            vinogradovRectangularKernelWeight (Y := Y) α g) := by
      gcongr
      exact sum_vinogradovEmbeddedFejerWeight_mul_polynomialMoment_le
        eX hX hY α
    _ = (Fintype.card (VinogradovDiagonalSolution Y b k) *
        Fintype.card (VinogradovDiagonalSolution X b k)) *
          ∏ j : Fin k,
            ∑ g : Fin (vinogradovDifferenceBoxSize X b k),
              vinogradovCoordinateKernelWeight (Y := Y) α j g := by
      rw [sum_vinogradovRectangularKernelWeight_eq_prod]
      ring

end

end RHTower.Sieve
