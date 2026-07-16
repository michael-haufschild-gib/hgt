import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolCoefficientFlatness
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Abelian rigidity of a flat matrix principal-symbol tower

The determinant horizon hides a stronger constraint.  Fix a law direction whose symbols are
invertible.  In the coefficient convention forced by iterated derivations, flatness makes the
symbols at every layer commute after normalization by that direction.  Thus a flat finite-rank
principal tower carries only a commutative normalized observable algebra.  Noncommutativity is an
exact obstruction to flatness, hence forces nonzero principal curvature somewhere.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K g ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The coefficient symbol at layer `n`, normalized on the left by a regular reference law. -/
def coefficientNormalizedMatrixPrincipalSymbol
    (symbol : ℕ → g → Matrix ι ι K) (e : g) (n : ℕ) (A : g) :
    Matrix ι ι K :=
  (symbol n e)⁻¹ * symbol n A

/-- One flat square with the reference law transports a symbol to the next layer. -/
theorem matrixCoefficientPrincipalSymbol_transport
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A : g) :
    symbol (n + 1) A =
      coefficientNormalizedMatrixPrincipalSymbol symbol e n A * symbol (n + 1) e := by
  have hunit : IsUnit (symbol n e).det := isUnit_iff_ne_zero.mpr (he n)
  unfold coefficientNormalizedMatrixPrincipalSymbol
  calc
    symbol (n + 1) A =
        (symbol n e)⁻¹ * (symbol n e * symbol (n + 1) A) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
    _ = (symbol n e)⁻¹ * (symbol n A * symbol (n + 1) e) := by
      rw [hflat n A e]
    _ = ((symbol n e)⁻¹ * symbol n A) * symbol (n + 1) e := by
      rw [Matrix.mul_assoc]

/-- Normalized coefficient symbols are transported between layers by conjugation. -/
theorem coefficientNormalizedMatrixPrincipalSymbol_succ_eq_conj
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A : g) :
    coefficientNormalizedMatrixPrincipalSymbol symbol e (n + 1) A =
      (symbol (n + 1) e)⁻¹ *
        coefficientNormalizedMatrixPrincipalSymbol symbol e n A *
          symbol (n + 1) e := by
  unfold coefficientNormalizedMatrixPrincipalSymbol
  rw [matrixCoefficientPrincipalSymbol_transport symbol hflat e he n A]
  simp only [coefficientNormalizedMatrixPrincipalSymbol, Matrix.mul_assoc]

/-- **Abelian rigidity.**  At every layer, all normalized symbols of a flat coefficient tower
commute pairwise. -/
theorem coefficientNormalizedMatrixPrincipalSymbol_commute
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A B : g) :
    Commute
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n A)
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n B) := by
  have hnextUnit : IsUnit (symbol (n + 1) e) :=
    (symbol (n + 1) e).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr (he (n + 1)))
  have hcross := hflat n A B
  rw [matrixCoefficientPrincipalSymbol_transport symbol hflat e he n A,
    matrixCoefficientPrincipalSymbol_transport symbol hflat e he n B] at hcross
  have hcancel :
      symbol n B * coefficientNormalizedMatrixPrincipalSymbol symbol e n A =
        symbol n A * coefficientNormalizedMatrixPrincipalSymbol symbol e n B := by
    apply hnextUnit.mul_right_cancel
    simpa only [Matrix.mul_assoc] using hcross
  have hleft := congrArg
    (fun M : Matrix ι ι K ↦ (symbol n e)⁻¹ * M) hcancel
  show coefficientNormalizedMatrixPrincipalSymbol symbol e n A *
      coefficientNormalizedMatrixPrincipalSymbol symbol e n B =
    coefficientNormalizedMatrixPrincipalSymbol symbol e n B *
      coefficientNormalizedMatrixPrincipalSymbol symbol e n A
  simpa only [coefficientNormalizedMatrixPrincipalSymbol, Matrix.mul_assoc] using hleft.symm

/-- The whole normalized law family is pairwise commuting at every layer. -/
theorem coefficientNormalizedMatrixPrincipalSymbol_pairwise_commute
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) :
    Pairwise (fun A B ↦ Commute
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n A)
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n B)) := by
  intro A B _
  exact coefficientNormalizedMatrixPrincipalSymbol_commute symbol hflat e he n A B

/-- **Noncommutativity forces curvature.**  A noncommuting pair of normalized observables rules
out flatness of the complete principal-symbol tower. -/
theorem not_matrixCoefficientPrincipalSymbolFlat_of_normalized_not_commute
    (symbol : ℕ → g → Matrix ι ι K)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A B : g)
    (hnc : ¬ Commute
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n A)
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n B)) :
    ¬ MatrixCoefficientPrincipalSymbolFlat symbol := by
  intro hflat
  exact hnc <|
    coefficientNormalizedMatrixPrincipalSymbol_commute symbol hflat e he n A B

/-- In curvature language, a noncommuting normalized pair forces a nonzero coefficient curvature
at some layer and pair of law directions. -/
theorem exists_matrixCoefficientPrincipalCurvature_ne_zero_of_normalized_not_commute
    (symbol : ℕ → g → Matrix ι ι K)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A B : g)
    (hnc : ¬ Commute
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n A)
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n B)) :
    ∃ m C D, matrixCoefficientPrincipalCurvature symbol m C D ≠ 0 := by
  have hnflat := not_matrixCoefficientPrincipalSymbolFlat_of_normalized_not_commute
    symbol e he n A B hnc
  rw [matrixCoefficientPrincipalSymbolFlat_iff_curvature_zero] at hnflat
  push Not at hnflat
  exact hnflat

/-! ## Classification by a static abelian family and a gauge sequence -/

/-- The successive conjugates of one static matrix family by a gauge sequence. -/
def abelianGaugeOrbit
    (base : g → Matrix ι ι K) (gauge : ℕ → Matrix ι ι K) :
    ℕ → g → Matrix ι ι K
  | 0, A => base A
  | n + 1, A => (gauge (n + 1))⁻¹ * abelianGaugeOrbit base gauge n A * gauge (n + 1)

/-- The principal-symbol tower generated by a static family and a sequence of changes of frame. -/
def abelianGaugePrincipalSymbol
    (base : g → Matrix ι ι K) (gauge : ℕ → Matrix ι ι K) :
    ℕ → g → Matrix ι ι K
  | 0, A => gauge 0 * base A
  | n + 1, A => abelianGaugeOrbit base gauge n A * gauge (n + 1)

/-- Conjugation by an invertible gauge preserves commutation throughout the gauge orbit. -/
theorem abelianGaugeOrbit_commute
    (base : g → Matrix ι ι K) (gauge : ℕ → Matrix ι ι K)
    (hgauge : ∀ n, (gauge n).det ≠ 0)
    (hbase : ∀ A B, Commute (base A) (base B)) :
    ∀ n A B, Commute
      (abelianGaugeOrbit base gauge n A)
      (abelianGaugeOrbit base gauge n B) := by
  intro n
  induction n with
  | zero =>
      intro A B
      exact hbase A B
  | succ n ih =>
      intro A B
      have hunit : IsUnit (gauge (n + 1)).det :=
        isUnit_iff_ne_zero.mpr (hgauge (n + 1))
      show ((gauge (n + 1))⁻¹ * abelianGaugeOrbit base gauge n A * gauge (n + 1)) *
          ((gauge (n + 1))⁻¹ * abelianGaugeOrbit base gauge n B * gauge (n + 1)) =
        ((gauge (n + 1))⁻¹ * abelianGaugeOrbit base gauge n B * gauge (n + 1)) *
          ((gauge (n + 1))⁻¹ * abelianGaugeOrbit base gauge n A * gauge (n + 1))
      calc
        _ = (gauge (n + 1))⁻¹ * abelianGaugeOrbit base gauge n A *
              (gauge (n + 1) * (gauge (n + 1))⁻¹) *
                abelianGaugeOrbit base gauge n B * gauge (n + 1) := by
          noncomm_ring
        _ = (gauge (n + 1))⁻¹ * abelianGaugeOrbit base gauge n A *
              1 * abelianGaugeOrbit base gauge n B * gauge (n + 1) := by
          rw [Matrix.mul_nonsing_inv _ hunit]
        _ = (gauge (n + 1))⁻¹ *
              (abelianGaugeOrbit base gauge n A *
                abelianGaugeOrbit base gauge n B) * gauge (n + 1) := by
          noncomm_ring
        _ = (gauge (n + 1))⁻¹ *
              (abelianGaugeOrbit base gauge n B *
                abelianGaugeOrbit base gauge n A) * gauge (n + 1) := by
          rw [(ih A B).eq]
        _ = _ := by
          rw [show (gauge (n + 1))⁻¹ *
                (abelianGaugeOrbit base gauge n B *
                  abelianGaugeOrbit base gauge n A) * gauge (n + 1) =
              (gauge (n + 1))⁻¹ * abelianGaugeOrbit base gauge n B *
                1 * abelianGaugeOrbit base gauge n A * gauge (n + 1) by
            noncomm_ring]
          rw [← Matrix.mul_nonsing_inv _ hunit]
          noncomm_ring

/-- Conversely, a static commuting family and invertible changes of frame generate a flat
coefficient principal-symbol tower. -/
theorem abelianGaugePrincipalSymbol_flat
    (base : g → Matrix ι ι K) (gauge : ℕ → Matrix ι ι K)
    (hgauge : ∀ n, (gauge n).det ≠ 0)
    (hbase : ∀ A B, Commute (base A) (base B)) :
    MatrixCoefficientPrincipalSymbolFlat
      (abelianGaugePrincipalSymbol base gauge) := by
  intro n A B
  cases n with
  | zero =>
      change (gauge 0 * base B) * (base A * gauge 1) =
        (gauge 0 * base A) * (base B * gauge 1)
      simpa only [Matrix.mul_assoc] using congrArg
        (fun M : Matrix ι ι K ↦ gauge 0 * M * gauge 1) (hbase A B).eq.symm
  | succ n =>
      have hunit : IsUnit (gauge (n + 1)).det :=
        isUnit_iff_ne_zero.mpr (hgauge (n + 1))
      simp only [abelianGaugePrincipalSymbol, abelianGaugeOrbit]
      calc
        _ = abelianGaugeOrbit base gauge n B * gauge (n + 1) *
              (gauge (n + 1))⁻¹ * abelianGaugeOrbit base gauge n A *
                gauge (n + 1) * gauge (n + 1 + 1) := by
          noncomm_ring
        _ = abelianGaugeOrbit base gauge n B * 1 *
              abelianGaugeOrbit base gauge n A * gauge (n + 1) *
                gauge (n + 1 + 1) := by
          rw [Matrix.mul_nonsing_inv_cancel_right (gauge (n + 1))
            (abelianGaugeOrbit base gauge n B) hunit]
          noncomm_ring
        _ = (abelianGaugeOrbit base gauge n B *
              abelianGaugeOrbit base gauge n A) * gauge (n + 1) *
                gauge (n + 1 + 1) := by
          noncomm_ring
        _ = (abelianGaugeOrbit base gauge n A *
              abelianGaugeOrbit base gauge n B) * gauge (n + 1) *
                gauge (n + 1 + 1) := by
          rw [(abelianGaugeOrbit_commute base gauge hgauge hbase n A B).eq]
        _ = _ := by
          rw [show (abelianGaugeOrbit base gauge n A *
                abelianGaugeOrbit base gauge n B) * gauge (n + 1) *
                  gauge (n + 1 + 1) =
              abelianGaugeOrbit base gauge n A * gauge (n + 1) *
                (gauge (n + 1))⁻¹ * abelianGaugeOrbit base gauge n B *
                  gauge (n + 1) * gauge (n + 1 + 1) by
            rw [Matrix.mul_nonsing_inv_cancel_right (gauge (n + 1))
              (abelianGaugeOrbit base gauge n A) hunit]]
          noncomm_ring

/-- For a flat tower, its gauge orbit reconstructed from layer zero is exactly its family of
normalized symbols at every layer. -/
theorem abelianGaugeOrbit_eq_normalized_of_flat
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0) :
    ∀ n A,
      abelianGaugeOrbit
          (coefficientNormalizedMatrixPrincipalSymbol symbol e 0)
          (fun m ↦ symbol m e) n A =
        coefficientNormalizedMatrixPrincipalSymbol symbol e n A := by
  intro n
  induction n with
  | zero => intro A; rfl
  | succ n ih =>
      intro A
      change (symbol (n + 1) e)⁻¹ *
          abelianGaugeOrbit
            (coefficientNormalizedMatrixPrincipalSymbol symbol e 0)
            (fun m ↦ symbol m e) n A * symbol (n + 1) e =
        coefficientNormalizedMatrixPrincipalSymbol symbol e (n + 1) A
      rw [ih A]
      exact (coefficientNormalizedMatrixPrincipalSymbol_succ_eq_conj
        symbol hflat e he n A).symm

/-- A regular flat tower is recovered exactly from its static normalized layer-zero family and
its symbols in the reference direction. -/
theorem abelianGaugePrincipalSymbol_reconstruct
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0) :
    abelianGaugePrincipalSymbol
        (coefficientNormalizedMatrixPrincipalSymbol symbol e 0)
        (fun n ↦ symbol n e) = symbol := by
  funext n A
  cases n with
  | zero =>
      change symbol 0 e * ((symbol 0 e)⁻¹ * symbol 0 A) = symbol 0 A
      rw [Matrix.mul_nonsing_inv_cancel_left _ _
        (isUnit_iff_ne_zero.mpr (he 0))]
  | succ n =>
      change abelianGaugeOrbit
          (coefficientNormalizedMatrixPrincipalSymbol symbol e 0)
          (fun m ↦ symbol m e) n A * symbol (n + 1) e = symbol (n + 1) A
      rw [abelianGaugeOrbit_eq_normalized_of_flat symbol hflat e he n A]
      exact (matrixCoefficientPrincipalSymbol_transport symbol hflat e he n A).symm

/-- The reference direction of a gauge orbit of the identity is the identity at every layer. -/
theorem abelianGaugeOrbit_reference_eq_one
    (base : g → Matrix ι ι K) (gauge : ℕ → Matrix ι ι K)
    (e : g) (hbasee : base e = 1)
    (hgauge : ∀ n, (gauge n).det ≠ 0) :
    ∀ n, abelianGaugeOrbit base gauge n e = 1 := by
  intro n
  induction n with
  | zero => exact hbasee
  | succ n ih =>
      change (gauge (n + 1))⁻¹ * abelianGaugeOrbit base gauge n e * gauge (n + 1) = 1
      rw [ih, Matrix.mul_one, Matrix.nonsing_inv_mul _
        (isUnit_iff_ne_zero.mpr (hgauge (n + 1)))]

/-- In the generated tower, the chosen reference law reads off the gauge sequence itself. -/
theorem abelianGaugePrincipalSymbol_reference
    (base : g → Matrix ι ι K) (gauge : ℕ → Matrix ι ι K)
    (e : g) (hbasee : base e = 1)
    (hgauge : ∀ n, (gauge n).det ≠ 0) :
    ∀ n, abelianGaugePrincipalSymbol base gauge n e = gauge n := by
  intro n
  cases n with
  | zero => simp [abelianGaugePrincipalSymbol, hbasee]
  | succ n =>
      change abelianGaugeOrbit base gauge n e * gauge (n + 1) = gauge (n + 1)
      rw [abelianGaugeOrbit_reference_eq_one base gauge e hbasee hgauge n, Matrix.one_mul]

/-- **Complete regular-flat classification.**  A coefficient principal-symbol tower is flat and
has one everywhere-regular law if and only if it is obtained from a single commuting matrix family
by invertible changes of frame.  Thus every regular exact-flat finite-rank tower is static and
abelian up to gauge. -/
theorem regular_matrixCoefficientPrincipalSymbolFlat_iff_abelianGauge
    (symbol : ℕ → g → Matrix ι ι K) :
    (MatrixCoefficientPrincipalSymbolFlat symbol ∧
        ∃ e : g, ∀ n, (symbol n e).det ≠ 0) ↔
      ∃ (e : g) (base : g → Matrix ι ι K) (gauge : ℕ → Matrix ι ι K),
        base e = 1 ∧
        (∀ A B, Commute (base A) (base B)) ∧
        (∀ n, (gauge n).det ≠ 0) ∧
        symbol = abelianGaugePrincipalSymbol base gauge := by
  constructor
  · rintro ⟨hflat, e, he⟩
    let base := coefficientNormalizedMatrixPrincipalSymbol symbol e 0
    let gauge : ℕ → Matrix ι ι K := fun n ↦ symbol n e
    refine ⟨e, base, gauge, ?_, ?_, he, ?_⟩
    · change (symbol 0 e)⁻¹ * symbol 0 e = 1
      exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (he 0))
    · intro A B
      exact coefficientNormalizedMatrixPrincipalSymbol_commute symbol hflat e he 0 A B
    · exact (abelianGaugePrincipalSymbol_reconstruct symbol hflat e he).symm
  · rintro ⟨e, base, gauge, hbasee, hcomm, hgauge, rfl⟩
    exact ⟨abelianGaugePrincipalSymbol_flat base gauge hgauge hcomm,
      e, fun n ↦ by
        rw [abelianGaugePrincipalSymbol_reference base gauge e hbasee hgauge n]
        exact hgauge n⟩

end

end GaloisForLFunctions.HTGeometry
