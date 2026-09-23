import GaloisForLFunctions.HTGeometry.GomesFockSpectralGauge

/-!
Internal spectral-window tensors reconstructed from all vector-state measures.
This applies the tensor-reconstruction and internal-space viewpoints in Gomes,
arXiv:2607.24901v1 and arXiv:2404.10461, beyond the corpus's singleton atom matrices.
Every window has a positive matrix bounded by the identity, and its quadratic
observations are exactly the original spectral masses. The full window is the
identity and singleton windows recover the existing atom matrices.
-/
open scoped Matrix BigOperators ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- Real spectral mass in an arbitrary window for an internal observing vector. -/
def gomesFockWindowMass {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) : ℝ :=
  (gomesFockSpectralMeasure B x S).toReal

/-- Every spectral-window observation is nonnegative. -/
theorem gomesFockWindowMass_nonneg {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) :
    0 ≤ gomesFockWindowMass B S x := ENNReal.toReal_nonneg

/-- Spectral-window masses carry exactly squared scalar amplitude. -/
theorem gomesFockWindowMass_smul {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (c : ℂ) (x : Fin (d+1) → ℂ) :
    gomesFockWindowMass B S (c • x) = Complex.normSq c*gomesFockWindowMass B S x := by
  unfold gomesFockWindowMass
  rw [gomesFockSpectralMeasure_smul]
  change (ENNReal.ofReal (Complex.normSq c)*gomesFockSpectralMeasure B x S).toReal = _
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Complex.normSq_nonneg c)]

/-- Every spectral window obeys the complex quadratic parallelogram law. -/
theorem gomesFockWindowMass_parallelogram {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x y : Fin (d+1) → ℂ) :
    gomesFockWindowMass B S (x+y)+gomesFockWindowMass B S (x-y) =
      2*gomesFockWindowMass B S x+2*gomesFockWindowMass B S y := by
  have h := congrArg (fun μ : Measure ℝ => (μ S).toReal)
    (freeFockVectorSpectralMeasure_parallelogram _ (gomesCompletedFockGenerators_hermitian B)
      (gomesCompletedFockGenerators_commonKernel B) x y)
  change ((gomesFockSpectralMeasure B (x+y) S+gomesFockSpectralMeasure B (x-y) S).toReal) =
    (ENNReal.ofReal 2*gomesFockSpectralMeasure B x S+
      ENNReal.ofReal 2*gomesFockSpectralMeasure B y S).toReal at h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add
      (ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)))
      (ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))),
    ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 2)] at h
  exact h

/-- A spectral-window observation never exceeds the initial source mass. -/
theorem gomesFockWindowMass_le_total {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) :
    gomesFockWindowMass B S x ≤ freeFockVectorMoment (gomesCompletedFockGenerators B) x 0 := by
  rw [← gomesFockSpectralMeasure_totalMass]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ S))

/-- The existing finite-dimensional bound controls every window's quadratic observation. -/
theorem gomesFockWindowMass_bound {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) :
    gomesFockWindowMass B S x ≤ (Fintype.card (Fin (d+1)) : ℝ)*‖x‖^(2 : ℕ) := by
  apply (gomesFockWindowMass_le_total B S x).trans
  rw [freeFockVectorMoment_zero]
  exact sum_normSq_le_card_mul_norm_sq x

/-- Matrix of a spectral window reconstructed by the existing complex polarization. -/
def gomesFockWindowMatrix {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  fun i j => complexQuadraticPolarization (gomesFockWindowMass B S)
    (freeFockInternalBasis i) (freeFockInternalBasis j)

/-- Reconstructed spectral-window tensors are Hermitian. -/
theorem gomesFockWindowMatrix_adjoint {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    (gomesFockWindowMatrix B S)ᴴ = gomesFockWindowMatrix B S := by
  ext i j
  exact (complexQuadraticPolarization_conj_symm (gomesFockWindowMass B S)
    (gomesFockWindowMass_smul B S) (gomesFockWindowMass_parallelogram B S)
    (freeFockInternalBasis j) (freeFockInternalBasis i)).symm

/-- Every vector quadratic observation of the window tensor is exactly its original spectral mass. -/
theorem gomesFockWindowMatrix_quadratic {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) :
    star x ⬝ᵥ (gomesFockWindowMatrix B S*ᵥx) = (gomesFockWindowMass B S x : ℂ) := by
  let q := gomesFockWindowMass B S
  have hs := gomesFockWindowMass_smul B S
  have hp := gomesFockWindowMass_parallelogram B S
  have hn := gomesFockWindowMass_nonneg B S
  have hc : 0 ≤ (Fintype.card (Fin (d+1)) : ℝ) := Nat.cast_nonneg _
  have hb := gomesFockWindowMass_bound B S
  change (∑ i, star (x i)*∑ j, complexQuadraticPolarization q
    (freeFockInternalBasis i) (freeFockInternalBasis j)*x j) = (q x : ℂ)
  calc
    (∑ i, star (x i)*∑ j, complexQuadraticPolarization q
        (freeFockInternalBasis i) (freeFockInternalBasis j)*x j) =
        ∑ i, ∑ j, star (x i)*x j*complexQuadraticPolarization q
          (freeFockInternalBasis i) (freeFockInternalBasis j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, ∑ j, complexQuadraticPolarization q
        (x i • freeFockInternalBasis i) (x j • freeFockInternalBasis j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [complexQuadraticPolarization_smul_left q hs hp hn _ hc hb,
        complexQuadraticPolarization_smul_right q hs hp hn _ hc hb]
      ring
    _ = ∑ i, complexQuadraticPolarization q (x i • freeFockInternalBasis i)
        (∑ j, x j • freeFockInternalBasis j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [complexQuadraticPolarization_sum_right q hs hp hn _ hc hb]
    _ = complexQuadraticPolarization q (∑ i, x i • freeFockInternalBasis i)
        (∑ j, x j • freeFockInternalBasis j) := by
      rw [complexQuadraticPolarization_sum_left q hs hp hn _ hc hb]
    _ = complexQuadraticPolarization q x x := by rw [sum_smul_freeFockInternalBasis]
    _ = (q x : ℂ) := complexQuadraticPolarization_self q hs hp x

/-- Every spectral-window matrix is positive semidefinite. -/
theorem gomesFockWindowMatrix_posSemidef {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    (gomesFockWindowMatrix B S).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact gomesFockWindowMatrix_adjoint B S
  · intro x
    rw [gomesFockWindowMatrix_quadratic]
    exact Complex.zero_le_real.mpr (gomesFockWindowMass_nonneg B S x)

/-- The full spectral-window tensor is the identity internal metric. -/
theorem gomesFockWindowMatrix_univ {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    gomesFockWindowMatrix B Set.univ = 1 := by
  apply matrix_eq_of_quadraticForm_eq
  intro x
  rw [gomesFockWindowMatrix_quadratic]
  change ((gomesFockSpectralMeasure B x Set.univ).toReal : ℂ) = _
  rw [gomesFockSpectralMeasure_totalMass,gomesFockVector_mass_quadratic]
  simp

/-- The empty spectral window has zero observation tensor. -/
theorem gomesFockWindowMatrix_empty {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    gomesFockWindowMatrix B ∅ = 0 := by
  apply matrix_eq_of_quadraticForm_eq
  intro x
  rw [gomesFockWindowMatrix_quadratic]
  simp [gomesFockWindowMass]

/-- Singleton windows recover the corpus's existing matrix atom weights exactly. -/
theorem gomesFockWindowMatrix_singleton {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (a : ℝ) :
    gomesFockWindowMatrix B {a} = freeFockMatrixAtomMass (gomesCompletedFockGenerators B)
      (gomesCompletedFockGenerators_hermitian B) (gomesCompletedFockGenerators_commonKernel B) a := rfl

/-- Every spectral-window tensor is bounded above by the identity in the Hermitian order. -/
theorem gomesFockWindowMatrix_complement_posSemidef {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    (1-gomesFockWindowMatrix B S).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (1-gomesFockWindowMatrix B S)ᴴ = 1-gomesFockWindowMatrix B S
    simp [Matrix.conjTranspose_sub,gomesFockWindowMatrix_adjoint]
  · intro x
    rw [Matrix.sub_mulVec,dotProduct_sub,Matrix.one_mulVec,gomesFockWindowMatrix_quadratic,
      ← gomesFockVector_mass_quadratic (gomesCompletedFockGenerators B) x,← Complex.ofReal_sub]
    exact Complex.zero_le_real.mpr (sub_nonneg.mpr (gomesFockWindowMass_le_total B S x))

end GaloisForLFunctions.HTGeometry
