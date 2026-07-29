import GaloisForLFunctions.HilbertMetric.GradedPartition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Sigma.Order
import Mathlib.Order.PiLex
import Mathlib.Topology.Instances.Matrix

/-!
# Gaussian Fock determinant laws for finite Hilbert metrics

This module constructs the ordered-tensor Fock expansion of the exponential inner-product
kernel.  Finite Pluecker partitions supply nonnegative graded coefficients; Taylor convergence
and determinant continuity then lift their multiplicative midpoint inequality to every finite
configuration in an arbitrary real Hilbert space.
-/

open scoped BigOperators RealInnerProductSpace

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

section GaussianFockApplication

open Filter

/-! ### Ordered-tensor Fock truncations

The ordered-tensor indexing below avoids multi-index normalization choices.  In tensor degree
`k`, summing over all maps `Fin k → Fin d` expands the `k`-th power of the Euclidean dot product.
The factorial weight then gives the Taylor truncations of the exponential inner-product kernel.
-/

/-- Ordered tensor words of degree at most `m`, equipped with a canonical lexicographic order. -/
abbrev orderedTensorFeature (d m : ℕ) :=
  Lex (Σ k : Fin (m + 1), Lex (Fin k.1 → Fin d))

/-- The coordinate monomial carried by one ordered tensor word. -/
def orderedTensorMonomial {n d m : ℕ} (y : Fin n → Fin d → ℝ)
    (i : Fin n) (q : orderedTensorFeature d m) : ℝ :=
  ∏ r, y i (ofLex (ofLex q).2 r)

/-- Tensor degree of an ordered Fock feature. -/
def orderedTensorDegree {d m : ℕ} (q : orderedTensorFeature d m) : ℕ :=
  (ofLex q).1.1

/-- Exponential-series weight `2^k / k!` in tensor degree `k`. -/
def orderedTensorWeight {d m : ℕ} (q : orderedTensorFeature d m) : ℝ :=
  (2 : ℝ) ^ orderedTensorDegree q / Nat.factorial (orderedTensorDegree q)

/-- A degree-scaled ordered-tensor Fock row. -/
def orderedTensorFockRow {n d m : ℕ} (y : Fin n → Fin d → ℝ) (r : ℝ)
    (i : Fin n) (q : orderedTensorFeature d m) : ℝ :=
  scaledFeatureRows (orderedTensorMonomial y) orderedTensorWeight
    orderedTensorDegree r i q

/-- The Gram matrix of the degree-`m` ordered-tensor Fock truncation. -/
def orderedTensorFockGram {n d : ℕ} (y : Fin n → Fin d → ℝ) (m : ℕ) (r : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  standardFeatureGram (fun i (q : orderedTensorFeature d m) =>
    orderedTensorFockRow y r i q)

/-- The Taylor polynomial of the real exponential through degree `m`. -/
def truncatedExpSeries (z : ℝ) (m : ℕ) : ℝ :=
  ∑ k : Fin (m + 1), z ^ k.1 / Nat.factorial k.1

/-- The ordinary coordinate dot product of two rows. -/
def coordinateDot {n d : ℕ} (y : Fin n → Fin d → ℝ) (i j : Fin n) : ℝ :=
  ∑ s, y i s * y j s

/-- Entrywise Taylor truncation of the exponential inner-product matrix. -/
def truncatedExponentialInnerMatrix {n d : ℕ} (y : Fin n → Fin d → ℝ)
    (m : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => truncatedExpSeries (2 * t * coordinateDot y i j) m

/-- The exact exponential inner-product matrix of a finite Euclidean configuration. -/
def coordinateExponentialInnerMatrix {n d : ℕ} (y : Fin n → Fin d → ℝ)
    (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp (2 * t * coordinateDot y i j)

theorem orderedTensorWeight_nonneg {d m : ℕ} (q : orderedTensorFeature d m) :
    0 ≤ orderedTensorWeight q := by
  exact div_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)

/-- A sum over ordered tensor features separates first by degree and then by tensor word. -/
theorem sum_orderedTensorFeature {d m : ℕ} (f : orderedTensorFeature d m → ℝ) :
    (∑ q, f q) =
      ∑ k : Fin (m + 1), ∑ q : Fin k.1 → Fin d,
        f (toLex ⟨k, toLex q⟩) := by
  rw [← (toLex :
    (Σ k : Fin (m + 1), Lex (Fin k.1 → Fin d)) ≃
      orderedTensorFeature d m).sum_comp]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  exact ((toLex : (Fin k.1 → Fin d) ≃ Lex (Fin k.1 → Fin d)).sum_comp
    (fun q => f (toLex ⟨k, q⟩))).symm

/-- Ordered tensor words expand powers of the coordinate dot product. -/
theorem sum_orderedTensorMonomial_mul {n d m : ℕ} (y : Fin n → Fin d → ℝ)
    (i j : Fin n) (k : Fin (m + 1)) :
    (∑ q : Fin k.1 → Fin d,
        orderedTensorMonomial y i (toLex ⟨k, toLex q⟩) *
          orderedTensorMonomial y j (toLex ⟨k, toLex q⟩)) =
      coordinateDot y i j ^ k.1 := by
  unfold coordinateDot
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro q _
  change (∏ x, y i (q x)) * (∏ x, y j (q x)) =
    ∏ x, y i (q x) * y j (q x)
  exact Finset.prod_mul_distrib.symm

/-- Taylor truncations converge to the real exponential. -/
theorem tendsto_truncatedExpSeries (z : ℝ) :
    Tendsto (fun m => truncatedExpSeries z m) atTop (nhds (Real.exp z)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp z).tendsto_sum_nat
  have hpartial (m : ℕ) :
      truncatedExpSeries z m =
        ∑ k ∈ Finset.range (m + 1), z ^ k / Nat.factorial k := by
    exact Fin.sum_univ_eq_sum_range
      (fun k => z ^ k / Nat.factorial k) (m + 1)
  rw [Real.exp_eq_exp_ℝ]
  simpa only [hpartial, Function.comp_apply] using!
    h.comp (tendsto_add_atTop_nat 1)

/-- The ordered-tensor Gram entries are precisely exponential Taylor truncations. -/
theorem orderedTensorFockGram_apply {n d : ℕ} (y : Fin n → Fin d → ℝ) (m : ℕ)
    (r : ℝ) (i j : Fin n) :
    orderedTensorFockGram y m r i j =
      truncatedExpSeries (2 * r ^ 2 * coordinateDot y i j) m := by
  unfold orderedTensorFockGram standardFeatureGram
  change (∑ q : orderedTensorFeature d m,
      orderedTensorFockRow y r i q * orderedTensorFockRow y r j q) = _
  rw [sum_orderedTensorFeature]
  unfold truncatedExpSeries
  apply Finset.sum_congr rfl
  intro k _
  have hq (q : Fin k.1 → Fin d) :
      orderedTensorFockRow y r i (toLex ⟨k, toLex q⟩) *
          orderedTensorFockRow y r j (toLex ⟨k, toLex q⟩) =
        (((2 : ℝ) ^ k.1 / Nat.factorial k.1) * r ^ (2 * k.1)) *
          (orderedTensorMonomial y i (toLex ⟨k, toLex q⟩) *
            orderedTensorMonomial y j (toLex ⟨k, toLex q⟩)) := by
    unfold orderedTensorFockRow scaledFeatureRows orderedTensorWeight orderedTensorDegree
    change (Real.sqrt ((2 : ℝ) ^ k.1 / Nat.factorial k.1) * r ^ k.1 *
          orderedTensorMonomial y i (toLex ⟨k, toLex q⟩)) *
        (Real.sqrt ((2 : ℝ) ^ k.1 / Nat.factorial k.1) * r ^ k.1 *
          orderedTensorMonomial y j (toLex ⟨k, toLex q⟩)) = _
    calc
      _ = Real.sqrt ((2 : ℝ) ^ k.1 / Nat.factorial k.1) ^ 2 *
          r ^ (2 * k.1) *
          (orderedTensorMonomial y i (toLex ⟨k, toLex q⟩) *
            orderedTensorMonomial y j (toLex ⟨k, toLex q⟩)) := by ring
      _ = _ := by
        rw [Real.sq_sqrt]
        exact div_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)
  rw [Finset.sum_congr rfl (fun q _ => hq q)]
  rw [← Finset.mul_sum]
  rw [sum_orderedTensorMonomial_mul]
  simp only [mul_pow]
  rw [pow_mul]
  ring

theorem orderedTensorFockGram_sqrt_eq_truncatedExponentialInnerMatrix
    {n d : ℕ} (y : Fin n → Fin d → ℝ) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    orderedTensorFockGram y m (Real.sqrt t) =
      truncatedExponentialInnerMatrix y m t := by
  ext i j
  rw [orderedTensorFockGram_apply]
  unfold truncatedExponentialInnerMatrix
  rw [Real.sq_sqrt ht]

/-- The determinant of every Fock truncation is its canonical nonnegative Pluecker partition. -/
theorem det_truncatedExponentialInnerMatrix_eq_canonicalFeatureVolume
    {n d : ℕ} (y : Fin n → Fin d → ℝ) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (truncatedExponentialInnerMatrix y m t).det =
      canonicalFeatureVolume (κ := orderedTensorFeature d m)
        (orderedTensorMonomial (m := m) y)
        (orderedTensorWeight (d := d) (m := m))
        (orderedTensorDegree (d := d) (m := m)) t := by
  rw [← orderedTensorFockGram_sqrt_eq_truncatedExponentialInnerMatrix y m t ht]
  unfold orderedTensorFockGram orderedTensorFockRow
  rw [det_scaledFeatureGram_eq_canonicalFeatureVolume _ _ _ orderedTensorWeight_nonneg]
  rw [Real.sq_sqrt ht]

/-- Every finite Taylor truncation already obeys the multiplicative determinant law. -/
theorem det_truncatedExponentialInnerMatrix_mul_sq_le
    {n d : ℕ} (y : Fin n → Fin d → ℝ) (m : ℕ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (truncatedExponentialInnerMatrix y m (a * b)).det ^ 2 ≤
      (truncatedExponentialInnerMatrix y m (a ^ 2)).det *
        (truncatedExponentialInnerMatrix y m (b ^ 2)).det := by
  rw [det_truncatedExponentialInnerMatrix_eq_canonicalFeatureVolume
    y m (a * b) (mul_nonneg ha hb)]
  rw [det_truncatedExponentialInnerMatrix_eq_canonicalFeatureVolume
    y m (a ^ 2) (sq_nonneg a)]
  rw [det_truncatedExponentialInnerMatrix_eq_canonicalFeatureVolume
    y m (b ^ 2) (sq_nonneg b)]
  exact canonicalFeatureVolume_mul_sq_le
    (orderedTensorMonomial y) orderedTensorWeight orderedTensorDegree
      orderedTensorWeight_nonneg a b

theorem tendsto_truncatedExponentialInnerMatrix
    {n d : ℕ} (y : Fin n → Fin d → ℝ) (t : ℝ) :
    Tendsto (fun m => truncatedExponentialInnerMatrix y m t)
      atTop (nhds (coordinateExponentialInnerMatrix y t)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact tendsto_truncatedExpSeries (2 * t * coordinateDot y i j)

theorem tendsto_det_truncatedExponentialInnerMatrix
    {n d : ℕ} (y : Fin n → Fin d → ℝ) (t : ℝ) :
    Tendsto
        (fun m => (truncatedExponentialInnerMatrix y m t).det)
        atTop
        (nhds (coordinateExponentialInnerMatrix y t).det) := by
  exact continuous_id.matrix_det.continuousAt.tendsto.comp
    (tendsto_truncatedExponentialInnerMatrix y t)

/-- **Euclidean Gaussian Fock determinant law.**  The determinant of the full exponential
inner-product matrix inherits multiplicative midpoint log-convexity from its finite nonnegative
Pluecker partitions. -/
theorem coordinateExponentialInnerMatrix_det_mul_sq_le
    {n d : ℕ} (y : Fin n → Fin d → ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (coordinateExponentialInnerMatrix y (a * b)).det ^ 2 ≤
      (coordinateExponentialInnerMatrix y (a ^ 2)).det *
        (coordinateExponentialInnerMatrix y (b ^ 2)).det := by
  apply le_of_tendsto_of_tendsto
    ((tendsto_det_truncatedExponentialInnerMatrix y (a * b)).pow 2)
    ((tendsto_det_truncatedExponentialInnerMatrix y (a ^ 2)).mul
      (tendsto_det_truncatedExponentialInnerMatrix y (b ^ 2)))
  exact Filter.Eventually.of_forall fun m =>
    det_truncatedExponentialInnerMatrix_mul_sq_le y m a b ha hb

/-! ### Reduction of arbitrary finite Hilbert configurations to finite coordinates -/

/-- The exponential inner-product matrix of a family in a real Hilbert space. -/
def hilbertExponentialInnerMatrix {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ι → E) (t : ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.exp (2 * t * inner ℝ (x i) (x j))

/-- Coordinates in mathlib's canonical orthonormal basis of a finite-dimensional Hilbert space. -/
def orthonormalCoordinates {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (x : Fin n → E) : Fin n → Fin (Module.finrank ℝ E) → ℝ :=
  fun i r => inner ℝ (x i) (stdOrthonormalBasis ℝ E r)

theorem coordinateDot_orthonormalCoordinates {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (x : Fin n → E) (i j : Fin n) :
    coordinateDot (orthonormalCoordinates x) i j = inner ℝ (x i) (x j) := by
  unfold coordinateDot orthonormalCoordinates
  simpa only [real_inner_comm (x j)] using
    (stdOrthonormalBasis ℝ E).sum_inner_mul_inner (x i) (x j)

theorem coordinateExponentialInnerMatrix_orthonormalCoordinates
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x : Fin n → E) (t : ℝ) :
    coordinateExponentialInnerMatrix (orthonormalCoordinates x) t =
      hilbertExponentialInnerMatrix x t := by
  ext i j
  simp only [coordinateExponentialInnerMatrix, hilbertExponentialInnerMatrix]
  rw [coordinateDot_orthonormalCoordinates]

theorem hilbertExponentialInnerMatrix_fin_det_mul_sq_le_of_finiteDimensional
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x : Fin n → E)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (hilbertExponentialInnerMatrix x (a * b)).det ^ 2 ≤
      (hilbertExponentialInnerMatrix x (a ^ 2)).det *
        (hilbertExponentialInnerMatrix x (b ^ 2)).det := by
  simpa only [coordinateExponentialInnerMatrix_orthonormalCoordinates] using
    coordinateExponentialInnerMatrix_det_mul_sq_le
      (orthonormalCoordinates x) a b ha hb

/-- **Finite Hilbert Gaussian Fock law.**  No finite-dimensional ambient-space hypothesis is
needed: the finite family is reduced to its own finite-dimensional linear span. -/
theorem hilbertExponentialInnerMatrix_fin_det_mul_sq_le
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : Fin n → E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (hilbertExponentialInnerMatrix x (a * b)).det ^ 2 ≤
      (hilbertExponentialInnerMatrix x (a ^ 2)).det *
        (hilbertExponentialInnerMatrix x (b ^ 2)).det := by
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range x)
  letI : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range x)
  let xs : Fin n → S := fun i =>
    ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩
  have h := hilbertExponentialInnerMatrix_fin_det_mul_sq_le_of_finiteDimensional
    xs a b ha hb
  simpa [hilbertExponentialInnerMatrix, xs] using! h

/-- **Universal finite Hilbert Gaussian Fock law.**  For every finite index type and every real
Hilbert space, the exponential inner-product determinant is multiplicatively log-convex in the
bandwidth parameter. -/
theorem hilbertExponentialInnerMatrix_det_mul_sq_le
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ι → E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (hilbertExponentialInnerMatrix x (a * b)).det ^ 2 ≤
      (hilbertExponentialInnerMatrix x (a ^ 2)).det *
        (hilbertExponentialInnerMatrix x (b ^ 2)).det := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let xf : Fin (Fintype.card ι) → E := fun k => x (e.symm k)
  have h := hilbertExponentialInnerMatrix_fin_det_mul_sq_le xf a b ha hb
  have hreindex (t : ℝ) :
      hilbertExponentialInnerMatrix xf t =
        Matrix.reindex e e (hilbertExponentialInnerMatrix x t) := by
    ext i j
    rfl
  have hdet (t : ℝ) :
      (hilbertExponentialInnerMatrix xf t).det =
        (hilbertExponentialInnerMatrix x t).det := by
    rw [hreindex]
    exact Matrix.det_reindex_self e _
  simpa only [hdet] using h

end GaussianFockApplication

end

end GaloisForLFunctions.HilbertMetric
