import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Nonnegative graded partition laws

This module isolates the finite graded-partition engine used by feature-space determinant
expansions.  A nonnegative weight `weight i` placed in natural degree `degree i` defines

`gradedPartition weight degree t = ∑ i, weight i * t ^ degree i`.

Two unconditional inequalities follow from finite Cauchy--Schwarz:

* multiplicative midpoint convexity of the partition function;
* nonnegativity of its unnormalised degree variance.

The results are general parent theory.  They carry no Hilbert-space or Gaussian-kernel
assumptions; later modules can discharge nonnegative weights by squared feature minors.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- A finite partition function whose states have nonnegative integer degrees. -/
def gradedPartition (weight : ι → ℝ) (degree : ι → ℕ) (t : ℝ) : ℝ :=
  ∑ i, weight i * t ^ degree i

/-- The unnormalised first degree moment of a finite graded partition function. -/
def gradedFirstMoment (weight : ι → ℝ) (degree : ι → ℕ) (t : ℝ) : ℝ :=
  ∑ i, (degree i : ℝ) * weight i * t ^ degree i

/-- The unnormalised second degree moment of a finite graded partition function. -/
def gradedSecondMoment (weight : ι → ℝ) (degree : ι → ℕ) (t : ℝ) : ℝ :=
  ∑ i, (degree i : ℝ) ^ 2 * weight i * t ^ degree i

/-- **Multiplicative midpoint law.**  A nonnegative finite graded partition function is
log-convex on multiplicative scales.  The square-parameter form avoids any auxiliary square-root
or positivity side condition on the partition function itself. -/
theorem gradedPartition_mul_sq_le
    (weight : ι → ℝ) (degree : ι → ℕ)
    (hweight : ∀ i, 0 ≤ weight i) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    gradedPartition weight degree (a * b) ^ 2 ≤
      gradedPartition weight degree (a ^ 2) *
        gradedPartition weight degree (b ^ 2) := by
  unfold gradedPartition
  convert Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => weight i * (a * b) ^ degree i)
    (f := fun i => weight i * (a ^ 2) ^ degree i)
    (g := fun i => weight i * (b ^ 2) ^ degree i)
    (fun i _ => mul_nonneg (hweight i) (pow_nonneg (sq_nonneg a) _))
    (fun i _ => mul_nonneg (hweight i) (pow_nonneg (sq_nonneg b) _))
    (fun i _ => by
      rw [mul_pow, mul_pow, mul_pow]
      ring_nf
      exact le_rfl) using 1 <;>
    simp only [Finset.sum_const_zero, Finset.sum_mul, pow_mul', mul_pow]

/-- **Degree-fluctuation law.**  The unnormalised variance numerator of a nonnegative finite
graded partition function is nonnegative.  When the partition function is positive, division by
its square says that the second degree moment dominates the square of the mean degree. -/
theorem gradedFirstMoment_sq_le_partition_mul_secondMoment
    (weight : ι → ℝ) (degree : ι → ℕ)
    (hweight : ∀ i, 0 ≤ weight i) (t : ℝ) (ht : 0 ≤ t) :
    gradedFirstMoment weight degree t ^ 2 ≤
      gradedPartition weight degree t * gradedSecondMoment weight degree t := by
  unfold gradedFirstMoment gradedPartition gradedSecondMoment
  convert Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => (degree i : ℝ) * weight i * t ^ degree i)
    (f := fun i => weight i * t ^ degree i)
    (g := fun i => (degree i : ℝ) ^ 2 * weight i * t ^ degree i)
    (fun i _ => mul_nonneg (hweight i) (pow_nonneg ht _))
    (fun i _ => mul_nonneg
      (mul_nonneg (sq_nonneg _) (hweight i)) (pow_nonneg ht _))
    (fun i _ => by
      ring_nf
      exact le_rfl) using 1

section HilbertApplication

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite Hilbert sum whose orthogonal channels are scaled by their natural degrees. -/
def gradedHilbertSum (v : ι → E) (degree : ι → ℕ) (t : ℝ) : E :=
  ∑ i, (t ^ degree i) • v i

/-- Pythagoras identifies the squared norm of a scaled orthogonal grading with its nonnegative
graded partition function. -/
theorem norm_gradedHilbertSum_sq_eq_partition
    (v : ι → E) (degree : ι → ℕ)
    (horth : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0) (t : ℝ) :
    ‖gradedHilbertSum v degree t‖ ^ 2 =
      gradedPartition (fun i => ‖v i‖ ^ 2) degree (t ^ 2) := by
  rw [← real_inner_self_eq_norm_sq]
  unfold gradedHilbertSum gradedPartition
  rw [Finset.sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    simp only [smul_eq_mul]
    rw [← mul_pow]
    ring
  · intro j _ hji
    rw [real_inner_smul_left, real_inner_smul_right, horth i j hji.symm]
    simp
  · simp

/-- **Graded Hilbert multiplicative convexity.**  The fourth power of the scaled norm at a
multiplicative midpoint is bounded by the product of the endpoint squared norms.  This is the
finite orthogonal-feature form later applied to exterior Fock channels. -/
theorem norm_gradedHilbertSum_mul_four_le
    (v : ι → E) (degree : ι → ℕ)
    (horth : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖gradedHilbertSum v degree (a * b)‖ ^ 4 ≤
      ‖gradedHilbertSum v degree (a ^ 2)‖ ^ 2 *
        ‖gradedHilbertSum v degree (b ^ 2)‖ ^ 2 := by
  rw [show ‖gradedHilbertSum v degree (a * b)‖ ^ 4 =
      (‖gradedHilbertSum v degree (a * b)‖ ^ 2) ^ 2 by ring]
  rw [norm_gradedHilbertSum_sq_eq_partition v degree horth]
  rw [norm_gradedHilbertSum_sq_eq_partition v degree horth]
  rw [norm_gradedHilbertSum_sq_eq_partition v degree horth]
  simpa [pow_mul] using gradedPartition_mul_sq_le
    (fun i => ‖v i‖ ^ 2) degree (fun i => sq_nonneg ‖v i‖) (a ^ 2) (b ^ 2)
      (sq_nonneg a) (sq_nonneg b)

end HilbertApplication

section ExteriorGramApplication

open Module Set

variable {κ : Type*} [Fintype κ] [LinearOrder κ]

/-- A maximal coordinate minor of a finite real feature matrix. -/
def standardFeatureMinor {n : ℕ} (evaluation : Fin n → κ → ℝ)
    (s : Set.powersetCard κ n) : ℝ :=
  (Matrix.of fun i j =>
    evaluation i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det

/-- The top exterior feature wedge of the rows of an evaluation matrix. -/
def standardFeatureWedge {n : ℕ} (evaluation : Fin n → κ → ℝ) :
    ⋀[ℝ]^n (κ → ℝ) :=
  exteriorPower.ιMulti ℝ n evaluation

/-- The ordinary Euclidean Gram matrix of a finite real feature matrix. -/
def standardFeatureGram {n : ℕ} (evaluation : Fin n → κ → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k, evaluation i k * evaluation j k

/-- The sum of the squares of all canonical maximal feature minors. -/
def standardFeaturePluckerVolumeSq {n : ℕ} (evaluation : Fin n → κ → ℝ) : ℝ :=
  ∑ s : Set.powersetCard κ n, standardFeatureMinor evaluation s ^ 2

/-- The Euclidean dot-product functional associated with one finite feature row. -/
def finiteDotDual (u : κ → ℝ) : Module.Dual ℝ (κ → ℝ) :=
  { toFun := fun z => ∑ k, u k * z k
    map_add' := fun x y => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := fun c x => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring }

/-- The exterior dual wedge associated with the rows of an evaluation matrix. -/
def standardFeatureWedgeDual {n : ℕ} (evaluation : Fin n → κ → ℝ) :
    Module.Dual ℝ (⋀[ℝ]^n (κ → ℝ)) :=
  exteriorPower.pairingDual ℝ (κ → ℝ) n
    (exteriorPower.ιMulti ℝ n fun i => finiteDotDual (evaluation i))

/-- Every standard exterior coordinate of the feature wedge is its corresponding maximal
minor. -/
theorem standardFeatureWedge_coordinate {n : ℕ} (evaluation : Fin n → κ → ℝ)
    (s : Set.powersetCard κ n) :
    ((Pi.basisFun ℝ κ).exteriorPower n).repr (standardFeatureWedge evaluation) s =
      standardFeatureMinor evaluation s := by
  rw [exteriorPower.basis_repr_apply]
  unfold standardFeatureWedge standardFeatureMinor
  rw [exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1
  ext i j
  simp

/-- The exterior dual wedge evaluates on a standard exterior basis vector as the matching
feature minor. -/
theorem standardFeatureWedgeDual_basis_apply
    {n : ℕ} (evaluation : Fin n → κ → ℝ) (s : Set.powersetCard κ n) :
    standardFeatureWedgeDual evaluation ((Pi.basisFun ℝ κ).exteriorPower n s) =
      standardFeatureMinor evaluation s := by
  rw [exteriorPower.basis_apply]
  unfold standardFeatureWedgeDual exteriorPower.ιMulti_family standardFeatureMinor
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [finiteDotDual]

/-- Pairing the exterior dual wedge with the feature wedge gives the Gram determinant. -/
theorem standardFeatureWedgeDual_wedge_apply
    {n : ℕ} (evaluation : Fin n → κ → ℝ) :
    standardFeatureWedgeDual evaluation (standardFeatureWedge evaluation) =
      (standardFeatureGram evaluation).det := by
  unfold standardFeatureWedgeDual standardFeatureWedge standardFeatureGram
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  congr 1
  ext i j
  simp [finiteDotDual, mul_comm]

/-- **Finite Gram--Cauchy--Binet law.**  The determinant of a finite real feature Gram matrix is
the exact sum of the squares of all its maximal coordinate minors. -/
theorem det_standardFeatureGram_eq_pluckerVolumeSq
    {n : ℕ} (evaluation : Fin n → κ → ℝ) :
    (standardFeatureGram evaluation).det =
      standardFeaturePluckerVolumeSq evaluation := by
  let B := (Pi.basisFun ℝ κ).exteriorPower n
  let w := standardFeatureWedge evaluation
  let L := standardFeatureWedgeDual evaluation
  calc
    (standardFeatureGram evaluation).det = L w :=
      (standardFeatureWedgeDual_wedge_apply evaluation).symm
    _ = L (∑ s, B.repr w s • B s) := by rw [B.sum_repr]
    _ = ∑ s, B.repr w s * L (B s) := by simp
    _ = standardFeaturePluckerVolumeSq evaluation := by
      unfold B w L standardFeaturePluckerVolumeSq
      simp_rw [standardFeatureWedge_coordinate, standardFeatureWedgeDual_basis_apply]
      simp only [smul_eq_mul]

/-- The nonnegative canonical Pluecker weight of one unordered feature basis. -/
def canonicalPluckerWeight {n : ℕ} (evaluation : Fin n → κ → ℝ)
    (featureWeight : κ → ℝ) (s : Set.powersetCard κ n) : ℝ :=
  standardFeatureMinor evaluation s ^ 2 *
    ∏ j, featureWeight (Set.powersetCard.ofFinEmbEquiv.symm s j)

/-- The total degree of one unordered feature basis. -/
def canonicalPluckerDegree {n : ℕ} (featureDegree : κ → ℕ)
    (s : Set.powersetCard κ n) : ℕ :=
  ∑ j, featureDegree (Set.powersetCard.ofFinEmbEquiv.symm s j)

/-- The canonical finite graded Pluecker-volume partition of an evaluation matrix. -/
def canonicalFeatureVolume {n : ℕ} (evaluation : Fin n → κ → ℝ)
    (featureWeight : κ → ℝ) (featureDegree : κ → ℕ) (t : ℝ) : ℝ :=
  gradedPartition (canonicalPluckerWeight evaluation featureWeight)
    (canonicalPluckerDegree featureDegree) t

/-- A feature matrix after orthogonal square-root weighting and degree scaling. -/
def scaledFeatureRows {n : ℕ} (evaluation : Fin n → κ → ℝ)
    (featureWeight : κ → ℝ) (featureDegree : κ → ℕ) (t : ℝ) :
    Fin n → κ → ℝ :=
  fun i k => Real.sqrt (featureWeight k) * t ^ featureDegree k * evaluation i k

/-- Canonical Pluecker weights are nonnegative when the scalar feature weights are. -/
theorem canonicalPluckerWeight_nonneg
    {n : ℕ} (evaluation : Fin n → κ → ℝ) (featureWeight : κ → ℝ)
    (hfeature : ∀ k, 0 ≤ featureWeight k) (s : Set.powersetCard κ n) :
    0 ≤ canonicalPluckerWeight evaluation featureWeight s := by
  exact mul_nonneg (sq_nonneg _)
    (Finset.prod_nonneg fun j _ =>
      hfeature (Set.powersetCard.ofFinEmbEquiv.symm s j))

/-- Scaling the feature columns scales every maximal minor by the product of its selected
column factors. -/
theorem scaled_standardFeatureMinor
    {n : ℕ} (evaluation : Fin n → κ → ℝ)
    (featureWeight : κ → ℝ) (featureDegree : κ → ℕ) (t : ℝ)
    (s : Set.powersetCard κ n) :
    standardFeatureMinor
        (scaledFeatureRows evaluation featureWeight featureDegree t) s =
      (∏ j, Real.sqrt
          (featureWeight (Set.powersetCard.ofFinEmbEquiv.symm s j)) *
        t ^ featureDegree (Set.powersetCard.ofFinEmbEquiv.symm s j)) *
        standardFeatureMinor evaluation s := by
  unfold standardFeatureMinor scaledFeatureRows
  rw [← Matrix.det_mul_row]
  congr 1
  ext i j
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- **Weighted Gram partition identity.**  The determinant of a degree-scaled feature Gram
matrix is exactly its nonnegative canonical Pluecker partition function. -/
theorem det_scaledFeatureGram_eq_canonicalFeatureVolume
    {n : ℕ} (evaluation : Fin n → κ → ℝ)
    (featureWeight : κ → ℝ) (featureDegree : κ → ℕ)
    (hfeature : ∀ k, 0 ≤ featureWeight k) (t : ℝ) :
    (standardFeatureGram
      (scaledFeatureRows evaluation featureWeight featureDegree t)).det =
      canonicalFeatureVolume evaluation featureWeight featureDegree (t ^ 2) := by
  rw [det_standardFeatureGram_eq_pluckerVolumeSq]
  unfold standardFeaturePluckerVolumeSq canonicalFeatureVolume gradedPartition
  apply Finset.sum_congr rfl
  intro s _
  rw [scaled_standardFeatureMinor]
  unfold canonicalPluckerWeight canonicalPluckerDegree
  rw [mul_pow, Finset.prod_mul_distrib, mul_pow, ← Finset.prod_pow]
  simp_rw [Real.sq_sqrt (hfeature _)]
  rw [← Finset.prod_pow, Finset.prod_pow_eq_pow_sum]
  ring

/-- Canonical finite feature volumes obey the multiplicative midpoint law. -/
theorem canonicalFeatureVolume_mul_sq_le
    {n : ℕ} (evaluation : Fin n → κ → ℝ)
    (featureWeight : κ → ℝ) (featureDegree : κ → ℕ)
    (hfeature : ∀ k, 0 ≤ featureWeight k)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    canonicalFeatureVolume evaluation featureWeight featureDegree (a * b) ^ 2 ≤
      canonicalFeatureVolume evaluation featureWeight featureDegree (a ^ 2) *
        canonicalFeatureVolume evaluation featureWeight featureDegree (b ^ 2) := by
  exact gradedPartition_mul_sq_le _ _
    (canonicalPluckerWeight_nonneg evaluation featureWeight hfeature) a b ha hb

/-- **Finite graded Gram determinant law.**  Degree scaling of arbitrary finite orthogonal
features makes the Gram determinant multiplicatively log-convex.  This is the exact finite
truncation theorem used by the Gaussian Fock limit. -/
theorem det_scaledFeatureGram_mul_sq_le
    {n : ℕ} (evaluation : Fin n → κ → ℝ)
    (featureWeight : κ → ℝ) (featureDegree : κ → ℕ)
    (hfeature : ∀ k, 0 ≤ featureWeight k)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (standardFeatureGram
        (scaledFeatureRows evaluation featureWeight featureDegree (a * b))).det ^ 2 ≤
      (standardFeatureGram
          (scaledFeatureRows evaluation featureWeight featureDegree (a ^ 2))).det *
        (standardFeatureGram
          (scaledFeatureRows evaluation featureWeight featureDegree (b ^ 2))).det := by
  rw [det_scaledFeatureGram_eq_canonicalFeatureVolume _ _ _ hfeature]
  rw [det_scaledFeatureGram_eq_canonicalFeatureVolume _ _ _ hfeature]
  rw [det_scaledFeatureGram_eq_canonicalFeatureVolume _ _ _ hfeature]
  simpa [mul_pow, pow_mul] using canonicalFeatureVolume_mul_sq_le
    evaluation featureWeight featureDegree hfeature (a ^ 2) (b ^ 2)
      (sq_nonneg a) (sq_nonneg b)

end ExteriorGramApplication

end

end GaloisForLFunctions.HilbertMetric
