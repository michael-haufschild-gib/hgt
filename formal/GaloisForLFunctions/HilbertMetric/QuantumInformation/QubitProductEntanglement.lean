import GaloisForLFunctions.HTGeometry.PureBipartiteEntanglementEntropy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Qubit entanglement forced by three product measurements

Unbiasedness to product bases with the three Pauli qubit bases forces the
qubit reduction to be one half of the identity. The environment basis may
vary with both measurement axis and qubit outcome. Parseval converts the
individual product probabilities into marginal probabilities; the three
axes determine all entries of the reduced density matrix.

This applies the product-basis normal form of Yang, arXiv:2611.21188,
Section 2.1, equation (1), in arbitrary environment dimension.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.QubitProducts
open GaloisForLFunctions.HTGeometry

inductive Axis | z | x | y

variable {κ : Type*} [Fintype κ]

/-- A qubit coefficient row as a vector in the environment Hilbert space. -/
def environmentRow (ψ : Bool × κ → ℂ) (b : Bool) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun j => ψ (b, j))

private def halfScale : ℂ := (Real.sqrt 2 / 2 : ℝ)

private theorem halfScale_norm_sq : ‖halfScale‖ ^ 2 = (1 / 2 : ℝ) := by
  change ‖((Real.sqrt 2 / 2 : ℝ) : ℂ)‖ ^ 2 = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

private theorem halfScale_sq : halfScale ^ 2 = (1 / 2 : ℂ) := by
  unfold halfScale
  rw [← Complex.ofReal_pow, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private theorem conj_halfScale : starRingEnd ℂ halfScale = halfScale := by
  exact Complex.conj_ofReal _

/-- The three normalized qubit measurement bases, in Z, X, and Y order. -/
def qubitVector : Axis → Bool → EuclideanSpace ℂ Bool
  | .z, b => WithLp.toLp 2 (fun i => if i = b then 1 else 0)
  | .x, false => WithLp.toLp 2 (fun _ => halfScale)
  | .x, true => WithLp.toLp 2 (fun i => if i then -halfScale else halfScale)
  | .y, false => WithLp.toLp 2 (fun i => if i then -Complex.I * halfScale else halfScale)
  | .y, true => WithLp.toLp 2 (fun i => if i then Complex.I * halfScale else halfScale)

/-- Each of the three qubit families is orthonormal. -/
theorem qubitVector_orthonormal (a : Axis) : Orthonormal ℂ (qubitVector a) := by
  apply orthonormal_iff_ite.mpr
  intro b c
  rw [PiLp.inner_apply, Fintype.sum_bool]
  cases a <;> cases b <;> cases c <;>
    simp only [qubitVector, WithLp.ofLp_toLp, RCLike.inner_apply,
      map_mul, map_neg, map_one, map_zero, conj_halfScale, Complex.conj_I,
      Bool.false_eq_true, Bool.true_eq_false, if_true, if_false,
      mul_one, mul_zero, zero_add, add_zero] <;>
      ring_nf <;> norm_num [halfScale_sq, Complex.I_sq]

/-- Conditional environment vectors for the three normalized Pauli bases. -/
def measurementBranch (ψ : Bool × κ → ℂ) : Axis → Bool → EuclideanSpace ℂ κ
  | .z, b => environmentRow ψ b
  | .x, false => halfScale • (environmentRow ψ false + environmentRow ψ true)
  | .x, true => halfScale • (environmentRow ψ false - environmentRow ψ true)
  | .y, false => halfScale • (environmentRow ψ false + Complex.I • environmentRow ψ true)
  | .y, true => halfScale • (environmentRow ψ false - Complex.I • environmentRow ψ true)

/-- Actual product-basis amplitudes, allowing a separate environment basis for every branch. -/
def productAmplitude (ψ : Bool × κ → ℂ)
    (B : Axis → Bool → OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ))
    (a : Axis) (b : Bool) (j : κ) : ℂ :=
  inner ℂ (B a b j) (measurementBranch ψ a b)

/-- A pure product vector in qubit-environment coordinates. -/
def productVector (u : EuclideanSpace ℂ Bool) (v : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (Bool × κ) :=
  WithLp.toLp 2 (fun z => u z.1 * v z.2)

private theorem productVector_inner (u u' : EuclideanSpace ℂ Bool)
    (v v' : EuclideanSpace ℂ κ) :
    inner ℂ (productVector u v) (productVector u' v') = inner ℂ u u' * inner ℂ v v' := by
  rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change inner ℂ (u i * v j) (u' i * v' j) = inner ℂ (u i) (u' i) * inner ℂ (v j) (v' j)
  simp only [RCLike.inner_apply, map_mul]
  ring

/-- The measurement vectors remain orthonormal with a branch-dependent environment basis. -/
theorem product_measurement_orthonormal
    (B : Axis → Bool → OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ)) (a : Axis) :
    Orthonormal ℂ (fun z : Bool × κ => productVector (qubitVector a z.1) (B a z.1 z.2)) := by
  classical
  apply orthonormal_iff_ite.mpr
  rintro ⟨b, j⟩ ⟨c, k⟩
  rw [productVector_inner, (orthonormal_iff_ite.mp (qubitVector_orthonormal a)) b c]
  by_cases hbc : b = c
  · subst c
    rw [if_pos rfl, one_mul, (orthonormal_iff_ite.mp (B a b).orthonormal) j k]
    simp only [Prod.mk.injEq, true_and]
  · rw [if_neg hbc, zero_mul, if_neg (fun h => hbc (congrArg Prod.fst h))]

/-- The conditional product vectors form a complete orthonormal measurement basis. -/
def productMeasurementBasis
    (B : Axis → Bool → OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ)) (a : Axis) :
    OrthonormalBasis (Bool × κ) ℂ (EuclideanSpace ℂ (Bool × κ)) := by
  apply OrthonormalBasis.mk (product_measurement_orthonormal B a)
  exact le_of_eq (LinearIndependent.span_eq_top_of_card_eq_finrank'
    (product_measurement_orthonormal B a).linearIndependent (by simp)).symm

@[simp] theorem productMeasurementBasis_apply
    (B : Axis → Bool → OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ))
    (a : Axis) (z : Bool × κ) :
    productMeasurementBasis B a z = productVector (qubitVector a z.1) (B a z.1 z.2) := by
  simp only [productMeasurementBasis, OrthonormalBasis.coe_mk]

/-- The branch amplitude is exactly the inner product with the corresponding product vector. -/
theorem productAmplitude_eq_inner (ψ : Bool × κ → ℂ)
    (B : Axis → Bool → OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ))
    (a : Axis) (b : Bool) (j : κ) :
    productAmplitude ψ B a b j =
      inner ℂ (productVector (qubitVector a b) (B a b j)) (WithLp.toLp 2 ψ) := by
  unfold productAmplitude
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;>
    simp only [measurementBranch, qubitVector, productVector, environmentRow,
      PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, WithLp.ofLp_toLp,
      RCLike.inner_apply, map_mul, map_neg, conj_halfScale, Complex.conj_I,
      Bool.false_eq_true, Bool.true_eq_false, if_true, if_false,
      map_zero, mul_zero, zero_mul, one_mul, Finset.sum_const_zero, zero_add, add_zero]
  all_goals
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- Equal product probabilities force the qubit marginal probability to be one half. -/
theorem branch_norm_sq [Nonempty κ] (ψ : Bool × κ → ℂ)
    (B : Axis → Bool → OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ))
    (h : ∀ a b j, ‖productAmplitude ψ B a b j‖ ^ 2 = 1 / (2 * Fintype.card κ : ℝ))
    (a : Axis) (b : Bool) : ‖measurementBranch ψ a b‖ ^ 2 = (1 / 2 : ℝ) := by
  rw [← (B a b).sum_sq_norm_inner_right]
  change (∑ j, ‖productAmplitude ψ B a b j‖ ^ 2) = _
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- The three qubit marginals force two orthogonal coefficient rows of equal squared norm. -/
theorem coefficient_rows_orthogonal [Nonempty κ] (ψ : Bool × κ → ℂ)
    (B : Axis → Bool → OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ))
    (h : ∀ a b j, ‖productAmplitude ψ B a b j‖ ^ 2 = 1 / (2 * Fintype.card κ : ℝ)) :
    ‖environmentRow ψ false‖ ^ 2 = (1 / 2 : ℝ) ∧
    ‖environmentRow ψ true‖ ^ 2 = (1 / 2 : ℝ) ∧
    inner ℂ (environmentRow ψ false) (environmentRow ψ true) = 0 := by
  have h₀ := branch_norm_sq ψ B h .z false
  have h₁ := branch_norm_sq ψ B h .z true
  change ‖environmentRow ψ false‖ ^ 2 = (1 / 2 : ℝ) at h₀
  change ‖environmentRow ψ true‖ ^ 2 = (1 / 2 : ℝ) at h₁
  have hx := branch_norm_sq ψ B h .x false
  have hy := branch_norm_sq ψ B h .y false
  change ‖halfScale • (environmentRow ψ false + environmentRow ψ true)‖ ^ 2 = _ at hx
  change ‖halfScale • (environmentRow ψ false + Complex.I • environmentRow ψ true)‖ ^ 2 = _ at hy
  rw [norm_smul, mul_pow, halfScale_norm_sq, @norm_add_sq ℂ, h₀, h₁] at hx
  rw [norm_smul, mul_pow, halfScale_norm_sq, @norm_add_sq ℂ, h₀,
    norm_smul, Complex.norm_I, one_mul, h₁, inner_smul_right] at hy
  change (1 / 2 : ℝ) * (1 / 2 + 2 *
    (inner ℂ (environmentRow ψ false) (environmentRow ψ true)).re + 1 / 2) = 1 / 2 at hx
  change (1 / 2 : ℝ) * (1 / 2 + 2 *
    (Complex.I * inner ℂ (environmentRow ψ false) (environmentRow ψ true)).re + 1 / 2) = 1 / 2 at hy
  rw [Complex.I_mul_re] at hy
  refine ⟨h₀, h₁, Complex.ext ?_ ?_⟩
  · change (inner ℂ (environmentRow ψ false) (environmentRow ψ true)).re = 0
    linarith only [hx]
  · change (inner ℂ (environmentRow ψ false) (environmentRow ψ true)).im = 0
    linarith only [hy]

private theorem reduction_eq_inner (ψ : Bool × κ → ℂ) (i j : Bool) :
    pureStateReducedLeft ψ i j = inner ℂ (environmentRow ψ j) (environmentRow ψ i) := by
  rw [pureStateReducedLeft_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [RCLike.inner_apply]
  rfl

/-- Unbiasedness to the three product measurements forces maximal entanglement of the qubit. -/
theorem product_unbiased_reduced [Nonempty κ] (ψ : Bool × κ → ℂ)
    (B : Axis → Bool → OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ))
    (h : ∀ a b j, ‖productAmplitude ψ B a b j‖ ^ 2 = 1 / (2 * Fintype.card κ : ℝ)) :
    pureStateReducedLeft ψ = (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  classical
  obtain ⟨h₀, h₁, ho⟩ := coefficient_rows_orthogonal ψ B h
  have ho' : inner ℂ (environmentRow ψ true) (environmentRow ψ false) = 0 := by
    rw [← inner_conj_symm, ho, map_zero]
  have he₀ : inner ℂ (environmentRow ψ false) (environmentRow ψ false) = (1 / 2 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (‖environmentRow ψ false‖ : ℂ) ^ 2 = 1 / 2
    calc
      _ = ((‖environmentRow ψ false‖ ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
      _ = 1 / 2 := by rw [h₀]; norm_num
  have he₁ : inner ℂ (environmentRow ψ true) (environmentRow ψ true) = (1 / 2 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (‖environmentRow ψ true‖ : ℂ) ^ 2 = 1 / 2
    calc
      _ = ((‖environmentRow ψ true‖ ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
      _ = 1 / 2 := by rw [h₁]; norm_num
  ext i j
  cases i <;> cases j <;>
    simp only [reduction_eq_inner, he₀, he₁, ho, ho', Matrix.smul_apply,
      Matrix.one_apply, Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
      smul_eq_mul, mul_zero, mul_one]

/-- Unbiasedness stated directly against the complete product bases gives the maximally mixed qubit. -/
theorem product_basis_unbiased_reduced [Nonempty κ] (ψ : Bool × κ → ℂ)
    (B : Axis → Bool → OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ))
    (h : ∀ a z, ‖inner ℂ (productMeasurementBasis B a z)
      (WithLp.toLp 2 ψ)‖ ^ 2 = 1 / (2 * Fintype.card κ : ℝ)) :
    pureStateReducedLeft ψ = (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  apply product_unbiased_reduced ψ B
  intro a b j
  rw [productAmplitude_eq_inner, ← productMeasurementBasis_apply B a (b, j)]
  exact h a (b, j)

/-- No product pure state can be unbiased to all three product measurements. -/
theorem no_product_unbiased [Nonempty κ] (ψ : Bool × κ → ℂ)
    (B : Axis → Bool → OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ))
    (h : ∀ a b j, ‖productAmplitude ψ B a b j‖ ^ 2 = 1 / (2 * Fintype.card κ : ℝ)) :
    ¬ ∃ u : Bool → ℂ, ∃ v : κ → ℂ, ∀ i j, ψ (i, j) = u i * v j := by
  rintro ⟨u, v, huv⟩
  obtain ⟨h₀, h₁, ho⟩ := coefficient_rows_orthogonal ψ B h
  have hu : u false ≠ 0 := by
    intro hu
    have hz : environmentRow ψ false = 0 := by
      ext j
      change ψ (false, j) = 0
      rw [huv, hu, zero_mul]
    rw [hz, norm_zero, zero_pow two_ne_zero] at h₀
    norm_num at h₀
  have hr : environmentRow ψ true = (u true / u false) • environmentRow ψ false := by
    ext j
    change ψ (true, j) = (u true / u false) * ψ (false, j)
    rw [huv, huv]
    field_simp
  have he : inner ℂ (environmentRow ψ false) (environmentRow ψ false) = (1 / 2 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (‖environmentRow ψ false‖ : ℂ) ^ 2 = 1 / 2
    calc
      _ = ((‖environmentRow ψ false‖ ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
      _ = 1 / 2 := by rw [h₀]; norm_num
  rw [hr, inner_smul_right, he] at ho
  have hz : u true / u false = 0 := (mul_eq_zero.mp ho).resolve_right (by norm_num)
  rw [hr, hz, zero_smul, norm_zero, zero_pow two_ne_zero] at h₁
  norm_num at h₁

#print axioms productMeasurementBasis
#print axioms product_basis_unbiased_reduced
#print axioms no_product_unbiased
#print axioms product_measurement_orthonormal
#print axioms productAmplitude_eq_inner
#print axioms branch_norm_sq
#print axioms coefficient_rows_orthogonal
#print axioms product_unbiased_reduced
end GaloisForLFunctions.HilbertMetric.QubitProducts
