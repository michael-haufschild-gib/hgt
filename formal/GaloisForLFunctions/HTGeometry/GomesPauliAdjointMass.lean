import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Algebras.SimpleDLA
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The mass-kernel/stabilizer construction for Pauli adjoint orbits

Gomes, arXiv:2509.25276, constructs gauge mass operators as Gram operators of
infinitesimal orbit displacements and identifies their kernels with stabilizers.
Here that construction is applied to the corpus's single-qubit Pauli matrices.
The exact normalized Gram is `|r|² I - r rᵀ`; the raw commutator energy is eight
times its quadratic form. Its characteristic determinant, kernel axis, and full
symmetry-restoration locus are all classified without nonzero-carrier assumptions.
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- A real three-axis carrier in the corpus's actual single-qubit Pauli matrices. -/
def gomesPauliCarrier (r : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (r 0 : ℂ) • QuantumAlg.pauliX + (r 1 : ℂ) • QuantumAlg.pauliY +
    (r 2 : ℂ) • QuantumAlg.pauliZ

/-- The adjoint-orbit Gram matrix, with the universal Pauli commutator factor removed. -/
def gomesPauliAdjointMass (r : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (r ⬝ᵥ r) • 1 - Matrix.vecMulVec r r

/-- Real Pauli coordinates give a Hermitian carrier. -/
theorem gomesPauliCarrier_isHermitian (r : Fin 3 → ℝ) :
    (gomesPauliCarrier r).IsHermitian := by
  change (gomesPauliCarrier r)ᴴ = gomesPauliCarrier r
  simp [gomesPauliCarrier,QuantumAlg.pauliX_isHermitian,QuantumAlg.pauliY_isHermitian,
    QuantumAlg.pauliZ_isHermitian]

/-- The real Pauli carrier has no coordinate kernel. -/
theorem gomesPauliCarrier_eq_zero_iff (r : Fin 3 → ℝ) :
    gomesPauliCarrier r = 0 ↔ r = 0 := by
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).re) h
    have hi01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).im) h
    simp [gomesPauliCarrier,QuantumAlg.pauliX,QuantumAlg.pauliY,QuantumAlg.pauliZ] at h00 h01 hi01
    funext i
    fin_cases i <;> simp [h00,h01,hi01]
  · rintro rfl
    simp [gomesPauliCarrier]

/-- Pauli commutators realize the cross-product tangent to the conjugacy orbit. -/
theorem gomesPauliCarrier_commutator (r x : Fin 3 → ℝ) :
    gomesPauliCarrier r * gomesPauliCarrier x - gomesPauliCarrier x * gomesPauliCarrier r =
      (2 * Complex.I) • gomesPauliCarrier (r ⨯₃ x) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [gomesPauliCarrier,QuantumAlg.pauliX,QuantumAlg.pauliY,QuantumAlg.pauliZ,
      cross_apply] <;> ring

/-- Explicit orthogonal-complement formula for the orbit Gram operator. -/
theorem gomesPauliAdjointMass_mulVec (r x : Fin 3 → ℝ) :
    gomesPauliAdjointMass r *ᵥ x = (r ⬝ᵥ r) • x - (r ⬝ᵥ x) • r := by
  funext i
  fin_cases i <;>
    simp [gomesPauliAdjointMass,Matrix.mulVec,Matrix.vecMulVec,dotProduct,
      Fin.sum_univ_three] <;> ring

/-- The mass operator is exactly the Gram operator of infinitesimal adjoint displacement. -/
theorem gomesPauliAdjointMass_gram (r x y : Fin 3 → ℝ) :
    x ⬝ᵥ (gomesPauliAdjointMass r *ᵥ y) = (r ⨯₃ x) ⬝ᵥ (r ⨯₃ y) := by
  rw [gomesPauliAdjointMass_mulVec,cross_dot_cross]
  simp only [dotProduct_sub,dotProduct_smul]
  rw [dotProduct_comm x r]
  ring

/-- The orbit Gram energy is nonnegative without restrictions on the carrier. -/
theorem gomesPauliAdjointMass_energy_nonneg (r x : Fin 3 → ℝ) :
    0 ≤ x ⬝ᵥ (gomesPauliAdjointMass r *ᵥ x) := by
  rw [gomesPauliAdjointMass_gram]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg ((r ⨯₃ x) i))

/-- The exact zero-energy directions are the infinitesimal stabilizer of the Pauli carrier. -/
theorem gomesPauliAdjointMass_energy_zero_iff (r x : Fin 3 → ℝ) :
    x ⬝ᵥ (gomesPauliAdjointMass r *ᵥ x) = 0 ↔ r ⨯₃ x = 0 := by
  rw [gomesPauliAdjointMass_gram,dotProduct_self_eq_zero]

/-- The carrier direction is always massless under its own adjoint action. -/
theorem gomesPauliAdjointMass_carrier (r : Fin 3 → ℝ) :
    gomesPauliAdjointMass r *ᵥ r = 0 := by
  rw [gomesPauliAdjointMass_mulVec,sub_self]

/-- The Gram operator has the exact quadratic spectral law. -/
theorem gomesPauliAdjointMass_quadratic (r : Fin 3 → ℝ) :
    gomesPauliAdjointMass r * gomesPauliAdjointMass r =
      (r ⬝ᵥ r) • gomesPauliAdjointMass r := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesPauliAdjointMass,Matrix.mul_apply,Matrix.vecMulVec,dotProduct,
      Fin.sum_univ_three] <;> ring

/-- Its characteristic determinant records one zero mode and two equal transverse masses. -/
theorem gomesPauliAdjointMass_characteristic (r : Fin 3 → ℝ) (mu : ℝ) :
    Matrix.det (mu • (1 : Matrix (Fin 3) (Fin 3) ℝ) - gomesPauliAdjointMass r) =
      mu * (mu - r ⬝ᵥ r)^2 := by
  simp [gomesPauliAdjointMass,Matrix.det_fin_three,Matrix.vecMulVec,dotProduct,
    Fin.sum_univ_three]
  ring

/-- The Gram action is the negative double infinitesimal rotation. -/
theorem gomesPauliAdjointMass_double_cross (r x : Fin 3 → ℝ) :
    gomesPauliAdjointMass r *ᵥ x = -(r ⨯₃ (r ⨯₃ x)) := by
  rw [gomesPauliAdjointMass_mulVec,cross_cross_eq_smul_sub_smul',neg_sub]

/-- The operator kernel equals the zero-energy kernel, including the zero carrier. -/
theorem gomesPauliAdjointMass_kernel (r x : Fin 3 → ℝ) :
    gomesPauliAdjointMass r *ᵥ x = 0 ↔ r ⨯₃ x = 0 := by
  constructor
  · intro h
    apply (gomesPauliAdjointMass_energy_zero_iff r x).mp
    rw [h,dotProduct_zero]
  · intro h
    rw [gomesPauliAdjointMass_double_cross,h,map_zero,neg_zero]

/-- Exact application of the paper's mass-kernel/stabilizer principle to the corpus's Pauli
matrices: massless directions are precisely commuting generators. -/
theorem gomesPauliAdjointMass_kernel_iff_commutes (r x : Fin 3 → ℝ) :
    gomesPauliAdjointMass r *ᵥ x = 0 ↔
      gomesPauliCarrier r * gomesPauliCarrier x = gomesPauliCarrier x * gomesPauliCarrier r := by
  rw [gomesPauliAdjointMass_kernel]
  conv_rhs =>
    rw [← sub_eq_zero,gomesPauliCarrier_commutator,smul_eq_zero,
      or_iff_right (mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) Complex.I_ne_zero),
      gomesPauliCarrier_eq_zero_iff]

/-- The stabilizer is the carrier axis away from the zero carrier, where every direction survives. -/
theorem gomesPauliAdjointMass_kernel_axis (r x : Fin 3 → ℝ) :
    gomesPauliAdjointMass r *ᵥ x = 0 ↔ r = 0 ∨ ∃ c : ℝ, x = c • r := by
  rw [gomesPauliAdjointMass_kernel]
  by_cases hr : r = 0
  · simp [hr]
  · rw [or_iff_right hr]
    rw [← not_iff_not]
    change (r ⨯₃ x ≠ 0) ↔ _
    rw [crossProduct_ne_zero_iff_linearIndependent (v := r) (w := x),
      LinearIndependent.pair_iff' hr]
    simp only [not_exists,ne_comm]

/-- The exact Gram trace is twice the carrier's squared Euclidean length. -/
theorem gomesPauliAdjointMass_trace (r : Fin 3 → ℝ) :
    Matrix.trace (gomesPauliAdjointMass r) = 2 * (r ⬝ᵥ r) := by
  simp [gomesPauliAdjointMass,Matrix.trace,Matrix.diag,Matrix.vecMulVec,dotProduct,
    Fin.sum_univ_three]
  ring

/-- Complete symmetry restoration occurs exactly at the zero carrier. -/
theorem gomesPauliAdjointMass_eq_zero_iff (r : Fin 3 → ℝ) :
    gomesPauliAdjointMass r = 0 ↔ r = 0 := by
  constructor
  · intro h
    have ht := congrArg Matrix.trace h
    rw [gomesPauliAdjointMass_trace,Matrix.trace_zero] at ht
    have hn : r ⬝ᵥ r = 0 := by linarith
    exact dotProduct_self_eq_zero.mp hn
  · rintro rfl
    simp [gomesPauliAdjointMass]

/-- The raw squared Frobenius norm of the actual Pauli commutator is eight times the normalized
orbit Gram energy. This fixes the normalization without a physical convention. -/
theorem gomesPauliAdjointMass_commutator_energy (r x : Fin 3 → ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, Complex.normSq
      ((gomesPauliCarrier r * gomesPauliCarrier x -
        gomesPauliCarrier x * gomesPauliCarrier r) i j)) =
      8 * (x ⬝ᵥ (gomesPauliAdjointMass r *ᵥ x)) := by
  rw [gomesPauliCarrier_commutator,gomesPauliAdjointMass_gram]
  simp [gomesPauliCarrier,QuantumAlg.pauliX,QuantumAlg.pauliY,QuantumAlg.pauliZ,
    Complex.normSq_apply,dotProduct,Fin.sum_univ_two,Fin.sum_univ_three,cross_apply]
  ring

/-- Every Pauli direction commutes with the carrier exactly at complete symmetry restoration. -/
theorem gomesPauliCarrier_full_stabilizer (r : Fin 3 → ℝ) :
    (∀ x : Fin 3 → ℝ,
      gomesPauliCarrier r * gomesPauliCarrier x = gomesPauliCarrier x * gomesPauliCarrier r) ↔
      r = 0 := by
  constructor
  · intro h
    apply (gomesPauliAdjointMass_eq_zero_iff r).mp
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [Matrix.zero_mulVec]
    exact (gomesPauliAdjointMass_kernel_iff_commutes r _).mpr (h _)
  · rintro rfl x
    simp [gomesPauliCarrier]

end GaloisForLFunctions.HTGeometry
