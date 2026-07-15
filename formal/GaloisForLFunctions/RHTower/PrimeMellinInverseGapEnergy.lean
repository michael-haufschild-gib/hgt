/-
# Prime--Mellin boundary origin of the inverse-gap energy

The universal right-half-plane Cauchy Gram already present in the CCM Mellin colligation has a
finite boundary commutator which removes its divergent diagonal.  For nodes

`w_i(epsilon) = epsilon + i x_i`

and a diagonal value packet `v`, its matrix entries are

`C_epsilon(i,j) (v_j-v_i) = (v_j-v_i)/(2 epsilon + i(x_i-x_j))`.

Their squared entry norms are the Lorentzian regularizations

`|v_i-v_j|^2 / (4 epsilon^2 + (x_i-x_j)^2)`.

At the boundary this is the inverse-square gap energy.  Before taking any boundary value, the
whole commutator is exactly the commutator of the resolved von-Mangoldt Gram minus the shifted
polar Gram plus the critical Mellin-defect Gram.  Thus the inverse-gap object is derived on
arbitrary real nodes from the prime--polar--Mellin source identity; Xi zeros are not used in its
construction.
-/
import GaloisForLFunctions.RHTower.CCMComplexMellinColligation

open scoped BigOperators ComplexConjugate
open Complex Matrix

noncomputable section

namespace RHTower

/-- Entrywise form of the commutator of a matrix `G` with the diagonal value operator `diag(v)`:
`[G,diag(v)]_{ij} = G_{ij}(v_j-v_i)`. -/
def gramValueCommutator {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => G i j * (v j - v i)

/-- The entrywise definition is the literal matrix commutator with the diagonal value
operator.  This identifies the residue as an operator energy, not merely a weighted graph sum. -/
theorem gramValueCommutator_eq_matrixCommutator {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    gramValueCommutator G v =
      G * Matrix.diagonal v - Matrix.diagonal v * G := by
  ext i j
  simp only [gramValueCommutator, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.sub_apply]
  ring

/-- The value commutator transports a signed three-channel incidence exactly. -/
theorem gramValueCommutator_sub_add {N : ℕ}
    (E B M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    gramValueCommutator (E - B + M) v =
      gramValueCommutator E v - gramValueCommutator B v + gramValueCommutator M v := by
  ext i j
  simp only [gramValueCommutator, Matrix.add_apply, Matrix.sub_apply]
  ring

/-- Nodes approaching the imaginary boundary of the Mellin right half-plane. -/
def primeMellinBoundaryNode {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (i : Fin N) : ℂ :=
  (ε : ℂ) + (x i : ℂ) * I

/-- The pair coordinate of two boundary nodes is the regularized imaginary gap. -/
theorem primeMellinBoundaryNode_add_star {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (i j : Fin N) :
    primeMellinBoundaryNode ε x i + star (primeMellinBoundaryNode ε x j) =
      ((2 * ε : ℝ) : ℂ) + ((x i - x j : ℝ) : ℂ) * I := by
  simp only [primeMellinBoundaryNode, map_add, Complex.conj_ofReal, map_mul,
    conj_I]
  push_cast
  ring

/-- Exact entry of the Cauchy-Gram value commutator on a boundary packet. -/
theorem gramValueCommutator_cauchy_boundary_apply {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (v : Fin N → ℂ) (i j : Fin N) :
    gramValueCommutator
        (cauchyRightHalfPlaneGram (primeMellinBoundaryNode ε x)) v i j =
      (v j - v i) /
        (((2 * ε : ℝ) : ℂ) + ((x i - x j : ℝ) : ℂ) * I) := by
  rw [gramValueCommutator, cauchyRightHalfPlaneGram,
    primeMellinBoundaryNode_add_star]
  simp only [one_div, div_eq_mul_inv]
  ring

/-- Squared entry energy is the exact Lorentzian regularization of the inverse-gap weight. -/
theorem norm_sq_gramValueCommutator_cauchy_boundary_apply {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (v : Fin N → ℂ) (i j : Fin N) :
    ‖gramValueCommutator
        (cauchyRightHalfPlaneGram (primeMellinBoundaryNode ε x)) v i j‖ ^ 2 =
      ‖v j - v i‖ ^ 2 / ((2 * ε) ^ 2 + (x i - x j) ^ 2) := by
  rw [gramValueCommutator_cauchy_boundary_apply, norm_div, div_pow]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, mul_zero, Complex.I_im, mul_one, add_zero, Complex.add_im,
    zero_add]

/-- Finite Hilbert--Schmidt entry energy of the regularized Cauchy boundary commutator. -/
def regularizedInverseGapCommutatorEnergy {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (v : Fin N → ℂ) : ℝ :=
  ∑ i, ∑ j,
    ‖gramValueCommutator
        (cauchyRightHalfPlaneGram (primeMellinBoundaryNode ε x)) v i j‖ ^ 2

/-- The regularized commutator energy is the ordered Lorentzian pair energy. -/
theorem regularizedInverseGapCommutatorEnergy_eq {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (v : Fin N → ℂ) :
    regularizedInverseGapCommutatorEnergy ε x v =
      ∑ i, ∑ j, ‖v j - v i‖ ^ 2 /
        ((2 * ε) ^ 2 + (x i - x j) ^ 2) := by
  unfold regularizedInverseGapCommutatorEnergy
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  exact norm_sq_gramValueCommutator_cauchy_boundary_apply ε x v i j

/-- The ordered inverse-gap energy.  Its diagonal is definitionally zero, and for pairwise
distinct nodes it is twice `sum_(i<j) |v_i-v_j|^2/(x_i-x_j)^2`. -/
def orderedInverseGapEnergy {N : ℕ}
    (x : Fin N → ℝ) (v : Fin N → ℂ) : ℝ :=
  ∑ i, ∑ j, ‖v j - v i‖ ^ 2 / (x i - x j) ^ 2

/-- Boundary evaluation of the source-derived commutator is exactly the ordered inverse-gap
energy. -/
theorem regularizedInverseGapCommutatorEnergy_zero {N : ℕ}
    (x : Fin N → ℝ) (v : Fin N → ℂ) :
    regularizedInverseGapCommutatorEnergy 0 x v = orderedInverseGapEnergy x v := by
  rw [regularizedInverseGapCommutatorEnergy_eq]
  unfold orderedInverseGapEnergy
  simp only [mul_zero, zero_pow, OfNat.ofNat, zero_add]

/-- **Prime--polar--Mellin incidence for inverse-gap regularization.**  At every positive
regularization scale, before any zero set is chosen, the Cauchy value commutator is the exact
signed sum of the resolved prime, shifted-polar, and critical Mellin-defect commutators. -/
theorem cauchyBoundaryValueCommutator_eq_prime_sub_shiftedPolar_add_mellinDefect
    {N : ℕ} (ε : ℝ) (hε : 0 < ε) (x : Fin N → ℝ) (v : Fin N → ℂ) :
    gramValueCommutator
        (cauchyRightHalfPlaneGram (primeMellinBoundaryNode ε x)) v =
      gramValueCommutator
          (vonMangoldtPrimeRightHalfPlaneGram (primeMellinBoundaryNode ε x)) v -
        gramValueCommutator
          (shiftedPolarRightHalfPlaneGram (primeMellinBoundaryNode ε x)) v +
        gramValueCommutator
          (criticalMellinDefectRightHalfPlaneGram (primeMellinBoundaryNode ε x)) v := by
  rw [cauchyRightHalfPlaneGram_eq_prime_sub_shiftedPolar_add_criticalMellinDefect,
    gramValueCommutator_sub_add]
  intro i
  simp only [primeMellinBoundaryNode, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
    mul_one, sub_self, add_zero]
  exact hε

end RHTower
