import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Conserved local-compression witness

This module isolates the finite-dimensional Cauchy--Schwarz core of the
two-query locality distinguisher for time-independent local Hamiltonians.

Let `C` be the matrix obtained by compressing Heisenberg evolution back to a
finite local-observable dictionary.  Energy conservation supplies a nonzero
coefficient vector `h` with `C *ᵥ h = h`.  Therefore the squared Frobenius
mass of `C` is at least one.  Choosing input and output dictionary coordinates
uniformly gives mean squared transition weight at least the inverse square of
the dictionary size, independent of evolution time.

The physical two-copy randomized-Pauli protocol and its Haar comparison are
due to Cui--Schuster--Mao--Huang--Brandão, *Random unitaries from Hamiltonian
dynamics*, arXiv:2510.08434.  No novelty is claimed for that protocol here;
the purpose of this module is unconditional formal support for its conserved
coordinate inequality.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- **Conserved-coordinate Frobenius law.** A real matrix with a nonzero fixed
vector has squared Frobenius mass at least one.  In the locality test, `C` is
the local Pauli compression of Heisenberg evolution and the fixed vector is
the coefficient vector of the Hamiltonian itself. -/
theorem localCompression_frobenius_sq_ge_one
    (C : Matrix ι ι ℝ) (h : ι → ℝ) (hh : h ≠ 0)
    (hfix : C *ᵥ h = h) :
    1 ≤ ∑ i, ∑ j, (C i j) ^ 2 := by
  classical
  have hex : ∃ i, h i ≠ 0 := by
    by_contra hnone
    apply hh
    funext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  let S : ℝ := ∑ j, (h j) ^ 2
  let F : ℝ := ∑ i, ∑ j, (C i j) ^ 2
  have hSpos : 0 < S := by
    obtain ⟨i, hi⟩ := hex
    exact Finset.sum_pos' (fun j _ => sq_nonneg (h j))
      ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hrow (i : ι) :
      (h i) ^ 2 ≤ (∑ j, (C i j) ^ 2) * S := by
    rw [← hfix]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (C i) h
  have hSF : S ≤ F * S := by
    dsimp only [S, F]
    calc
      (∑ j, (h j) ^ 2) ≤
          ∑ i, (∑ j, (C i j) ^ 2) * (∑ j, (h j) ^ 2) :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = (∑ i, ∑ j, (C i j) ^ 2) * (∑ j, (h j) ^ 2) := by
        rw [Finset.sum_mul]
  dsimp only [F] at hSF ⊢
  nlinarith

/-- Mean squared transition coefficient obtained by choosing local input and
output dictionary coordinates independently and uniformly. -/
def twoQueryLocalRetentionMean (C : Matrix ι ι ℝ) : ℝ :=
  (∑ i, ∑ j, (C i j) ^ 2) / (Fintype.card ι : ℝ) ^ 2

/-- Every nonzero conserved local coordinate gives inverse-dictionary-squared
mean signal, uniformly in evolution time. -/
theorem twoQueryLocalRetentionMean_ge_card_sq_inv
    [Nonempty ι] (C : Matrix ι ι ℝ) (h : ι → ℝ) (hh : h ≠ 0)
    (hfix : C *ᵥ h = h) :
    1 / (Fintype.card ι : ℝ) ^ 2 ≤ twoQueryLocalRetentionMean C := by
  have hden : 0 < (Fintype.card ι : ℝ) ^ 2 := by
    positivity
  rw [twoQueryLocalRetentionMean, div_le_div_iff_of_pos_right hden]
  exact localCompression_frobenius_sq_ge_one C h hh hfix

/-- If the full traceless observable dimension `K` exceeds the square of the
local dictionary size, the conserved-local signal strictly exceeds the
isotropic benchmark `1 / K`.  For `n` qubits, `K = 4^n - 1` while a fixed-`q`
Pauli dictionary has polynomial cardinality. -/
theorem twoQueryLocalRetentionMean_gt_isotropicBenchmark
    [Nonempty ι] (C : Matrix ι ι ℝ) (h : ι → ℝ) (hh : h ≠ 0)
    (hfix : C *ᵥ h = h) (K : ℕ)
    (hK : (Fintype.card ι) ^ 2 < K) :
    1 / (K : ℝ) < twoQueryLocalRetentionMean C := by
  have hcard : 0 < (Fintype.card ι : ℝ) ^ 2 := by positivity
  have hKreal : (Fintype.card ι : ℝ) ^ 2 < (K : ℝ) := by
    exact_mod_cast hK
  have hinv : 1 / (K : ℝ) < 1 / (Fintype.card ι : ℝ) ^ 2 :=
    one_div_lt_one_div_of_lt hcard hKreal
  exact hinv.trans_le
    (twoQueryLocalRetentionMean_ge_card_sq_inv C h hh hfix)

/-! ## Autonomous energy conservation -/

open NormedSpace

variable {A : Type*} [CStarAlgebra A]

/-- Exponentiating any scalar multiple of `H` preserves `H` exactly under
conjugation.  This is the algebraic source of the fixed coordinate consumed by
`localCompression_frobenius_sq_ge_one`. -/
theorem unitaryEvolution_conserves_generator (H : A) (t : ℝ) :
    exp (-(t • ((-Complex.I) • H))) * H *
        exp (t • ((-Complex.I) • H)) = H := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have hcomm : Commute H (t • ((-Complex.I) • H)) := by
    exact ((Commute.refl H).smul_right (-Complex.I)).smul_right t
  exact hcomm.exp_neg_mul_mul_exp_eq_self

/-- Self-adjoint Hamiltonian form: Heisenberg evolution fixes the Hamiltonian
at every real time. -/
theorem selfAdjoint_unitaryEvolution_conserves_energy
    (H : A) (hH : IsSelfAdjoint H) (t : ℝ) :
    star (exp (t • ((-Complex.I) • H))) * H *
        exp (t • ((-Complex.I) • H)) = H := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have hx : (-Complex.I) • H ∈ skewAdjoint A := by
    rw [skewAdjoint.mem_iff, star_smul, hH.star_eq]
    simp
  rw [star_exp, skewAdjoint.mem_iff.mp (skewAdjoint.smul_mem t hx)]
  exact unitaryEvolution_conserves_generator H t

end

end GaloisForLFunctions.HTGeometry
