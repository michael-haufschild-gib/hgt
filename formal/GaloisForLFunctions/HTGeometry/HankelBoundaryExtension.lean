import GaloisForLFunctions.HTGeometry.HankelBoundaryFlux
import Mathlib.Analysis.Matrix.Order

/-!
# Positive-semidefinite extension across a Hankel boundary

Suppose an `n x n` Hankel block has a null polynomial `c`.  Padding `c` by one terminal zero
gives zero quadratic energy in the next block.  Positive semidefiniteness upgrades zero energy to
an actual kernel vector, so the last row forces the first omitted moment pairing to vanish.

Thus the single scalar isolated by the terminal-flux law is also the exact obstruction to extending
a singular Hankel face by one positive-semidefinite row and column.  A nonzero boundary flux is not
merely a possible crossing direction: it certifies failure of the next block.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pad a finite coefficient vector by a zero leading coefficient. -/
def padTerminalZero {n : ℕ} (c : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases 0 c

/-- A kernel vector of the current Hankel block has zero quadratic energy after terminal-zero
padding in the next block. -/
theorem dotProduct_finiteHankelMatrix_padTerminalZero_eq_zero
    (m : ℕ → ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hc : finiteHankelMatrix m n *ᵥ c = 0) :
    padTerminalZero c ⬝ᵥ
      (finiteHankelMatrix m (n + 1) *ᵥ padTerminalZero c) = 0 := by
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp only [padTerminalZero, Fin.lastCases_castSucc, Fin.lastCases_last, zero_mul, add_zero]
  apply Finset.sum_eq_zero
  intro i _
  have hi : (∑ j : Fin n, m ((i : ℕ) + (j : ℕ)) * c j) = 0 := by
    simpa [Matrix.mulVec, dotProduct, finiteHankelMatrix] using congrFun hc i
  change c i * (∑ j : Fin (n + 1),
    m ((i : ℕ) + (j : ℕ)) * padTerminalZero c j) = 0
  rw [Fin.sum_univ_castSucc]
  simp only [padTerminalZero, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero]
  simpa using mul_eq_zero_of_right (c i) hi

/-- **PSD extension rigidity.** If a null polynomial of the current block survives one
positive-semidefinite Hankel extension, its pairing with the first omitted monomial is zero. -/
theorem hankelFirstOmittedCoupling_eq_zero_of_posSemidef_succ_of_kernel
    (m : ℕ → ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hpsd : (finiteHankelMatrix m (n + 1)).PosSemidef)
    (hc : finiteHankelMatrix m n *ᵥ c = 0) :
    hankelFirstOmittedCoupling m n c = 0 := by
  let x : Fin (n + 1) → ℝ := padTerminalZero c
  have hquad : x ⬝ᵥ (finiteHankelMatrix m (n + 1) *ᵥ x) = 0 := by
    simpa only [x] using
      dotProduct_finiteHankelMatrix_padTerminalZero_eq_zero m n c hc
  have hfull : finiteHankelMatrix m (n + 1) *ᵥ x = 0 :=
    (hpsd.dotProduct_mulVec_zero_iff x).mp (by simpa using hquad)
  have hlast := congrFun hfull (Fin.last n)
  change (∑ j : Fin (n + 1), m (n + (j : ℕ)) * x j) = 0 at hlast
  rw [Fin.sum_univ_castSucc] at hlast
  simp only [x, padTerminalZero, Fin.lastCases_castSucc, Fin.lastCases_last,
    mul_zero, add_zero] at hlast
  simpa [hankelFirstOmittedCoupling, mul_comm] using hlast

/-- A nonzero first omitted coupling is an explicit certificate that the next Hankel block is not
positive semidefinite. -/
theorem finiteHankelMatrix_succ_not_posSemidef_of_kernel_of_coupling_ne_zero
    (m : ℕ → ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hc : finiteHankelMatrix m n *ᵥ c = 0)
    (hboundary : hankelFirstOmittedCoupling m n c ≠ 0) :
    ¬ (finiteHankelMatrix m (n + 1)).PosSemidef := by
  intro hpsd
  exact hboundary
    (hankelFirstOmittedCoupling_eq_zero_of_posSemidef_succ_of_kernel m n c hpsd hc)

/-- A singular block that admits a PSD extension has zero quadratic terminal flux on every one of
its null vectors. -/
theorem dotProduct_finiteHankelDerivativeMatrix_mulVec_eq_zero_of_posSemidef_succ_of_kernel
    (m : ℕ → ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hpsd : (finiteHankelMatrix m (n + 1)).PosSemidef)
    (hc : finiteHankelMatrix m n *ᵥ c = 0) :
    c ⬝ᵥ (finiteHankelDerivativeMatrix m n *ᵥ c) = 0 := by
  rw [dotProduct_finiteHankelDerivativeMatrix_mulVec_of_kernel m n c hc,
    dotProduct_hankelTerminalMomentVector,
    hankelFirstOmittedCoupling_eq_zero_of_posSemidef_succ_of_kernel m n c hpsd hc]
  ring

/-- **Minimal-face leading-coefficient rigidity.** If the preceding principal Hankel block is
positive definite, every nonzero null vector of the next block has nonzero terminal coefficient.
Equivalently, a first singular null polynomial has its full advertised degree. -/
theorem hankelNullVector_terminal_ne_zero_of_head_posDef
    (m : ℕ → ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (finiteHankelMatrix m n).PosDef)
    (hcne : c ≠ 0)
    (hc : finiteHankelMatrix m (n + 1) *ᵥ c = 0) :
    c (Fin.last n) ≠ 0 := by
  intro hlast
  let d : Fin n → ℝ := fun i => c i.castSucc
  have hdne : d ≠ 0 := by
    intro hd
    apply hcne
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hlast
    · exact congrFun hd j
  have hdkernel : finiteHankelMatrix m n *ᵥ d = 0 := by
    funext i
    have hi := congrFun hc i.castSucc
    change (∑ j : Fin (n + 1),
      m ((i : ℕ) + (j : ℕ)) * c j) = 0 at hi
    rw [Fin.sum_univ_castSucc, hlast, mul_zero, add_zero] at hi
    simpa [Matrix.mulVec, dotProduct, finiteHankelMatrix, d] using hi
  have hpos := hhead.dotProduct_mulVec_pos hdne
  rw [hdkernel, dotProduct_zero] at hpos
  exact lt_irrefl 0 hpos

/-- Change only the first moment not visible to an `(n+1) × (n+1)` Hankel block. -/
def hankelBoundaryPerturbation
    (m : ℕ → ℝ) (n : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  if k = 2 * n + 1 then m k + δ else m k

/-- The current Hankel face is completely insensitive to its first unseen moment. -/
theorem finiteHankelMatrix_boundaryPerturbation
    (m : ℕ → ℝ) (n : ℕ) (δ : ℝ) :
    finiteHankelMatrix (hankelBoundaryPerturbation m n δ) (n + 1) =
      finiteHankelMatrix m (n + 1) := by
  ext i j
  simp only [finiteHankelMatrix, hankelBoundaryPerturbation]
  split_ifs with h
  · have hi : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
    have hj : (j : ℕ) ≤ n := Nat.le_of_lt_succ j.isLt
    omega
  · rfl

/-- Moving the first unseen moment translates the extension coordinate by the null polynomial's
leading coefficient. -/
theorem hankelFirstOmittedCoupling_boundaryPerturbation
    (m : ℕ → ℝ) (n : ℕ) (δ : ℝ) (c : Fin (n + 1) → ℝ) :
    hankelFirstOmittedCoupling (hankelBoundaryPerturbation m n δ) (n + 1) c =
      hankelFirstOmittedCoupling m (n + 1) c + c (Fin.last n) * δ := by
  simp only [hankelFirstOmittedCoupling]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hcast : ∀ j : Fin n,
      n + 1 + (j : ℕ) ≠ 2 * n + 1 := by
    intro j h
    have hj : (j : ℕ) < n := j.isLt
    omega
  simp only [Fin.val_castSucc, Fin.val_last]
  simp_rw [hankelBoundaryPerturbation, if_neg (hcast _)]
  simp only [show n + 1 + n = 2 * n + 1 by omega, if_pos]
  ring

/-- **Extension-coordinate independence.** If a null polynomial has full degree, its first
omitted coupling can be assigned arbitrarily without changing a single entry of the current
Hankel block.  Therefore no invariant of the current face alone can control PSD extension. -/
theorem exists_boundaryPerturbation_coupling_eq
    (m : ℕ → ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) (target : ℝ) :
    ∃ m' : ℕ → ℝ,
      finiteHankelMatrix m' (n + 1) = finiteHankelMatrix m (n + 1) ∧
      hankelFirstOmittedCoupling m' (n + 1) c = target := by
  let δ := (target - hankelFirstOmittedCoupling m (n + 1) c) / c (Fin.last n)
  refine ⟨hankelBoundaryPerturbation m n δ,
    finiteHankelMatrix_boundaryPerturbation m n δ, ?_⟩
  rw [hankelFirstOmittedCoupling_boundaryPerturbation]
  dsimp [δ]
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
