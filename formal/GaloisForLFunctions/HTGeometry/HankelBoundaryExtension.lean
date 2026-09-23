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

/-- **Exact two-degree determinant loss at odd contact.**  A terminal-normalized kernel of the
current Hankel block forces the determinant two sizes higher to be minus the square of its first
omitted coupling times the preceding determinant.  Thus odd boundary source is exactly signed
determinant curvature, not merely a witness that positive semidefiniteness fails. -/
theorem det_finiteHankelMatrix_add_two_of_monic_kernel
    (m : ℕ → ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) = 1)
    (hc : finiteHankelMatrix m (n + 1) *ᵥ c = 0) :
    (finiteHankelMatrix m (n + 2)).det =
      -(hankelFirstOmittedCoupling m (n + 1) c) ^ (2 : ℕ) *
        (finiteHankelMatrix m n).det := by
  let M := finiteHankelMatrix m (n + 2)
  let v : Fin (n + 2) → ℝ := padTerminalZero c
  let k : Fin (n + 2) := (Fin.last n).castSucc
  let ell : Fin (n + 2) := Fin.last (n + 1)
  let gamma := hankelFirstOmittedCoupling m (n + 1) c
  let B := M.updateCol k (M *ᵥ v)
  have hMv_cast (i : Fin (n + 1)) : (M *ᵥ v) i.castSucc = 0 := by
    change (∑ j : Fin (n + 2), m ((i : ℕ) + (j : ℕ)) * v j) = 0
    rw [Fin.sum_univ_castSucc]
    simp only [v, padTerminalZero, Fin.lastCases_castSucc, Fin.val_castSucc,
      Fin.lastCases_last, mul_zero, add_zero]
    simpa [finiteHankelMatrix, Matrix.mulVec, dotProduct] using congrFun hc i
  have hMv_last : (M *ᵥ v) ell = gamma := by
    change (∑ j : Fin (n + 2), m ((ell : ℕ) + (j : ℕ)) * v j) = gamma
    rw [Fin.sum_univ_castSucc]
    simp only [v, padTerminalZero, Fin.lastCases_castSucc, Fin.lastCases_last,
      mul_zero, add_zero, ell, Fin.val_last]
    simp only [gamma, hankelFirstOmittedCoupling]
    apply Finset.sum_congr rfl
    intro j _
    change m (n + 1 + (j : ℕ)) * c j = c j * m (n + 1 + (j : ℕ))
    ring
  have hcol : (fun r => ∑ j, v j • M r j) = M *ᵥ v := by
    funext r
    simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hBdet : B.det = M.det := by
    have h := Matrix.det_updateCol_sum M k v
    rw [hcol] at h
    simpa [B, v, k, padTerminalZero, hlast] using h
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    B.submatrix ell.succAbove k.succAbove
  have hBdet_expand : B.det = -gamma * N.det := by
    rw [Matrix.det_succ_column B k]
    rw [Finset.sum_eq_single ell]
    · have hsign : (-1 : ℝ) ^ ((ell : ℕ) + (k : ℕ)) = -1 := by
        change (-1 : ℝ) ^ ((n + 1) + n) = -1
        rw [show n + 1 + n = 2 * n + 1 by omega, pow_succ]
        simp
      rw [hsign]
      simp only [B, Matrix.updateCol_self, hMv_last, N]
      ring
    · intro i _ hi
      have hik : i ≠ ell := hi
      have hi0 : (M *ᵥ v) i = 0 := by
        revert hik
        refine Fin.lastCases ?_ (fun j => ?_) i
        · intro hik
          exact (hik rfl).elim
        · intro _
          exact hMv_cast j
      simp [B, hi0]
    · simp
  let R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    N.updateRow (Fin.last n) (∑ i, c i • N i)
  have hRdet : R.det = N.det := by
    simpa [R, hlast] using Matrix.det_updateRow_sum N (Fin.last n) c
  have hk_cast (j : Fin n) : k.succAbove j.castSucc = j.castSucc.castSucc := by
    dsimp only [k]
    rw [Fin.succAbove_castSucc_of_lt]
    exact Fin.castSucc_lt_last j
  have hk_last : k.succAbove (Fin.last n) = ell := by
    dsimp only [k, ell]
    rw [Fin.succAbove_castSucc_self]
    rfl
  have hR_cast (j : Fin n) : R (Fin.last n) j.castSucc = 0 := by
    simp only [R, Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ i : Fin (n + 1), c i *
      B (ell.succAbove i) (k.succAbove j.castSucc)) = 0
    rw [hk_cast]
    simp only [ell, Fin.succAbove_last]
    have hne : j.castSucc.castSucc ≠ k := by
      apply Fin.ne_of_lt
      change (j : ℕ) < n
      exact j.isLt
    have hsum : (∑ i : Fin (n + 1), c i * B i.castSucc j.castSucc.castSucc) =
        ∑ i : Fin (n + 1), c i * m ((i : ℕ) + (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _
      change c i * (M.updateCol k (M *ᵥ v)) i.castSucc j.castSucc.castSucc = _
      rw [Matrix.updateCol_ne hne]
      rfl
    rw [hsum]
    have hj := congrFun hc j.castSucc
    simp only [finiteHankelMatrix, Matrix.mulVec, dotProduct, Pi.zero_apply,
      Fin.val_castSucc] at hj
    simpa [mul_comm, add_comm] using hj
  have hR_last : R (Fin.last n) (Fin.last n) = gamma := by
    simp only [R, Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ i : Fin (n + 1), c i *
      B (ell.succAbove i) (k.succAbove (Fin.last n))) = gamma
    rw [hk_last]
    simp only [ell, Fin.succAbove_last]
    have hne : ell ≠ k := by
      exact Fin.ne_of_gt (by
        simpa only [ell, k] using Fin.castSucc_lt_last (Fin.last n))
    simp only [gamma, hankelFirstOmittedCoupling]
    apply Finset.sum_congr rfl
    intro i _
    change c i * (M.updateCol k (M *ᵥ v)) i.castSucc ell = _
    rw [Matrix.updateCol_ne hne]
    change c i * m ((i : ℕ) + (n + 1)) = c i * m (n + 1 + (i : ℕ))
    rw [add_comm (i : ℕ) (n + 1)]
  have hminor :
      (R.submatrix (Fin.last n).succAbove (Fin.last n).succAbove).det =
        (finiteHankelMatrix m n).det := by
    congr 1
    ext i j
    rw [Matrix.submatrix_apply, Fin.succAbove_last_apply,
      Fin.succAbove_last_apply]
    have hi : i.castSucc ≠ Fin.last n := Fin.ne_of_lt (Fin.castSucc_lt_last i)
    change (N.updateRow (Fin.last n) (∑ q, c q • N q)) i.castSucc j.castSucc = _
    rw [Matrix.updateRow_ne hi]
    change (B.submatrix ell.succAbove k.succAbove) i.castSucc j.castSucc = _
    rw [Matrix.submatrix_apply, Fin.succAbove_last_apply]
    rw [hk_cast]
    have hne : j.castSucc.castSucc ≠ k := by
      apply Fin.ne_of_lt
      change (j : ℕ) < n
      exact j.isLt
    change (M.updateCol k (M *ᵥ v)) i.castSucc.castSucc j.castSucc.castSucc = _
    rw [Matrix.updateCol_ne hne]
    rfl
  have hRdet_expand : R.det = gamma * (finiteHankelMatrix m n).det := by
    rw [Matrix.det_succ_row R (Fin.last n)]
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp only [hR_last, Fin.val_last, hminor]
      rw [show (-1 : ℝ) ^ (n + n) = 1 by
        rw [show n + n = 2 * n by omega]
        simp]
      ring
    · intro j _ hj
      have hj0 : R (Fin.last n) j = 0 := by
        revert hj
        refine Fin.lastCases ?_ (fun q => ?_) j
        · intro hj
          exact (hj rfl).elim
        · intro _
          exact hR_cast q
      simp [hj0]
    · simp
  rw [← hBdet, hBdet_expand, ← hRdet, hRdet_expand]
  ring

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
