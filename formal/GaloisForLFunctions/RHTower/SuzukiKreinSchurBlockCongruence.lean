import GaloisForLFunctions.RHTower.SuzukiAffineResolventKreinDefect
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# General finite block congruence for the Suzuki Krein completion

The scalar Krein weld (`SuzukiAffineResolventKreinDefect`) fixes positivity of a two-channel form
`Q(x,y) = a x² + 2b xy + (c − n) y²` at the exact Schur threshold `c ≥ n + b²/a`.  The full weld
lives on a signed Krein splitting `H = H₊ ⊕ H₋` with metric `S = diag(P, −N)` (`P > 0`, `N > 0`) and
a self-adjoint source completion `C = [[C₊₊, C₊₋],[C₊₋ᴴ, C₋₋]]`.  When full-frequency projective
holonomy couples the two channels off-diagonally, diagonal debt cancellation is not enough: the
threshold acquires a genuine cross-channel Schur tax.

This file proves the general finite-dimensional block congruence underlying that statement.  With the
completed positive block `A = P + C₊₊` positive-definite, the completed weld `S + C` is
positive-semidefinite **iff** its Schur complement on the negative channel,

`(C₋₋ − N) − C₊₋ᴴ (P + C₊₊)⁻¹ C₊₋`,

is positive-semidefinite.  The congruence `Lᴴ (S+C) L = diag(A, D − BᴴA⁻¹B)` by block Gaussian
elimination is invertible, so it preserves inertia; positivity of the coercive first block reduces
whole-form positivity to nonnegativity of the Schur block.

The scalar law is recovered exactly as the one-dimensional (`Fin 1`) case: the two-channel form
`Q(x,y) ≥ 0` for all `x, y` iff the `1×1` block weld is positive-semidefinite, both equivalent to the
scalar Schur threshold `n + b²/a ≤ c`.
-/

open Matrix
open scoped Matrix

namespace RHTower

noncomputable section

/-- Signed Krein metric `S = diag(P, −N)` on `H₊ ⊕ H₋`: coercive block `P` on the positive channel,
negative debt `−N` on the negative Krein channel. -/
def suzukiSignedKreinMetric {m n : Type*} (P : Matrix m m ℝ) (N : Matrix n n ℝ) :
    Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  Matrix.fromBlocks P 0 0 (-N)

/-- Self-adjoint source completion `C = [[C₊₊, C₊₋],[C₊₋ᴴ, C₋₋]]`, Hermitian by construction from the
off-diagonal holonomy coupling `C₊₋`. -/
def suzukiKreinCompletion {m n : Type*} (Cpp : Matrix m m ℝ) (Cpm : Matrix m n ℝ)
    (Cmm : Matrix n n ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  Matrix.fromBlocks Cpp Cpm Cpmᴴ Cmm

/-- The completed weld `S + C` has block form `[[P + C₊₊, C₊₋],[C₊₋ᴴ, C₋₋ − N]]`: the signed metric
shifts the diagonal blocks, the completion supplies the coupling. -/
theorem suzukiSignedKreinMetric_add_completion {m n : Type*}
    (P : Matrix m m ℝ) (N : Matrix n n ℝ) (Cpp : Matrix m m ℝ) (Cpm : Matrix m n ℝ)
    (Cmm : Matrix n n ℝ) :
    suzukiSignedKreinMetric P N + suzukiKreinCompletion Cpp Cpm Cmm
      = Matrix.fromBlocks (P + Cpp) Cpm Cpmᴴ (Cmm - N) := by
  rw [suzukiSignedKreinMetric, suzukiKreinCompletion, Matrix.fromBlocks_add]
  congr 1 <;> simp [sub_eq_neg_add, add_comm]

/-- **General finite block congruence for the Krein weld.**  With the completed positive block
`A = P + C₊₊` positive-definite, the completed weld `S + C = diag(P, −N) + C` is
positive-semidefinite iff its Schur complement on the negative channel — the completed negative block
`C₋₋ − N` minus the holonomy tax `C₊₋ᴴ (P + C₊₊)⁻¹ C₊₋` — is positive-semidefinite.  The block
Gaussian congruence to `diag(A, D − BᴴA⁻¹B)` preserves inertia, and coercivity of `A` reduces
positivity to the Schur block. -/
theorem suzukiKreinWeld_posSemidef_iff_schurComplement {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (P : Matrix m m ℝ) (N : Matrix n n ℝ) (Cpp : Matrix m m ℝ) (Cpm : Matrix m n ℝ)
    (Cmm : Matrix n n ℝ) (hA : (P + Cpp).PosDef) [Invertible (P + Cpp)] :
    (suzukiSignedKreinMetric P N + suzukiKreinCompletion Cpp Cpm Cmm).PosSemidef
      ↔ ((Cmm - N) - Cpmᴴ * (P + Cpp)⁻¹ * Cpm).PosSemidef := by
  rw [suzukiSignedKreinMetric_add_completion]
  exact Matrix.PosDef.fromBlocks₁₁ Cpm (Cmm - N) hA

/-- **Scalar Schur complement threshold.**  The one-dimensional Schur complement
`(c − n) − b (a)⁻¹ b` is positive-semidefinite iff the scalar Schur threshold `n + b²/a ≤ c` holds:
the `1×1` positive-semidefinite matrix has a single nonnegative entry `c − n − b²/a`. -/
theorem suzukiKreinScalarSchurComplement_posSemidef_iff (a b c n : ℝ) :
    ((!![c] - !![n]) - !![b] * (!![a])⁻¹ * !![b]).PosSemidef ↔ n + b ^ 2 / a ≤ c := by
  have hinv : (!![a])⁻¹ = !![a⁻¹] := by
    rw [Matrix.inv_def]; ext i j; fin_cases i; fin_cases j
    simp [Matrix.adjugate_fin_one]
  have hentry : ((!![c] - !![n]) - !![b] * (!![a])⁻¹ * !![b]) = !![c - n - b ^ 2 / a] := by
    rw [hinv]; ext i j; fin_cases i; fin_cases j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  rw [hentry, show (!![c - n - b ^ 2 / a] : Matrix (Fin 1) (Fin 1) ℝ)
        = Matrix.diagonal (fun _ : Fin 1 => c - n - b ^ 2 / a) by
          ext i j; fin_cases i; fin_cases j; simp,
      Matrix.posSemidef_diagonal_iff]
  constructor
  · intro h; have h0 := h 0; linarith
  · intro h i; linarith

/-- **One-dimensional specialization of the block congruence.**  The scalar two-channel Krein form
`Q(x,y) = a x² + 2b xy + (c − n) y²` is nonnegative for all `x, y` iff the `1×1` block weld
`diag(a, −n) + [[0, b],[b, c]]` is positive-semidefinite.  Both are routed through the general block
congruence and the scalar Schur threshold `n + b²/a ≤ c`, exhibiting the scalar completed-square law
as the `Fin 1` case of the finite block congruence. -/
theorem suzukiKreinScalarWeld_posSemidef_iff_twoChannelForm (a b c n : ℝ) (ha : 0 < a) :
    (suzukiSignedKreinMetric (!![a] : Matrix (Fin 1) (Fin 1) ℝ) (!![n])
        + suzukiKreinCompletion 0 (!![b]) (!![c])).PosSemidef
      ↔ (∀ x y : ℝ, 0 ≤ suzukiTwoChannelKreinCompletionForm a b c n x y) := by
  haveI hinvA : Invertible ((!![a] : Matrix (Fin 1) (Fin 1) ℝ) + 0) := by
    rw [add_zero]
    exact Matrix.invertibleOfIsUnitDet _ (by rw [Matrix.det_fin_one]; simpa using ha.ne')
  have hpd : ((!![a] : Matrix (Fin 1) (Fin 1) ℝ) + 0).PosDef := by
    rw [add_zero, show (!![a] : Matrix (Fin 1) (Fin 1) ℝ) = Matrix.diagonal (fun _ : Fin 1 => a) by
          ext i j; fin_cases i; fin_cases j; simp, Matrix.posDef_diagonal_iff]
    intro _; exact ha
  rw [suzukiKreinWeld_posSemidef_iff_schurComplement (!![a]) (!![n]) 0 (!![b]) (!![c]) hpd,
    add_zero, show ((!![b] : Matrix (Fin 1) (Fin 1) ℝ))ᴴ = !![b] by
      ext i j; fin_cases i; fin_cases j; simp,
    suzukiKreinScalarSchurComplement_posSemidef_iff a b c n]
  exact (suzukiTwoChannelKreinCompletionForm_nonneg_iff_schurDebt ha).symm

end

end RHTower
